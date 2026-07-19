defmodule Cure.Otp.Builtins do
  @moduledoc """
  Runtime FFI helpers for `Std.Otp`'s `Subject` abstraction — a typed message
  address `{owner_pid, tag_ref}` in the style of Gleam's `Subject(message)`.

  A `Subject` is a `{pid, reference}` pair: the owning process plus a fresh,
  unique tag. `subject_send` delivers `{tag, message}` to the owner's mailbox;
  `subject_receive` does a tagged selective receive, so one process can own
  several subjects of different message types and receive each independently.
  These are the operations that cannot be expressed as plain BIFs (the tagged
  `receive ... after ... end` needs Erlang receive syntax); `Std.Otp` gives them
  their typed surface. Callable from Cure via `@extern(Elixir.Cure.Otp.Builtins, …)`.
  """

  @doc "Mint a fresh subject owned by the calling process: `{self(), make_ref()}`."
  def subject_new, do: {self(), make_ref()}

  @doc "Deliver a tagged message to the subject's owner. Returns `:ok`."
  def subject_send({owner, tag}, message) do
    send(owner, {tag, message})
    :ok
  end

  @doc """
  Tagged selective receive with a millisecond `timeout`. Only the owning process
  should call this. Returns the Cure `Option` representation — `{:Some, message}`
  on receipt, `:None` on timeout.
  """
  def subject_receive({_owner, tag}, timeout) do
    receive do
      {^tag, message} -> {:Some, message}
    after
      timeout -> :None
    end
  end

  # -- Selector: typed selective receive over several heterogeneous subjects -------------------------------
  #
  # A selector is `{:selector, handlers}` where `handlers` maps a subject's ref `tag` to its `transform`
  # (`payload -> payload'`). Subject messages are always the 2-tuple `{tag, payload}`, so `selector_receive` does
  # ONE receive matching `{tag, payload}` guarded by `is_map_key(tag, handlers)` — the dynamic multi-tag select
  # (the Subject-shaped case of Gleam's `gleam_erlang_ffi:select`). Unregistered messages stay in the mailbox.

  @doc "An empty selector."
  def selector_new, do: {:selector, %{}}

  @doc "Register `subject`'s messages, mapping each into the common payload via `transform`."
  def selector_select_map({:selector, handlers}, {_owner, tag}, transform) do
    {:selector, Map.put(handlers, tag, transform)}
  end

  @doc """
  Receive from whichever registered subject arrives first, within `timeout` ms, applying that subject's
  transform. Returns `{:Some, payload}` or `:None` on timeout. Unregistered messages stay in the mailbox.
  """
  def selector_receive({:selector, handlers}, timeout) do
    receive do
      # NB: Elixir's `is_map_key/2` is `(map, key)` — the reverse of Erlang's `is_map_key(key, map)`.
      {tag, payload} when is_map_key(handlers, tag) ->
        {:Some, Map.get(handlers, tag).(payload)}
    after
      timeout -> :None
    end
  end
end
