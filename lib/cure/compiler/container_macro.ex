defmodule Cure.Compiler.ContainerMacro do
  @moduledoc """
  Generic OTP lowering for Cure's process containers.

  The parser keeps the readable `actor`, `fsm`, `sup`, and `app` surface forms,
  but this module is the only lowering implementation. Each container is
  validated through `Cure.Compiler.OtpMacro` and emitted as ordinary Erlang
  abstract forms. There are deliberately no per-container compiler, verifier,
  or runtime classes.
  """

  alias Cure.Compiler.OtpMacro

  @container_types [:actor, :fsm, :supervisor, :sup, :app]

  @spec forms(term()) :: {:ok, [tuple()]} | :not_a_container | {:error, term()}
  def forms(ast) do
    case find_container(ast) do
      {:ok, meta, body} -> lower(Keyword.get(meta, :container_type), meta, body)
      :none -> :not_a_container
    end
  end

  @doc "Return the declarative container descriptor used by the generic lowerer."
  @spec descriptor(term()) :: {:ok, map()} | {:error, term()}
  def descriptor(ast) do
    case find_container(ast) do
      {:ok, meta, body} -> descriptor_for(Keyword.get(meta, :container_type), meta, body)
      :none -> {:error, :not_a_container}
    end
  end

  defp lower(kind, meta, body) do
    with {:ok, descriptor} <- descriptor_for(kind, meta, body),
         {:ok, _} <- validate_descriptor(descriptor) do
      {:ok, emit(descriptor)}
    end
  end

  defp descriptor_for(kind, meta, body) when kind in @container_types do
    kind = normalize_kind(kind)
    name = Keyword.get(meta, :name)

    with name when is_binary(name) <- normalize_name(name),
         {:ok, descriptor} <- build_descriptor(kind, name, meta, body) do
      {:ok, descriptor}
    else
      _ -> {:error, {:invalid_container, kind, name}}
    end
  end

  defp descriptor_for(kind, _meta, _body), do: {:error, {:unsupported_container, kind}}

  defp build_descriptor(:supervisor, name, meta, body) do
    children =
      body
      |> List.wrap()
      |> Enum.filter(&match?({:child_spec, _, _}, &1))
      |> Enum.map(&child_descriptor/1)

    {:ok,
     %{
       kind: :supervisor,
       module: name,
       strategy: value(Keyword.get(meta, :strategy, :one_for_one)),
       intensity: value(Keyword.get(meta, :intensity, 3)),
       period: value(Keyword.get(meta, :period, 5)),
       children: children
     }}
  end

  defp build_descriptor(:application, name, meta, _body) do
    {:ok,
     %{
       kind: :application,
       module: name,
       root: root_module(Keyword.get(meta, :root)),
       vsn: value(Keyword.get(meta, :vsn)),
       description: value(Keyword.get(meta, :description)),
       applications: value(Keyword.get(meta, :applications, [])),
       env: value(Keyword.get(meta, :env, %{}))
     }}
  end

  defp build_descriptor(kind, name, meta, _body) when kind in [:actor, :fsm] do
    {:ok,
     %{
       kind: kind,
       module: name,
       initial: value(Keyword.get(meta, :init, Keyword.get(meta, :payload, :undefined))),
       callbacks: callbacks(meta)
     }}
  end

  defp validate_descriptor(%{kind: :supervisor} = descriptor) do
    OtpMacro.supervisor_module(
      descriptor.module,
      descriptor.children,
      strategy: descriptor.strategy,
      intensity: descriptor.intensity,
      period: descriptor.period
    )
    |> case do
      {:ok, _} -> {:ok, descriptor}
      {:error, reason} -> {:error, reason}
    end
  end

  defp validate_descriptor(%{kind: :application} = descriptor) do
    callbacks = [%{name: :start, arity: 2}, %{name: :stop, arity: 1}, %{name: :start_phase, arity: 3}]
    case OtpMacro.validate_callbacks(:Application, callbacks) do
      :ok -> {:ok, descriptor}
      {:error, _} = error -> error
    end
  end

  defp validate_descriptor(%{kind: :actor} = descriptor) do
    callbacks =
      Enum.map([{:init, 1}, {:handle_call, 3}, {:handle_cast, 2}, {:handle_info, 2}, {:terminate, 2}, {:code_change, 3}], fn {name, arity} ->
        %{name: name, arity: arity}
      end)

    case OtpMacro.validate_callbacks(:GenServer, callbacks) do
      :ok -> {:ok, descriptor}
      {:error, _} = error -> error
    end
  end

  defp validate_descriptor(%{kind: :fsm} = descriptor) do
    callbacks = [%{name: :callback_mode, arity: 0}, %{name: :init, arity: 1}, %{name: :handle_event, arity: 4}]
    case OtpMacro.validate_callbacks(:GenStatem, callbacks) do
      :ok -> {:ok, descriptor}
      {:error, _} = error -> error
    end
  end

  defp emit(%{kind: :supervisor} = descriptor), do: supervisor_forms(descriptor)
  defp emit(%{kind: :application} = descriptor), do: application_forms(descriptor)
  defp emit(%{kind: :actor} = descriptor), do: actor_forms(descriptor)
  defp emit(%{kind: :fsm} = descriptor), do: fsm_forms(descriptor)

  defp supervisor_forms(d) do
    module = module_atom(d.module)
    exports = [{:start_link, 0}, {:init, 1}]
    start = remote_call(:supervisor, :start_link, [tuple([atom(:local), atom(module)]), atom(module), nil_form()])
    child_specs = list(Enum.map(d.children, &child_spec_form/1))
    init_result = tuple([atom(:ok), tuple([tuple([atom(d.strategy), integer(d.intensity), integer(d.period)]), child_specs])])

    module_forms(module, :supervisor, exports, [
      function(:start_link, 0, [clause([], [start])]),
      function(:init, 1, [clause([var(:Args)], [init_result])])
    ])
  end

  defp application_forms(d) do
    module = module_atom(d.module)
    exports = [{:start, 2}, {:stop, 1}, {:start_phase, 3}]
    start_body =
      case d.root do
        nil -> tuple([atom(:ok), remote_call(:erlang, :self, [])])
        root -> remote_call(root, :start_link, [])
      end

    module_forms(module, :application, exports, [
      function(:start, 2, [clause([var(:_Type), var(:_Args)], [start_body])]),
      function(:stop, 1, [clause([var(:_State)], [atom(:ok)])]),
      function(:start_phase, 3, [clause([var(:_Phase), var(:_Type), var(:_Args)], [atom(:ok)])])
    ])
  end

  defp actor_forms(d) do
    module = module_atom(d.module)
    exports = [{:start_link, 1}, {:init, 1}, {:handle_call, 3}, {:handle_cast, 2}, {:handle_info, 2}, {:terminate, 2}, {:code_change, 3}]
    start = remote_call(:gen_server, :start_link, [tuple([atom(:local), atom(module)]), atom(module), list([var(:Initial)]), nil_form()])

    module_forms(module, :gen_server, exports, [
      function(:start_link, 1, [clause([var(:Initial)], [start])]),
      function(:init, 1, [clause([list([var(:State)])], [tuple([atom(:ok), var(:State)])])]),
      function(:handle_call, 3, [clause([var(:_Request), var(:_From), var(:State)], [tuple([atom(:reply), var(:State), var(:State)])])]),
      function(:handle_cast, 2, [clause([var(:_Message), var(:State)], [tuple([atom(:noreply), var(:State)])])]),
      function(:handle_info, 2, [clause([var(:_Info), var(:State)], [tuple([atom(:noreply), var(:State)])])]),
      function(:terminate, 2, [clause([var(:_Reason), var(:_State)], [atom(:ok)])]),
      function(:code_change, 3, [clause([var(:_Old), var(:State), var(:_Extra)], [tuple([atom(:ok), var(:State)])])])
    ])
  end

  defp fsm_forms(d) do
    module = module_atom(d.module)
    exports = [{:start_link, 1}, {:callback_mode, 0}, {:init, 1}, {:handle_event, 4}, {:terminate, 3}]
    start = remote_call(:gen_statem, :start_link, [tuple([atom(:local), atom(module)]), atom(module), list([var(:Initial)]), nil_form()])

    module_forms(module, :gen_statem, exports, [
      function(:start_link, 1, [clause([var(:Initial)], [start])]),
      function(:callback_mode, 0, [clause([], [atom(:handle_event_function)])]),
      function(:init, 1, [clause([list([var(:State)])], [tuple([atom(:ok), atom(:initial), var(:State)])])]),
      function(:handle_event, 4, [clause([var(:_Type), var(:_Event), var(:State), var(:Data)], [tuple([atom(:keep_state), var(:Data)])])]),
      function(:terminate, 3, [clause([var(:_Reason), var(:_State), var(:_Data)], [atom(:ok)])])
    ])
  end

  defp module_forms(module, behaviour, exports, functions) do
    [{:attribute, 1, :module, module}, {:attribute, 1, :behaviour, behaviour}, {:attribute, 1, :export, exports} | functions]
  end

  defp child_spec_form(child) do
    module = module_atom(child.module)
    tuple([
      atom(child.id),
      tuple([tuple([atom(module), atom(:start_link), nil_form()])]),
      atom(child.restart),
      value_form(child.shutdown),
      atom(child.kind),
      list([atom(module)])
    ])
  end

  defp child_descriptor({:child_spec, meta, _}) do
    %{
      module: normalize_name(Keyword.get(meta, :module)),
      id: normalize_name(Keyword.get(meta, :id)),
      kind: Keyword.get(meta, :kind, :worker),
      restart: value(Keyword.get(meta, :restart, :permanent)),
      shutdown: value(Keyword.get(meta, :shutdown, 5000))
    }
  end

  defp callbacks(meta), do: Keyword.get(meta, :callbacks, [])

  defp find_container({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) in @container_types do
      {:ok, meta, body}
    else
      find_container(body)
    end
  end

  defp find_container(list) when is_list(list) do
    Enum.find_value(list, :none, fn item ->
      case find_container(item) do
        :none -> nil
        found -> found
      end
    end)
  end

  defp find_container({_tag, _meta, children}) when is_list(children), do: find_container(children)
  defp find_container(_), do: :none

  defp normalize_kind(:sup), do: :supervisor
  defp normalize_kind(:app), do: :application
  defp normalize_kind(kind), do: kind

  defp normalize_name(name) when is_atom(name), do: Atom.to_string(name)
  defp normalize_name(name) when is_binary(name), do: name
  defp normalize_name(_), do: nil

  defp module_atom(name) do
    name = normalize_name(name)
    if String.starts_with?(name, "Elixir."), do: String.to_atom(name), else: String.to_atom("Elixir." <> name)
  end

  defp root_module({:function_call, meta, _}) when is_list(meta), do: normalize_name(Keyword.get(meta, :name)) |> module_atom()
  defp root_module({:variable, _, name}), do: module_atom(name)
  defp root_module(name) when is_binary(name), do: module_atom(name)
  defp root_module(_), do: nil

  defp value(nil), do: nil
  defp value({:literal, _, value}), do: value
  defp value({:atom, _, value}), do: value
  defp value({:integer, _, value}), do: value
  defp value({:string, _, value}), do: value
  defp value({:variable, _, value}), do: value
  defp value(value), do: value

  defp value_form(value) when is_integer(value), do: integer(value)
  defp value_form(value) when is_atom(value), do: atom(value)
  defp value_form(value), do: atom(value(value))

  defp atom(value), do: {:atom, 1, value}
  defp integer(value), do: {:integer, 1, value}
  defp var(value), do: {:var, 1, value}
  defp nil_form, do: {:nil, 1}
  defp list(items), do: Enum.reduce(Enum.reverse(items), nil_form(), fn item, tail -> {:cons, 1, item, tail} end)
  defp tuple(items), do: {:tuple, 1, items}
  defp clause(patterns, body), do: {:clause, 1, patterns, [], body}
  defp function(name, arity, clauses), do: {:function, 1, name, arity, clauses}
  defp remote_call(module, name, args), do: {:call, 1, {:remote, 1, atom(module), atom(name)}, args}
end
