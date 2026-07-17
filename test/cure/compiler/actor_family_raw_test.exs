defmodule Cure.Compiler.ActorFamilyRawTest do
  use ExUnit.Case, async: false

  # §1e Mechanism A: the ActorDefinition family gains a raw-body branch — an
  # alternative to the `on_cast` Cases branch. A raw `handle_cast` body is a
  # full GenServer callback result (e.g. `%[:noreply, state]` or a `pickup`
  # dispatch) spliced verbatim, NOT a set of Cases arms wrapped in `:noreply`.
  # This lets the ONE family host both the derived (Cases) surface and the
  # Tier-0 raw surface, so the 15 positional raw templates can share the
  # family's single emitter instead of each re-spelling a full module.

  test "family actor accepts a raw handle_cast body with an explicit message type" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyCast
        state Int
        messages Atom
        handle_cast
          %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.RawFamilyCast", :handle_cast, [:ping, 7]) == {:noreply, 7}
    assert apply(:"Cure.Generated.RawFamilyCast", :init, [3]) == {:ok, 3}
    assert {:ok, pid} = apply(:"Cure.Generated.RawFamilyCast", :start_link, [5])
    assert :gen_server.cast(pid, :ping) == :ok
    :gen_server.stop(pid)
  end

  test "family raw handle_cast without a messages declaration is polymorphic in the message" do
    # No `messages` field: the family's raw branch must emit a message-polymorphic
    # `handle_cast` (an inline free type var at the callback, NOT a module-level
    # `typealias Message = m` with a free `m`, which the kernel cannot resolve).
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyNoMsg
        state Int
        handle_cast
          %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyNoMsg", :handle_cast, [:anything, 7]) == {:noreply, 7}
    assert apply(:"Cure.Generated.RawFamilyNoMsg", :handle_cast, [42, 7]) == {:noreply, 7}
  end

  test "family raw handle_cast body may branch on the message with pickup" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyPickup
        state Int
        messages Atom
        handle_cast
          pickup
            message == :inc -> %[:noreply, state + 1]
            else -> %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyPickup", :handle_cast, [:inc, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyPickup", :handle_cast, [:other, 4]) == {:noreply, 4}
  end

  test "family raw handle_cast body may be a match with full-result arms" do
    # A raw handle_cast whose body is a `match` on the message returning full
    # `%[:noreply, _]` results must splice VERBATIM. The family raw branch must
    # NOT re-wrap the arms in another `:noreply` — doing so double-wraps to
    # `%[:noreply, %[:noreply, _]]`, which breaks the callback's
    # `Effect(Tuple(Atom, State))` type (the nested tuple is not `State`) and
    # surfaces as `:ctor_requires_checking_mode` on the inner Sigma. Regression
    # pin for the raw/Cases emitter split (§1e wall 4).
    source = """
    mod M
      use Std.Actor

      type Cmd = Inc | Dec

      actor Cure.Generated.RawFamilyMatch
        state Int
        messages Cmd
        handle_cast
          match message
            Inc -> %[:noreply, state + 1]
            Dec -> %[:noreply, state - 1]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyMatch", :handle_cast, [:Inc, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyMatch", :handle_cast, [:Dec, 4]) == {:noreply, 3}
  end

  test "a bare (mod-less) computed raw actor is the program's top-level module" do
    # A `becomes lift module name` template yields a bare top-level `lift_module`
    # at parse time, so `compile_and_load` returns the actor module itself. A
    # computed/family expansion instead wraps its single lifted module in a
    # `:block`, which (pre-fix) fell through to an empty `Cure.Main` wrapper. This
    # pins in-place module identity for the computed path so bare-source guards
    # (container_macro_test:186/204/213) hold once terse heads route through the
    # shared family emitter.
    source = """
    actor Cure.Generated.BareTopRawCast
      state Int
      messages Atom
      handle_cast
        %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.Generated.BareTopRawCast"
    assert apply(module, :handle_cast, [:ping, 7]) == {:noreply, 7}
  end

  test "terse template form routes through the shared family raw emitter" do
    # The single-line-fields `actor N state T handle_cast <body>` form is the
    # positional TEMPLATE (not the block family form). It is rerouted from a
    # spelled-out `becomes lift module name` block to `computed by
    # emit_raw_state_cast`, which delegates to the shared family raw emitter.
    # This pins that the reroute expands and behaves like the block form.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawTemplateCast state Int handle_cast
        %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawTemplateCast", :handle_cast, [:ping, 7]) == {:noreply, 7}
    assert apply(:"Cure.Generated.RawTemplateCast", :handle_cast, [42, 7]) == {:noreply, 7}
  end

  test "terse messages template routes through the shared family raw emitter" do
    # The `actor N state T messages M handle_cast <body>` form (rule 172) carries
    # a `messages` hole, so it opts into the `computed directly by` multi-arg
    # input path (adapter emit_raw_state_messages_cast) rather than the shared
    # ActorSyntax record. This behavioral pin replaces the retired Raw05
    # byte-golden: the `pickup` dispatch and the spliced verbatim body must
    # survive the fold, and (via wall-3 in-place identity) the bare-source actor
    # is the program's top-level module.
    source = """
    actor Cure.Generated.RawMessagesTemplateCast state Int messages Atom handle_cast
      pickup
        message == :inc -> %[:noreply, state + 1]
        else -> %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.Generated.RawMessagesTemplateCast"
    assert apply(module, :handle_cast, [:inc, 4]) == {:noreply, 5}
    assert apply(module, :handle_cast, [:other, 4]) == {:noreply, 4}
  end

  test "terse init template routes through the shared family raw emitter" do
    # The `actor N state T init <body>` form (rule at actor.cure:158) carries an
    # `init` hole and no cast/messages, so it opts into the `computed directly by`
    # multi-arg input path (adapter emit_raw_state_init) into the family raw
    # branch (init: Some(body)). This behavioral pin replaces the retired Raw02
    # byte-golden: the spliced init body is the full GenServer init result, so
    # `init/1` returns it verbatim regardless of the start argument. Per the
    # corrected spec (d1aec7b4) the raw fold is behavioral-equivalence, NOT
    # byte-identical.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyInit state Int init
        %[:ok, 7]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyInit", :init, [:unit]) == {:ok, 7}
    assert apply(:"Cure.Generated.RawFamilyInit", :init, [:anything]) == {:ok, 7}
  end

  test "terse terminate template routes through the shared family raw emitter" do
    # The `actor N state T terminate <body>` form (rule at actor.cure:160) carries
    # a `terminate` hole and no cast/messages, so it opts into the `computed
    # directly by` multi-arg input path (adapter emit_raw_state_terminate) into the
    # family raw branch (terminate: Some(body)). This behavioral pin replaces the
    # retired Raw03 byte-golden: the spliced terminate body is the full callback
    # result, so `terminate/2` returns it verbatim.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyTerminate state Int terminate
        :shutdown_complete
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyTerminate", :terminate, [:normal, 5]) == :shutdown_complete
  end

  test "terse code_change template routes through the shared family raw emitter" do
    # The `actor N state T code_change <body>` form (rule at actor.cure:162) carries
    # a `code_change` hole and no cast/messages, so it opts into the `computed
    # directly by` multi-arg input path (adapter emit_raw_state_code_change) into
    # the family raw branch (code_change: Some(body)). This behavioral pin replaces
    # the retired Raw04 byte-golden: the spliced code_change body is the full
    # callback result, so `code_change/3` returns it verbatim over the state.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyCodeChange state Int code_change
        %[:ok, state + 1]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyCodeChange", :code_change, [:v1, 5, :extra]) == {:ok, 6}
  end

  test "terse initial+handle_cast template routes through the shared family raw emitter" do
    # The `actor N state T initial <payload> handle_cast <body>` form carries an
    # `initial` hole, so the adapter emit_raw_state_initial_cast seeds the family
    # with initial: Some(payload). This behavioral pin replaces the retired Raw07
    # byte-golden: derive_actor_init emits init(args: Atom) = %[:ok, payload], so
    # init/1 returns the seeded payload for any argument, and the handle_cast body
    # is spliced verbatim.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyInitialCast state Int initial 0 handle_cast
        %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyInitialCast", :init, [:anything]) == {:ok, 0}
    assert apply(:"Cure.Generated.RawFamilyInitialCast", :handle_cast, [:ping, 7]) == {:noreply, 7}
  end

  test "terse initial+messages+handle_cast template routes through the shared family raw emitter" do
    # The `actor N state T initial <payload> messages <M> handle_cast <body>` form
    # (adapter emit_raw_state_initial_messages_cast) seeds initial and aliases the
    # message type. This behavioral pin replaces the retired Raw08 byte-golden: the
    # `pickup` dispatch survives the fold and init/1 returns the seeded payload.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyInitialMsgCast state Int initial 0 messages Atom handle_cast
        pickup
          message == :inc -> %[:noreply, state + 1]
          else -> %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyInitialMsgCast", :init, [:anything]) == {:ok, 0}
    assert apply(:"Cure.Generated.RawFamilyInitialMsgCast", :handle_cast, [:inc, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyInitialMsgCast", :handle_cast, [:other, 4]) == {:noreply, 4}
  end

  test "terse messages+handle_info template routes through the shared family raw emitter" do
    # The `actor N state T messages <M> handle_info <body>` form (adapter
    # emit_raw_state_messages_info) routes the raw handle_info body through the
    # family raw branch (raw_info_handler). This behavioral pin replaces the retired
    # Raw11 byte-golden AND exercises wall-4 for the INFO path: a `match`-shaped info
    # body with full-result arms must splice VERBATIM, never re-wrapped in a second
    # `:noreply`.
    source = """
    mod M
      use Std.Actor

      type Sig = Tick | Tock

      actor Cure.Generated.RawFamilyMsgInfo state Int messages Sig handle_info
        match message
          Tick -> %[:noreply, state + 1]
          Tock -> %[:noreply, state - 1]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyMsgInfo", :handle_info, [:Tick, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyMsgInfo", :handle_info, [:Tock, 4]) == {:noreply, 3}
  end

  test "terse handle_info template routes through the shared family raw emitter" do
    # The `actor N state T handle_info <body>` form (adapter emit_raw_state_info)
    # routes the raw handle_info body through the family raw branch with a
    # polymorphic message type. This behavioral pin replaces the retired Raw12
    # byte-golden: the handle_info body is spliced verbatim.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyInfo state Int handle_info
        %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyInfo", :handle_info, [:timeout, 9]) == {:noreply, 9}
  end

  test "terse state+body template routes through the shared family raw emitter" do
    # The `actor N state T <body-declarations>` form (rule at actor.cure:200)
    # carries no callback holes but a trailing definition block, captured by the
    # NEW positional `Declarations until dedent` hole (parser raw-body branch,
    # task #24 step 1) and threaded to the family via emit_raw_state_body
    # (body: Some(...)). This behavioral pin replaces the retired Raw14
    # byte-golden: the default GenServer callbacks are emitted (init/1 =
    # {:ok, initial}, handle_cast/2 = {:noreply, state}, start_link/1) alongside
    # the spliced extra declaration, which becomes a callable function of the
    # generated module. Per the corrected spec (d1aec7b4) the raw fold is
    # behavioral-equivalence, NOT byte-identical (default-init family path emits
    # Effect-wrapped callback return types vs the template's bare Tuple types;
    # bodies identical, return types erased).
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyBody state Int
        fn helper() -> Int = 42
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyBody", :helper, []) == 42
    assert apply(:"Cure.Generated.RawFamilyBody", :init, [3]) == {:ok, 3}
    assert apply(:"Cure.Generated.RawFamilyBody", :handle_cast, [:ping, 7]) == {:noreply, 7}
    assert {:ok, pid} = apply(:"Cure.Generated.RawFamilyBody", :start_link, [5])
    :gen_server.stop(pid)
  end

  test "terse state+with+body template routes through the shared family raw emitter" do
    # The `actor N state T with <payload> <body-declarations>` form (rule at
    # actor.cure:187) carries a `with` seed AND a trailing definition block. The
    # seed threads through the family as initial: Some(payload) (adapter
    # emit_raw_state_initial_body) and the block through the NEW positional
    # `Declarations until dedent` hole as body: Some(...). This behavioral pin
    # replaces the retired Raw13 byte-golden: derive_actor_init emits
    # init(args: Atom) = %[:ok, payload], so init/1 returns the seeded payload for
    # any argument (behaviorally equivalent to the template's nullary
    # start_link seeding), the default handle_cast is {:noreply, state}, and the
    # spliced extra declaration is a callable function of the generated module.
    # Per the corrected spec (d1aec7b4) the raw fold is behavioral-equivalence,
    # NOT byte-identical.
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyStateWithBody state Int with 0
        fn helper() -> Int = 42
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyStateWithBody", :helper, []) == 42
    assert apply(:"Cure.Generated.RawFamilyStateWithBody", :init, [:anything]) == {:ok, 0}
    assert apply(:"Cure.Generated.RawFamilyStateWithBody", :handle_cast, [:ping, 7]) == {:noreply, 7}
  end
end
