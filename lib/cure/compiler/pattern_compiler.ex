defmodule Cure.Compiler.PatternCompiler.Error do
  @moduledoc """
  Raised when a pattern's shape is not one this compiler recognizes.

  `Cure.Compiler.Codegen.compile_module/2` rescues this and returns
  `{:error, {:pattern_error, code, message, line}}`, so an invalid pattern surfaces
  the way every other compile failure does.
  """
  defexception [:code, :message, :line]
end

defmodule Cure.Compiler.PatternCompiler do
  @moduledoc """
  Dedicated pattern-to-Erlang-abstract-form compiler for `match`, `let`,
  multi-clause function heads, comprehension generators, and catch arms.

  Separated from `Cure.Compiler.Codegen` so that pattern compilation can
  recurse through compound shapes (tuples, lists, cons, maps, records,
  ADT constructors, binaries, pins, wildcards, literals, variables)
  *without* accidentally dropping into expression codegen. Nested patterns
  such as `%[_, %{list: [h | t]}, _]` are therefore translated into proper
  Erlang abstract patterns whose sub-terms are themselves patterns.

  ## State

  Shares the `Cure.Compiler.Codegen` struct as its working state; the
  only fields consulted are `:line` and `:vars`. Newly-bound variables
  are added to `vars`. Rebinding an already-known variable in the same
  pattern is lowered to a guard `V_fresh =:= V_existing` returned in the
  third tuple element (a list of extra guard conjuncts the caller can
  merge with any explicit `when` clause).

  ## Entry points

  - `compile/2` -- translate a single pattern AST into an Erlang form.
    Returns `{form, state}` with any injected equality guards folded
    into `state.pattern_guards` (a list of Erlang abstract expressions).
  - `compile_with_guards/2` -- convenience wrapper that separates the
    pattern form from the injected guard list.

  ## Semantics

  - Map patterns compile with `:map_field_exact` (`K := V`) rather than
    `:map_field_assoc` (`K => V`) so they actually match rather than
    construct.
  - Record patterns compile to a map pattern with an exact
    `__struct__ := :tag` check plus `field := pat` entries for each
    named field. Unspecified fields are dropped (open matching) --
    consistent with Elixir struct patterns.
  - ADT constructor patterns (`Ok(x)`, `Some(v)`) compile to tagged
    tuples whose children are themselves compiled as patterns.
  - The pin operator `^x` (see `Cure.Compiler.Parser` for the surface
    syntax) compiles to a fresh variable plus an equality guard.
  - Binary patterns `<<x:8, rest/binary>>` compile to `{:bin, _, _}`.
  - As-patterns `whole @ Some(x)` compile to Erlang's `Whole = {some, X}`.
  - Any shape outside the recognized set — a range, a bare nullary constructor,
    a lowercase call head — raises `Cure.Compiler.PatternCompiler.Error`, which
    `Codegen.compile_module/2` turns into `{:error, {:pattern_error, …}}`. A
    wildcard row is only ever introduced by an actual `_` or variable.
  """

  alias Cure.Compiler.Codegen

  @doc """
  Compile a pattern AST into an Erlang abstract pattern form.

  Threads the codegen state so newly-bound variables become available
  to guards and bodies that follow. Equality guards introduced by the
  pin operator or by repeated variable occurrences are accumulated in
  `state.pattern_guards` (added dynamically if missing).
  """
  @spec compile(tuple(), Codegen.t()) :: {tuple(), Codegen.t()}
  def compile(ast, state) do
    state = ensure_pattern_guards(state)
    do_compile(ast, state)
  end

  @doc """
  Compile a pattern and return `{form, guards, state}` where `guards` is
  a list of extra Erlang guard expressions that must be conjoined with
  any explicit `when` clause.
  """
  @spec compile_with_guards(tuple(), Codegen.t()) :: {tuple(), [tuple()], Codegen.t()}
  def compile_with_guards(ast, state) do
    state = %{ensure_pattern_guards(state) | pattern_guards: []}
    {form, state} = do_compile(ast, state)
    guards = Enum.reverse(state.pattern_guards)
    {form, guards, %{state | pattern_guards: []}}
  end

  # -- Dispatch ---------------------------------------------------------------

  defp do_compile(ast, state) do
    case ast do
      # Wildcard
      {:variable, _meta, "_"} ->
        {{:var, state.line, :_}, state}

      # Anonymous wildcard-ish: _foo
      {:variable, _meta, "_" <> _rest = name} ->
        var_atom = Codegen.mangle_var(name)
        {{:var, state.line, var_atom}, state}

      # Bare PascalCase identifier: a nullary constructor written without its `()`.
      # `docs/MATCH.md` §5.12 requires the parens precisely because this grammar cannot
      # otherwise tell a capitalized binder from a capitalized constructor — and E074
      # exists to say so. Until now nothing raised it, and the name bound a variable that
      # matched everything, silently shadowing every arm below it.
      {:variable, meta, name} when is_binary(name) ->
        if constructor?(name) do
          bad_pattern!(
            "E074",
            "bare nullary constructor `#{name}` in pattern position — write `#{name}()`",
            Keyword.get(meta, :line, state.line)
          )
        end

        compile_variable_pattern(name, state)

      # As-pattern: `whole @ Some(x)` binds the scrutinee AND matches the inner pattern.
      # Erlang spells this `Whole = {some, X}` — a `{:match, …}` node, legal in patterns.
      {:as_pattern, meta, [name, inner]} when is_binary(name) ->
        compile_as_pattern(meta, name, inner, state)

      # Pin operator: ^x -- parsed as {:pin, meta, [{:variable, _, name}]}
      {:pin, meta, [inner]} ->
        compile_pin(meta, inner, state)

      # Cons or fixed list
      {:list, meta, elems} ->
        compile_list(meta, elems, state)

      # Tuple
      {:tuple, meta, elems} ->
        compile_tuple(meta, elems, state)

      # Map
      {:map, meta, pairs} ->
        compile_map_pattern(meta, pairs, state)

      # Record / ADT constructor / soft call
      {:function_call, meta, args} ->
        compile_call_pattern(meta, args, state)

      # Literal (binary pattern is dispatched inside `compile_literal`
      # when the :bytes subtype carries a list of bin-element ASTs).
      {:literal, meta, value} ->
        compile_literal_or_binary(meta, value, state)

      # Unary minus on literal (negative integer patterns)
      {:unary_op, meta, [{:literal, _, _} = lit]} ->
        case Keyword.get(meta, :operator) do
          :- ->
            {form, state} = compile_literal(elem(lit, 1), elem(lit, 2), state)
            negated = negate_literal_form(form, Keyword.get(meta, :line, state.line))
            {negated, state}

          op ->
            bad_pattern!(
              "E090",
              "unary `#{op}` is not a pattern",
              Keyword.get(meta, :line, state.line)
            )
        end

      # Range not supported in pattern position (`docs/PATTERNS.md`, and this module's own
      # moduledoc). It used to compile to a wildcard on the promise that "the type checker
      # will flag it"; no stage ever did, so `1..10 -> …` matched every value.
      {:range, meta, _} ->
        bad_pattern!(
          "E090",
          "range patterns are not supported in pattern position",
          Keyword.get(meta, :line, state.line)
        )

      other ->
        bad_pattern!("E090", "unrecognized pattern shape: #{inspect(other)}", state.line)
    end
  end

  # Maranget's algorithm — and every pattern elaborator built on it — specializes over a
  # CLOSED set of head shapes. An input outside that set is a compile error; a wildcard row
  # is only ever introduced by an actual `_` or variable in the source. This module used to
  # answer four different unrecognized shapes with `{:var, line, :_}`: a bare nullary
  # constructor, an as-pattern, a range, and any call whose name wasn't capitalized (a
  # typo'd `some(x)` for `Some(x)`). Each became an unconditional wildcard that swallowed
  # every scrutinee and shadowed every arm below — silent miscompilation, no diagnostic.
  @spec bad_pattern!(String.t(), String.t(), integer()) :: no_return()
  defp bad_pattern!(code, message, line) do
    raise Cure.Compiler.PatternCompiler.Error,
      code: code,
      line: line,
      message: "#{code}: #{message} (line #{line})"
  end

  # -- Literals ---------------------------------------------------------------

  defp compile_literal_or_binary(meta, parts, state) when is_list(parts) do
    case Keyword.get(meta, :subtype) do
      subtype when subtype in [:bytes, :binary] ->
        compile_binary_pattern(meta, parts, state)

      _ ->
        compile_literal(meta, parts, state)
    end
  end

  defp compile_literal_or_binary(meta, value, state) do
    compile_literal(meta, value, state)
  end

  defp compile_literal(meta, value, state) do
    line = Keyword.get(meta, :line, state.line)
    subtype = Keyword.get(meta, :subtype)

    form =
      case subtype do
        :integer -> {:integer, line, value}
        :float -> {:float, line, value}
        :string -> compile_string_literal(value, line)
        :boolean -> {:atom, line, value}
        :null -> {:atom, line, nil}
        :symbol -> {:atom, line, value}
        :char -> {:integer, line, value}
        :bytes -> compile_bytes_literal(value, line)
        _ -> {:atom, line, value}
      end

    {form, state}
  end

  defp compile_string_literal(value, line) when is_binary(value) do
    {:bin, line, [{:bin_element, line, {:string, line, String.to_charlist(value)}, :default, [:utf8]}]}
  end

  defp compile_string_literal(value, line), do: {:atom, line, value}

  defp compile_bytes_literal(value, line) when is_binary(value) do
    {:bin, line, [{:bin_element, line, {:string, line, :binary.bin_to_list(value)}, :default, :default}]}
  end

  defp compile_bytes_literal(value, line) when is_list(value) do
    elements =
      Enum.map(value, fn byte ->
        {:bin_element, line, {:integer, line, byte}, :default, :default}
      end)

    {:bin, line, elements}
  end

  defp compile_bytes_literal(_value, line), do: {:bin, line, []}

  defp negate_literal_form({:integer, line, n}, _ln), do: {:integer, line, -n}
  defp negate_literal_form({:float, line, n}, _ln), do: {:float, line, -n}
  defp negate_literal_form(form, line), do: {:op, line, :-, form}

  # -- Variables --------------------------------------------------------------

  defp compile_variable_pattern(name, state) do
    case Map.fetch(state.vars, name) do
      {:ok, existing_atom} ->
        # Repeated occurrence: bind a fresh var and emit an equality guard.
        {fresh, state} = fresh_var_atom(name, state)
        guard = equality_guard(fresh, existing_atom, state.line)

        state = %{
          state
          | pattern_guards: [guard | state.pattern_guards],
            vars: Map.put(state.vars, name, existing_atom)
        }

        {{:var, state.line, fresh}, state}

      :error ->
        var_atom = Codegen.mangle_var(name)
        state = %{state | vars: Map.put(state.vars, name, var_atom)}
        {{:var, state.line, var_atom}, state}
    end
  end

  # `whole @ Some(x)`: bind the whole scrutinee to `whole` and match `Some(x)` besides. The
  # inner pattern compiles exactly as if it had appeared bare — an as-binding is a
  # let-around-the-column, never an opaque node that disables matching on it. The classic
  # pipeline had no clause for this at all, so both halves fell into the catch-all and the
  # arm matched everything; the dependent elaborator has understood it all along
  # (`Elaborator.desugar_as_patterns/1`) and the oracle suite pins the semantics.
  defp compile_as_pattern(meta, name, inner, state) do
    line = Keyword.get(meta, :line, state.line)
    {inner_form, state} = do_compile(inner, state)
    {var_form, state} = compile_variable_pattern(name, state)
    {{:match, line, var_form, inner_form}, state}
  end

  # Two repeats of the same name in one pattern (`[x, x, x]`) must produce DISTINCT Erlang
  # variables, each equated to the original by its own guard. The counter that guarantees
  # that was declared on the codegen struct and read here, but incremented nowhere: every
  # dup in a clause collapsed onto `V__dup_x_0`, so a third occurrence re-matched a variable
  # already bound to the second occurrence's value.
  defp fresh_var_atom(name, state) do
    counter = Map.get(state, :pattern_dup_counter, 0)
    {String.to_atom("V__dup_#{name}_#{counter}"), %{state | pattern_dup_counter: counter + 1}}
  end

  defp equality_guard(fresh, existing, line) do
    {:op, line, :"=:=", {:var, line, fresh}, {:var, line, existing}}
  end

  # -- Pin --------------------------------------------------------------------

  defp compile_pin(meta, {:variable, _vmeta, name}, state) do
    line = Keyword.get(meta, :line, state.line)

    case Map.fetch(state.vars, name) do
      {:ok, atom} ->
        fresh = String.to_atom("V__pin_#{name}_#{line}")
        guard = equality_guard(fresh, atom, line)
        state = %{state | pattern_guards: [guard | state.pattern_guards]}
        {{:var, line, fresh}, state}

      :error ->
        # Unbound pin: compile as a normal variable binding and let the
        # type checker raise E024.
        compile_variable_pattern(name, state)
    end
  end

  defp compile_pin(_meta, other, state) do
    # Non-variable inside ^(...) -- treat as a plain sub-pattern.
    do_compile(other, state)
  end

  # -- Lists (fixed and cons) -------------------------------------------------

  defp compile_list(meta, elems, state) do
    line = Keyword.get(meta, :line, state.line)
    is_cons = Keyword.get(meta, :cons, false)

    if is_cons do
      case elems do
        [head, tail] ->
          {h_form, state} = do_compile(head, state)
          {t_form, state} = do_compile(tail, state)
          {{:cons, line, h_form, t_form}, state}

        _ ->
          compile_fixed_list(elems, line, state)
      end
    else
      compile_fixed_list(elems, line, state)
    end
  end

  defp compile_fixed_list(elems, line, state) do
    {forms, state} =
      Enum.map_reduce(elems, state, fn elem, st -> do_compile(elem, st) end)

    {build_cons_list(forms, line), state}
  end

  defp build_cons_list([], line), do: {nil, line}
  defp build_cons_list([h | t], line), do: {:cons, line, h, build_cons_list(t, line)}

  # -- Tuples -----------------------------------------------------------------

  defp compile_tuple(meta, elems, state) do
    line = Keyword.get(meta, :line, state.line)

    {forms, state} =
      Enum.map_reduce(elems, state, fn elem, st -> do_compile(elem, st) end)

    {{:tuple, line, forms}, state}
  end

  # -- Map patterns -----------------------------------------------------------

  defp compile_map_pattern(meta, pairs, state) do
    line = Keyword.get(meta, :line, state.line)

    {field_forms, state} =
      Enum.map_reduce(pairs, state, fn pair, st ->
        compile_map_field(pair, line, st)
      end)

    {{:map, line, field_forms}, state}
  end

  defp compile_map_field({:pair, _, [key, value_pat]}, line, state) do
    {k_form, state} = compile_map_key(key, state)
    {v_form, state} = do_compile(value_pat, state)
    {{:map_field_exact, line, k_form, v_form}, state}
  end

  defp compile_map_field(other, line, state) do
    # Defensive: treat any stray element as wildcard.
    _ = other
    {{:map_field_exact, line, {:var, line, :_}, {:var, line, :_}}, state}
  end

  # Map keys are values, not patterns: compile literals directly; variable
  # keys get bound (though that's very unusual in match patterns).
  defp compile_map_key({:literal, meta, value}, state), do: compile_literal(meta, value, state)

  defp compile_map_key({:variable, _meta, name}, state) when is_binary(name) do
    # Variable-as-key in a pattern: treat as already-bound reference.
    case Map.fetch(state.vars, name) do
      {:ok, atom} -> {{:var, state.line, atom}, state}
      :error -> {{:atom, state.line, String.to_atom(name)}, state}
    end
  end

  defp compile_map_key(other, state), do: do_compile(other, state)

  # -- Call patterns: records, ADT constructors, qualified references --------

  defp compile_call_pattern(meta, args, state) do
    name = Keyword.get(meta, :name, "unknown")
    is_record = Keyword.get(meta, :record, false)
    line = Keyword.get(meta, :line, state.line)

    cond do
      is_record ->
        compile_record_pattern(name, args, line, state)

      constructor?(name) ->
        compile_constructor_pattern(name, args, line, state)

      true ->
        # A lowercase call head is not a constructor and not a record. `some(x)` — a typo
        # for `Some(x)` — used to compile to a bind-everything wildcard, discarding the
        # argument `x` along with the shape test.
        bad_pattern!("E090", "`#{name}(…)` is not a constructor or record pattern", line)
    end
  end

  defp compile_record_pattern(name, args, line, state) do
    struct_tag = constructor_tag(name)

    # Expand shorthand field punning: a bare {:variable, _, name} inside a
    # record pattern binds a variable of the same name to the field of
    # the same name. A wildcard `_` keeps that field open.
    pairs =
      Enum.map(args, fn
        {:pair, _, _} = pair ->
          pair

        {:variable, _, "_"} = _wild ->
          # Wildcard alone inside record pattern is a no-op in terms of
          # binding; skip it.
          nil

        {:variable, vmeta, vname} when is_binary(vname) ->
          key = {:literal, [subtype: :symbol], String.to_atom(vname)}
          var = {:variable, vmeta, vname}
          {:pair, [], [key, var]}

        other ->
          {:pair, [], [{:literal, [subtype: :symbol], :_}, other]}
      end)
      |> Enum.reject(&is_nil/1)

    struct_entry =
      {:map_field_exact, line, {:atom, line, :__struct__}, {:atom, line, struct_tag}}

    {field_forms, state} =
      Enum.map_reduce(pairs, state, fn {:pair, _, [key, value_pat]}, st ->
        {k_form, st} = compile_map_key(key, st)
        {v_form, st} = do_compile(value_pat, st)
        {{:map_field_exact, line, k_form, v_form}, st}
      end)

    {{:map, line, [struct_entry | field_forms]}, state}
  end

  defp compile_constructor_pattern(name, args, line, state) do
    tag = constructor_tag(name)

    {arg_forms, state} =
      Enum.map_reduce(args, state, fn arg, st -> do_compile(arg, st) end)

    {{:tuple, line, [{:atom, line, tag} | arg_forms]}, state}
  end

  # -- Binary patterns --------------------------------------------------------
  #
  # v0.20.0 Parser wraps every `<<...>>` element in a
  # `{:bin_segment, meta, [value]}` node. Older AST shapes (bare
  # literals/variables) still appear in handwritten tests and legacy
  # stdlib fragments, so this compiler accepts both forms.

  defp compile_binary_pattern(meta, parts, state) do
    line = Keyword.get(meta, :line, state.line)
    subtype = Keyword.get(meta, :subtype)

    case subtype do
      :bytes ->
        {elements, state} =
          Enum.map_reduce(parts, state, fn part, st ->
            compile_binary_element(part, line, st)
          end)

        {{:bin, line, elements}, state}

      _ ->
        {form, state} = compile_literal(meta, parts, state)
        {form, state}
    end
  end

  defp compile_binary_element({:bin_segment, seg_meta, [value]}, line, state) do
    seg_line = Keyword.get(seg_meta, :line, line)
    {value_form, state} = do_compile(value, state)
    size_form = bin_segment_size(seg_meta, state)
    type_spec = bin_segment_typespec(seg_meta)

    value_form =
      case {value_form, Keyword.get(seg_meta, :type)} do
        # A literal `{:bin, ...}` inner wraps a single element; unwrap it
        # so size/type specifiers still apply to the payload.
        {{:bin, _, [{:bin_element, _, inner, _s, _ts}]}, _} -> inner
        _ -> value_form
      end

    {{:bin_element, seg_line, value_form, size_form, type_spec}, state}
  end

  defp compile_binary_element({:literal, meta, value}, _line, state) do
    {form, state} = compile_literal(meta, value, state)
    line = Keyword.get(meta, :line, state.line)

    element =
      case form do
        {:integer, _, _} = int_form ->
          {:bin_element, line, int_form, :default, :default}

        {:bin, _, [{:bin_element, _, inner, size, ts}]} ->
          {:bin_element, line, inner, size, ts}

        other ->
          {:bin_element, line, other, :default, :default}
      end

    {element, state}
  end

  defp compile_binary_element({:variable, _, name} = var, line, state) when is_binary(name) do
    {form, state} = do_compile(var, state)
    {{:bin_element, line, form, :default, :default}, state}
  end

  defp compile_binary_element(other, line, state) do
    {form, state} = do_compile(other, state)
    {{:bin_element, line, form, :default, :default}, state}
  end

  # Translate a `size(expr)` specifier into an Erlang abstract-form size.
  # Missing or non-integer sizes fall back to `:default`.
  defp bin_segment_size(seg_meta, state) do
    case Keyword.get(seg_meta, :size) do
      nil ->
        :default

      {:literal, lit_meta, value} ->
        line = Keyword.get(lit_meta, :line, state.line)
        {:integer, line, value}

      {:variable, var_meta, name} when is_binary(name) ->
        line = Keyword.get(var_meta, :line, state.line)

        # Reference an already-bound variable.
        case Map.fetch(state.vars, name) do
          {:ok, atom} -> {:var, line, atom}
          :error -> {:var, line, Codegen.mangle_var(name)}
        end

      _ ->
        :default
    end
  end

  # Build the Erlang type-specifier list from segment meta. Returns
  # `:default` when no specifiers were supplied so the Erlang defaults
  # (integer-unsigned-big-unit:1) apply.
  defp bin_segment_typespec(seg_meta) do
    type = Keyword.get(seg_meta, :type)
    sign = Keyword.get(seg_meta, :signedness)
    endian = Keyword.get(seg_meta, :endianness)
    unit = Keyword.get(seg_meta, :unit)

    parts =
      [type, sign, endian]
      |> Enum.filter(& &1)

    parts =
      case unit do
        {:literal, _, n} when is_integer(n) -> parts ++ [{:unit, n}]
        n when is_integer(n) -> parts ++ [{:unit, n}]
        _ -> parts
      end

    case parts do
      [] -> :default
      _ -> parts
    end
  end

  # -- Helpers ----------------------------------------------------------------

  defp ensure_pattern_guards(state) do
    if Map.has_key?(state, :pattern_guards) do
      state
    else
      Map.put(state, :pattern_guards, [])
    end
  end

  defp constructor?(name) when is_binary(name) do
    case String.first(name) do
      nil -> false
      first -> first == String.upcase(first) and first != String.downcase(first)
    end
  end

  defp constructor?(_), do: false

  defp constructor_tag(name) do
    name
    |> Macro.underscore()
    |> String.to_atom()
  end
end
