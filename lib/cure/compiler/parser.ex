defmodule Cure.Compiler.Parser do
  @moduledoc """
  Pratt parser for the Cure programming language.

  Transforms a token list from `Cure.Compiler.Lexer` into a MetaAST tree
  using Metastatic's 3-tuple format `{type, keyword_meta, children_or_value}`.

  The parser is indentation-aware: `:indent`/`:dedent`/`:newline` tokens from
  the lexer drive block structure.

  ## Record syntax

  Two record syntactic forms share the same `TypeName{...}` opening:

  - **Construction** `Point{x: 1, y: 2}` -- emits
    `{:function_call, [name: "Point", record: true, ...], field_pairs}`
  - **Update** `Point{p | x: 1}` -- emits
    `{:record_update, [name: "Point", ...], [base_expr | field_pairs]}`

  Detection uses a probe: after consuming `{`, one expression is parsed and
  the next token is inspected. If it is `|`, the parser commits to update
  mode. Otherwise it rewinds (saves and restores `pos` and `errors`) and
  falls back to normal field-pair parsing.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:parser, :node_parsed, ast, meta}` -- after each top-level expression
  - `{:parser, :parse_complete, ast, meta}` -- when parsing finishes
  - `{:parser, :error, error, meta}` -- on parse errors

  ## Usage

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens)
  """

  alias Cure.Compiler.Token
  alias Cure.Compiler.Parser.Precedence
  alias Cure.Pipeline.Events

  # -- Parser State ----------------------------------------------------------

  defstruct [:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}]

  # Keywords that can open a new top-level definition. Used by the
  # synchronize_to_statement/1 recovery helper to know when to stop
  # skipping tokens after a parse error.
  @definition_keywords [
    :fn,
    :local,
    :mod,
    :rec,
    :type,
    :use,
    :sup,
    :app,
    :proto,
    :impl,
    :interface,
    :implementation,
    :proof
  ]

  # Names parse_prefix/1's :identifier case already dispatches on via a
  # hard-coded clause (the soft-keyword container forms sup/app/macro/with,
  # plus the assert_type/rewrite builtins). A local macro can never claim one
  # of these: the guarded macro-use clause is checked FIRST, so an unguarded
  # collision would silently disable the existing form for the rest of the
  # module with no error raised. Reserved names simply keep today's
  # soft-keyword behavior; they are never macro-usable.
  @reserved_macro_keywords ~w(assert_type rewrite sup app with macro)

  # Decorators that describe the *module*, not the declaration that follows.
  # A `@name(...)` in this set NEVER attaches to the next `fn`/`rec`/`type`;
  # it always parses as a standalone `{:decorator, ...}` node so downstream
  # stages (codegen, preload) can read it as module metadata. `@group(:g)`
  # replaces the historical marker-function hack for stdlib preload groups.
  @module_level_decorators ~w(group)

  @type t :: %__MODULE__{}
  @type ast :: {atom(), keyword(), term()}
  @type result :: {ast(), t()}

  # -- Public API ------------------------------------------------------------

  @doc """
  Parse a token list into a MetaAST.

  Returns `{:ok, ast}` on success or `{:error, errors}` on failure.
  If the source contains multiple top-level expressions, they are wrapped
  in a `{:block, meta, exprs}` node.

  ## Options

  - `:file` -- filename for metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec parse([Token.t()], keyword()) :: {:ok, ast()} | {:error, [term()]}
  def parse(tokens, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)

    # Phase 1 (harvest): parse once with NO active macros, keep only the local
    # macro grammars. Use-sites may mis-parse here; we discard everything but
    # the {:macro_def, …} nodes and their (recovered) errors.
    harvest_state = %__MODULE__{tokens: tokens, file: file, emit_events: false}
    {harvest_exprs, _harvest_state} = parse_program(harvest_state)
    active = harvest_active_macros(harvest_exprs)

    # Phase 2 (authoritative): parse with active_macros seeded so use-sites expand.
    state = %__MODULE__{tokens: tokens, file: file, emit_events: emit?, active_macros: active}
    {exprs, state} = parse_program(state)

    ast =
      case exprs do
        [single] -> single
        many -> {:block, [line: 1, col: 1], many}
      end

    if emit? do
      Events.emit(:parser, :parse_complete, ast, Events.meta(file, 1))
    end

    case state.errors do
      [] -> {:ok, ast}
      errors -> {:error, Enum.reverse(errors)}
    end
  end

  # Collect every local macro rule, indexed by the rule's leading keyword, from
  # a parsed top-level expr list. Descends into containers (a `macro` inside a
  # `mod` is still a local macro of that module).
  defp harvest_active_macros(exprs) do
    exprs
    |> collect_macro_defs()
    |> Enum.reduce(%{}, fn {:macro_def, _meta, rules}, acc ->
      Enum.reduce(rules, acc, fn rule, acc2 ->
        Map.update(acc2, rule.keyword, [rule], &(&1 ++ [rule]))
      end)
    end)
  end

  defp collect_macro_defs(node) when is_list(node), do: Enum.flat_map(node, &collect_macro_defs/1)
  defp collect_macro_defs({:macro_def, _, _} = m), do: [m]
  defp collect_macro_defs({_t, _m, children}) when is_list(children), do: collect_macro_defs(children)
  defp collect_macro_defs(_), do: []

  # A use-site of an active macro keyword. Milestone-2 handles a single rule per
  # keyword with zero holes; multi-rule / hole matching is Task 3.
  defp parse_macro_use(state, keyword) do
    [rule | _] = Map.fetch!(state.active_macros, keyword)
    state = advance(state)  # consume the keyword token
    # Zero-hole rule: no segments to match; expand the template with no bindings.
    expanded = expand_rule(rule, %{})
    {expanded, state}
  end

  # Substitute hole bindings into a rule's template: replace any
  # `{:variable, _, name}` whose `name` is a bound hole with its bound AST.
  # A zero-hole rule (empty bindings) returns the template unchanged.
  defp expand_rule(rule, bindings) do
    subst_holes(rule.template, bindings)
  end

  defp subst_holes({:variable, _meta, name} = v, bindings) do
    case Map.fetch(bindings, name) do
      {:ok, arg} -> arg
      :error -> v
    end
  end

  defp subst_holes({t, meta, children}, bindings) when is_list(children) do
    {t, meta, Enum.map(children, &subst_holes(&1, bindings))}
  end

  defp subst_holes(other, _bindings), do: other

  # -- Program (top-level sequence) ------------------------------------------

  defp parse_program(state) do
    state = skip_newlines(state)
    parse_program(state, [])
  end

  defp parse_program(state, acc) do
    case peek(state) do
      %Token{type: :eof} ->
        {Enum.reverse(acc), state}

      %Token{type: :dedent} ->
        {Enum.reverse(acc), state}

      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        parse_program(state, [node | acc])

      %Token{type: :doc_comment} ->
        # Collect consecutive doc comments (including blocks separated by
        # blank-line gaps when no statement intervenes), attach to next
        # definition.
        {doc_text, state} = collect_all_doc_comments(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: type} when type in [:eof, :dedent] ->
            {Enum.reverse(acc), state}

          _ ->
            prev_errors = length(state.errors)
            {expr, state} = parse_expr(state, 0)
            expr = attach_doc(expr, doc_text)

            state =
              if length(state.errors) > prev_errors,
                do: synchronize_to_statement(state),
                else: state

            state = skip_newlines(state)
            parse_program(state, [expr | acc])
        end

      _ ->
        prev_errors = length(state.errors)
        {expr, state} = parse_expr(state, 0)
        # Recovery: synchronize after a broken top-level statement so subsequent
        # well-formed definitions (fn, mod, rec, etc.) are still parsed.
        state =
          if length(state.errors) > prev_errors,
            do: synchronize_to_statement(state),
            else: state

        state = skip_newlines(state)

        if state.emit_events do
          line =
            case expr do
              {_, meta, _} when is_list(meta) -> Keyword.get(meta, :line, 1)
              _ -> 1
            end

          Events.emit(:parser, :node_parsed, expr, Events.meta(state.file, max(line, 1)))
        end

        parse_program(state, [expr | acc])
    end
  end

  # -- Core Pratt Loop -------------------------------------------------------

  defp parse_expr(state, min_bp) do
    {left, state} = parse_prefix(state)
    parse_infix(state, left, min_bp)
  end

  defp parse_infix(state, left, min_bp) do
    token = peek(state)

    cond do
      # Postfix: function call  f(...)
      token.type == :lparen and min_bp <= 110 ->
        {left, state} = parse_call(state, left)
        parse_infix(state, left, min_bp)

      # Postfix: record construction  Name{...}
      token.type == :lbrace and min_bp <= 110 and is_pascal_case?(left) ->
        {left, state} = parse_record_construction(state, left)
        parse_infix(state, left, min_bp)

      true ->
        case Precedence.infix_bp(token.type) do
          {left_bp, _right_bp} when left_bp < min_bp ->
            {left, state}

          {left_bp, right_bp} ->
            state = advance(state)
            {ast, state} = build_infix_op(state, left, token, right_bp)
            state = reject_non_assoc_chain(state, token, left_bp)
            parse_infix(state, ast, min_bp)

          :not_infix ->
            {left, state}
        end
    end
  end

  # `a == b == c`, `a..b..c`, `a <-| b <-| c`: the spec's operator table and
  # `Precedence`'s own moduledoc call these non-associative, and `right_bp = left_bp + 1`
  # only stops the operator from swallowing a peer on its own right-hand side. It does
  # nothing to stop the loop above from picking the freshly-built node back up as a new
  # left operand at the original `min_bp` — mechanically the same trick `+` and `*` use to
  # left-associate. So the table's "non-assoc" entries parsed as plain left-associative
  # operators, and `a <-| b <-| c` quietly fanned out into two sends.
  #
  # Reject the chain outright, as Haskell (`infix 4 ==`), Rust, and Agda/Idris all do. The
  # error is recorded rather than raised, so the parser keeps going and reports the rest of
  # the file's problems in the same pass.
  defp reject_non_assoc_chain(state, token, left_bp) do
    next = peek(state)

    # Every operator sharing a left BP with a non-associative one is in its class.
    chained? =
      Precedence.non_assoc?(token.type) and match?({^left_bp, _}, Precedence.infix_bp(next.type))

    if chained? do
      error =
        {:non_associative, Precedence.operator_symbol(token.type), :chained_with,
         Precedence.operator_symbol(next.type), next.line, next.col}

      add_error(state, error)
    else
      state
    end
  end

  # -- Prefix Parsing --------------------------------------------------------

  defp parse_prefix(state) do
    token = peek(state)

    case token.type do
      # Literals
      :integer ->
        {literal(:integer, token), advance(state)}

      :float ->
        {literal(:float, token), advance(state)}

      :string ->
        {literal(:string, token), advance(state)}

      :bool ->
        {literal(:boolean, token), advance(state)}

      nil ->
        {literal(:null, token), advance(state)}

      :atom ->
        {literal(:symbol, token), advance(state)}

      :regex ->
        {literal(:regex, token), advance(state)}

      :char ->
        {literal(:char, token), advance(state)}

      # A hole `?name` / `??` — a deferred term (design spec §6 / M8.5).
      :hole ->
        {{:hole, [name: token.value, line: token.line, col: token.col], []}, advance(state)}

      :string_interpolation ->
        parse_string_interpolation(state)

      # Variables / identifiers
      :identifier ->
        case token.value do
          # A use-site of a locally-defined macro keyword. Checked FIRST so a
          # macro keyword wins, but guarded so non-macro identifiers are
          # untouched. (Reserved soft-keyword names are excluded below.)
          name when is_map_key(state.active_macros, name) and name not in @reserved_macro_keywords ->
            parse_macro_use(state, name)

          "assert_type" ->
            parse_assert_type(state, token)

          "rewrite" ->
            parse_rewrite(state, token)

          # Soft keyword: `sup Name ...` at statement-prefix position is
          # the supervisor container. When `sup` is followed by anything
          # other than an identifier (`:`, `,`, `}`, `)`, etc.) we treat
          # it as a plain variable, preserving legacy field/local uses.
          "sup" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} ->
                parse_supervisor(state)

              _ ->
                {variable(token), advance(state)}
            end

          # Soft keyword: `app Name ...` at statement-prefix position is
          # the application container. Everywhere else `app` remains a
          # plain identifier, so pre-existing code that happens to use
          # the name keeps parsing.
          "app" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} ->
                parse_app_container(state)

              _ ->
                {variable(token), advance(state)}
            end

          # Contextual keyword: `with e <arms>` is a with-abstraction only in
          # expression-prefix position and only when what follows `with` can
          # begin a scrutinee. The FSM/actor payload-binder `with` is consumed
          # inside parse_fsm/parse_actor before it reaches here, so those uses
          # (and any bare `with` operand) keep their identifier meaning.
          "with" ->
            if with_scrutinee_ahead?(state) do
              parse_with_abs(state, token)
            else
              {variable(token), advance(state)}
            end

          # Soft keyword: `macro Name …` at statement-prefix position is the
          # macro container. `macro` followed by anything other than an
          # identifier stays a plain variable (non-breaking, like sup/app).
          "macro" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} ->
                parse_macro_def(state)

              _ ->
                {variable(token), advance(state)}
            end

          _ ->
            {variable(token), advance(state)}
        end

      # Unary operators
      :minus ->
        parse_unary(state, :arithmetic)

      :not_op ->
        parse_unary(state, :boolean)

      :bnot_op ->
        parse_unary(state, :bitwise)

      # Grouping
      :lparen ->
        parse_grouped(state)

      # Collections
      :lbracket ->
        parse_list_or_comprehension(state)

      :tuple_open ->
        parse_tuple(state)

      :map_open ->
        parse_map(state)

      # Binary literal
      :binary_open ->
        parse_binary_literal(state)

      # Control flow
      :keyword ->
        parse_keyword_prefix(state, token)

      # At sign (decorator / attribute)
      :at ->
        parse_at(state)

      # Pin operator for patterns: ^x -- introduced in v0.18.0 as a
      # prefix that references a previously-bound variable rather than
      # rebinding. Compiled via {:pin, meta, [inner]}.
      :caret ->
        parse_pin(state)

      # Forced (dot) pattern: a leading `.` in prefix position introduces a
      # forced-equation pattern (`.x`, `.(S(k))`). The inner term is a value the
      # match must be convertible with rather than a fresh binder. Parsing
      # succeeds in any position by design; using a forced pattern outside a
      # pattern is rejected later, at elaboration. Infix `.` (module paths like
      # `Std.String`) is a different grammar position (handle_infix_op :dot) and
      # never reaches this prefix clause.
      :dot ->
        {inner, state} = parse_forced_inner(advance(state))
        {{:forced_pattern, [line: token.line, col: token.col], inner}, state}

      # Named-implicit dot pattern `{ name = <expr> }` in a constructor-argument
      # position — annotates an erased implicit index by name (Lean/Idris-style),
      # e.g. `vcons({k = .m}, h, r)`. Only the `{ IDENT = … }` shape is a
      # named-implicit; every other leading `{` in prefix position keeps its
      # previous unexpected-token error (records use the postfix `Name{…}` form,
      # maps use `#{…}`, blocks use indentation — none reach this clause).
      :lbrace ->
        case {peek_at(state, 1), peek_at(state, 2)} do
          {%Token{type: :identifier}, %Token{type: :assign}} ->
            parse_named_implicit_pat(state, token)

          _ ->
            error = {:unexpected_token, token.type, token.line, token.col}
            state = add_error(state, error)
            {error_node(token), advance(state)}
        end

      # Indent starts a block
      :indent ->
        parse_block(state)

      _ ->
        error = {:unexpected_token, token.type, token.line, token.col}
        state = add_error(state, error)
        {error_node(token), advance(state)}
    end
  end

  # -- assert_type builtin (v0.19.0) ----------------------------------------
  #
  # `assert_type expr : T` is a compile-time type assertion. The type
  # checker verifies `expr : T`; the codegen strips the wrapper and emits
  # only `expr`, so there is no runtime cost.
  defp parse_assert_type(state, token) do
    # Consume the `assert_type` identifier.
    state = advance(state)
    # Parse the expression being asserted. Stop before `:` (BP 6 is
    # high enough to keep the colon for us; let binding uses the same trick).
    {expr, state} = parse_expr(state, 6)
    state = expect(state, :colon)
    {type_ast, state} = parse_type_expr(state)
    ast = {:assert_type, [line: token.line, col: token.col], [expr, type_ast]}
    {ast, state}
  end

  # -- Propositional equality rewrite ---------------------------------------
  #
  # `rewrite proof in body` elaborates to a Core rewrite with an explicit motive
  # synthesized by `Cure.Elab`. `rewrite` remains a soft keyword so existing
  # values named `rewrite` only switch forms when used in expression-prefix
  # position.
  defp parse_rewrite(state, token) do
    state = advance(state)
    {proof, state} = parse_expr(state, 0)
    state = expect_keyword(state, :in)
    {body, state} = parse_expr(state, 0)
    {{:rewrite_expr, [line: token.line, col: token.col], [proof, body]}, state}
  end

  # -- Pin Operator (pattern position) ---------------------------------------

  defp parse_pin(state) do
    token = peek(state)
    state = advance(state)
    inner_token = peek(state)

    case inner_token.type do
      :identifier ->
        state = advance(state)
        inner = variable(inner_token)
        ast = {:pin, [line: token.line, col: token.col], [inner]}
        {ast, state}

      _ ->
        # Fallback: parse any prefix expression and wrap it so that
        # `Cure.Compiler.PatternCompiler.compile_pin/3` can unwrap it.
        {inner, state} = parse_prefix(state)
        ast = {:pin, [line: token.line, col: token.col], [inner]}
        {ast, state}
    end
  end

  # -- Forced (dot) pattern inner --------------------------------------------
  #
  # After a leading `.`, read the forced term. `.(expr)` parses a full
  # parenthesised expression (a compound forced pattern like `.(S(k))`); a bare
  # `.x` reads a single primary (identifier / literal) as the forced value.
  defp parse_forced_inner(state) do
    case peek(state).type do
      :lparen -> parse_grouped(state)
      _ -> parse_prefix(state)
    end
  end

  # -- Named-implicit dot pattern --------------------------------------------
  #
  # `{ name = <expr> }` annotates a constructor's erased implicit index `name`
  # with a forced value in a pattern-argument position. Valid only as a
  # constructor-pattern argument; ordinary expression elaboration rejects it
  # (`{:named_implicit_not_in_pattern, …}`). The inner expression is parsed with
  # the full expression grammar, so a leading `.` yields a `{:forced_pattern,…}`.
  defp parse_named_implicit_pat(state, brace_token) do
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = expect(state, :assign)
    {inner, state} = parse_expr(state, 0)
    state = expect(state, :rbrace)
    meta = [line: brace_token.line, col: brace_token.col]
    {{:named_implicit_pat, meta, name, inner}, state}
  end

  # -- Literals --------------------------------------------------------------

  defp literal(subtype, token) do
    {:literal, [subtype: subtype, line: token.line, col: token.col], token.value}
  end

  defp variable(token) do
    {:variable, [scope: :local, line: token.line, col: token.col], token.value}
  end

  defp error_node(token) do
    {:literal, [subtype: :null, line: token.line, col: token.col, error: true], nil}
  end

  # -- String Interpolation --------------------------------------------------

  defp parse_string_interpolation(state) do
    token = peek(state)
    state = advance(state)
    parts = token.value

    parsed_parts =
      Enum.map(parts, fn
        {:string_part, s} ->
          {:literal, [subtype: :string], s}

        {:expr, expr_tokens} ->
          # Append an EOF token so the sub-parser terminates
          sub_tokens = expr_tokens ++ [Token.new(:eof, nil, token.line, token.col)]
          sub_state = %__MODULE__{tokens: sub_tokens, file: state.file, emit_events: false}
          {expr, _} = parse_expr(sub_state, 0)
          expr
      end)

    ast = {:string_interpolation, [line: token.line, col: token.col], parsed_parts}
    {ast, state}
  end

  # -- Unary Operators -------------------------------------------------------

  defp parse_unary(state, category) do
    token = peek(state)
    state = advance(state)
    rbp = Precedence.prefix_bp(token.type)
    {operand, state} = parse_expr(state, rbp)
    op = Precedence.operator_symbol(token.type)
    ast = {:unary_op, [category: category, operator: op, line: token.line, col: token.col], [operand]}
    {ast, state}
  end

  # -- Grouping ( ... ) ------------------------------------------------------

  defp parse_grouped(state) do
    open = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        # `()` — the unit value (Swift-style): the sole inhabitant of `Unit`. It
        # is NOT an empty tuple; it lowers to the nullary `unit` constructor.
        state = advance(state)
        {{:unit_value, [line: open.line, col: open.col]}, state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        state = expect(state, :rparen)
        {expr, state}
    end
  end

  # -- Infix Operators -------------------------------------------------------

  # Build the node for one infix operator whose left operand is already parsed. The
  # caller resumes the Pratt loop, so it can see the token that follows.
  defp build_infix_op(state, left, token, right_bp) do
    case token.type do
      # Pipe desugaring: a |> f  or  a |> f(b, c)
      :pipe ->
        {right, state} = parse_expr(state, right_bp)
        {desugar_pipe(left, right, token), state}

      # Melquiades operator: `pid <-| message` or `pid ✉ message`.
      # Lowers to `{:send, meta, [target, message]}` and carries the
      # author's choice of ASCII vs unicode form in `:melquiades_form` so
      # the printer can round-trip it.
      :melquiades ->
        {right, state} = parse_expr(state, right_bp)
        form = melquiades_form(token.value)
        meta = [line: token.line, col: token.col, melquiades_form: form]
        {{:send, meta, [left, right]}, state}

      # Dot access: obj.field -> {:attribute_access, ...}
      :dot ->
        field_token = peek(state)
        state = advance(state)
        field_name = to_string(field_token.value)
        meta = [attribute: field_name, line: token.line, col: token.col]
        {{:attribute_access, meta, [left]}, state}

      # Range operators
      type when type in [:range, :range_inclusive] ->
        {right, state} = parse_expr(state, right_bp)
        inclusive = type == :range_inclusive
        {{:range, [inclusive: inclusive, line: token.line, col: token.col], [left, right]}, state}

      # Assignment
      :assign ->
        {right, state} = parse_expr(state, right_bp)
        {{:assignment, [line: token.line, col: token.col], [left, right]}, state}

      # Augmented assignment
      type when type in [:plus_assign, :minus_assign, :star_assign, :slash_assign] ->
        {right, state} = parse_expr(state, right_bp)
        op = augmented_op(type)
        meta = [operator: op, line: token.line, col: token.col]
        {{:augmented_assignment, meta, [left, right]}, state}

      # Regular binary operator
      _ ->
        {right, state} = parse_expr(state, right_bp)
        category = Precedence.operator_category(token.type)
        op = Precedence.operator_symbol(token.type)
        meta = [category: category, operator: op, line: token.line, col: token.col]
        {{:binary_op, meta, [left, right]}, state}
    end
  end

  defp augmented_op(:plus_assign), do: :+
  defp augmented_op(:minus_assign), do: :-
  defp augmented_op(:star_assign), do: :*
  defp augmented_op(:slash_assign), do: :/

  # `<-|` -> :ascii, `✉` -> :unicode. Any other lexeme (unlikely, but
  # we guard anyway) falls back to :ascii.
  defp melquiades_form("<-|"), do: :ascii
  defp melquiades_form("✉"), do: :unicode
  defp melquiades_form(_), do: :ascii

  # -- Pipe Desugaring -------------------------------------------------------

  defp desugar_pipe(left, right, token) do
    case right do
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name, "unknown")
        new_meta = Keyword.merge(meta, pipe: true, line: token.line, col: token.col)
        new_meta = Keyword.put(new_meta, :name, name)
        {:function_call, new_meta, [left | args]}

      {:variable, _meta, name} ->
        {:function_call, [name: name, pipe: true, line: token.line, col: token.col], [left]}

      _ ->
        {:function_call, [name: "unknown", pipe: true, line: token.line, col: token.col], [left, right]}
    end
  end

  # -- Function Call ---------------------------------------------------------

  defp parse_call(state, func) do
    token = peek(state)
    state = advance(state)
    {args, state} = parse_call_args(state)
    name = extract_call_name(func)

    meta = [name: name, line: token.line, col: token.col]

    # When the callee is an expression (e.g. f(x)(y)), preserve it so
    # the codegen can compile it as an expression-based call.
    meta =
      if name == "unknown" do
        Keyword.put(meta, :callee, func)
      else
        meta
      end

    ast = {:function_call, meta, args}
    {ast, state}
  end

  defp parse_call_args(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], advance(state)}

      _ ->
        {first, state} = parse_expr(state, 0)
        {first, state} = maybe_wrap_as(first, state)
        state = skip_newlines(state)
        {rest, state} = parse_more_args(state)
        state = skip_newlines(state)
        state = expect(state, :rparen)
        {[first | rest], state}
    end
  end

  defp parse_more_args(state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {expr, state} = parse_expr(state, 0)
        {expr, state} = maybe_wrap_as(expr, state)
        state = skip_newlines(state)
        {rest, state} = parse_more_args(state)
        {[expr | rest], state}

      _ ->
        {[], state}
    end
  end

  defp extract_call_name({:variable, _meta, name}), do: name

  defp extract_call_name({:attribute_access, meta, [parent]}) do
    # Reconstruct dotted name: Mod.Sub.func -> "Mod.Sub.func"
    attr = Keyword.get(meta, :attribute, "unknown")
    parent_name = extract_dotted_path(parent)

    case parent_name do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_call_name(_), do: "unknown"

  defp extract_dotted_path({:variable, _, name}), do: name

  defp extract_dotted_path({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute, "unknown")

    case extract_dotted_path(parent) do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_dotted_path(_), do: nil

  @doc "Reconstruct a dotted path string from an attribute_access/variable node, or nil."
  def dotted_path_of(node), do: extract_dotted_path(node)

  # -- Record Construction / Update  Name{fields}  or  Name{base | overrides} --

  defp parse_record_construction(state, name_ast) do
    open_token = peek(state)
    # consume {
    state = advance(state)

    rec_name =
      case name_ast do
        {:variable, _, n} -> n
        _ -> "unknown"
      end

    line = open_token.line
    col = open_token.col

    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        # Empty construction: TypeName{}
        state = advance(state)
        ast = {:function_call, [name: rec_name, record: true, line: line, col: col], []}
        {ast, state}

      _ ->
        # Probe: parse one expression to detect update syntax.
        # :bar ("|") is not an infix operator, so parse_expr stops naturally at it.
        # We save pos+errors so we can fully rewind on a non-update literal.
        saved_pos = state.pos
        saved_errors = state.errors
        {base_expr, probe_state} = parse_expr(state, 0)
        probe_state = skip_newlines(probe_state)

        case peek(probe_state) do
          %Token{type: :bar} ->
            # Record update: TypeName{base | field: val, ...}
            # consume "|"
            probe_state = advance(probe_state)
            probe_state = skip_newlines(probe_state)
            {fields, probe_state} = parse_map_pairs(probe_state, :rbrace)
            probe_state = expect(probe_state, :rbrace)
            ast = {:record_update, [name: rec_name, line: line, col: col], [base_expr | fields]}
            {ast, probe_state}

          _ ->
            # Not update syntax: rewind completely and parse as plain construction.
            state = %{state | pos: saved_pos, errors: saved_errors}
            {fields, state} = parse_map_pairs(state, :rbrace)
            state = expect(state, :rbrace)
            ast = {:function_call, [name: rec_name, record: true, line: line, col: col], fields}
            {ast, state}
        end
    end
  end

  defp is_pascal_case?({:variable, _, <<first, _rest::binary>>}) when first in ?A..?Z, do: true
  defp is_pascal_case?(_), do: false

  # -- Collections -----------------------------------------------------------

  # List: [1, 2, 3] or [h | t] or comprehension [x for x <- list]
  defp parse_list_or_comprehension(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        # Empty list
        {_, state} = {nil, advance(state)}
        {{:list, [line: token.line, col: token.col], []}, state}

      _ ->
        {first, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        case peek(state) do
          # Comprehension: [expr for ...]
          %Token{type: :keyword, value: :for} ->
            parse_comprehension(state, first, token)

          # Cons: [h | t]
          %Token{type: :bar} ->
            state = advance(state)
            state = skip_newlines(state)
            {tail, state} = parse_expr(state, 0)
            state = skip_newlines(state)
            state = expect(state, :rbracket)
            ast = {:list, [cons: true, line: token.line, col: token.col], [first, tail]}
            {ast, state}

          # Multi-head cons or regular list: [a, b, c]  or  [a, b | rest]
          _ ->
            {rest_heads, state} = parse_multi_head_list_rest(state)

            case peek(state) do
              %Token{type: :bar} ->
                # `[a, b | rest]` -- desugar into right-associated cons
                # cells: `[a | [b | rest]]`.
                state = advance(state)
                state = skip_newlines(state)
                {tail, state} = parse_expr(state, 0)
                state = skip_newlines(state)
                state = expect(state, :rbracket)

                heads = [first | rest_heads]
                ast = build_multi_head_cons(heads, tail, token)
                {ast, state}

              _ ->
                state = skip_newlines(state)
                state = expect(state, :rbracket)
                ast = {:list, [line: token.line, col: token.col], [first | rest_heads]}
                {ast, state}
            end
        end
    end
  end

  # Parse `, expr` repeatedly, stopping before `|` or `]`.
  defp parse_multi_head_list_rest(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        {rest, state} = parse_multi_head_list_rest(state)
        {[expr | rest], state}

      _ ->
        {[], state}
    end
  end

  # Build nested cons cells right-associatively:
  #   [a, b, c | rest]  ->  [a | [b | [c | rest]]]
  defp build_multi_head_cons([head], tail, token),
    do: {:list, [cons: true, line: token.line, col: token.col], [head, tail]}

  defp build_multi_head_cons([head | rest], tail, token) do
    nested = build_multi_head_cons(rest, tail, token)
    {:list, [cons: true, line: token.line, col: token.col], [head, nested]}
  end

  # Tuple: %[a, b, c]
  defp parse_tuple(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        {{:tuple, [line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {first, state} = parse_expr(state, 0)
        {rest, state} = parse_comma_exprs(state)
        state = skip_newlines(state)
        state = expect(state, :rbracket)

        {:tuple, [line: token.line, col: token.col], [first | rest]}
        |> then(&{&1, state})
    end
  end

  # Map: %{k: v, ...} or %{k => v, ...}
  defp parse_map(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {{:map, [line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {pairs, state} = parse_map_pairs(state, :rbrace)
        state = skip_newlines(state)
        state = expect(state, :rbrace)
        {{:map, [line: token.line, col: token.col], pairs}, state}
    end
  end

  defp parse_map_pairs(state, closing) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], state}

      _ ->
        {pair, state} = parse_map_pair(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, state} = parse_map_pairs(state, closing)
            {[pair | rest], state}

          _ ->
            {[pair], state}
        end
    end
  end

  defp parse_map_pair(state) do
    token = peek(state)
    next = peek_at(state, 1)

    cond do
      # Shorthand: identifier followed by colon  =>  atom key
      token.type == :identifier and next != nil and next.type == :colon ->
        key_atom = String.to_atom(token.value)
        state = advance(state) |> advance()
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)
        pair = {:pair, [], [{:literal, [subtype: :symbol], key_atom}, value]}
        {pair, state}

      # Pattern/construction field punning (v0.18.0): a bare identifier
      # followed by `,` or the closing delimiter is shorthand for
      # `name: name`. Used both in record patterns (`Point{x, y}`) and in
      # map-construction shorthand (`%{x, y}` -> `%{x: x, y: y}`).
      token.type == :identifier and next != nil and
          next.type in [:comma, :rbrace, :newline] ->
        key_atom = String.to_atom(token.value)
        var_ast = variable(token)
        state = advance(state)
        pair = {:pair, [pun: true], [{:literal, [subtype: :symbol], key_atom}, var_ast]}
        {pair, state}

      true ->
        # Explicit: key => value
        {key, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        state = expect(state, :fat_arrow)
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)
        pair = {:pair, [], [key, value]}
        {pair, state}
    end
  end

  # Binary literal / pattern: <<seg1, seg2, ...>>
  #
  # Each segment is `value [:: specifier_chain]` where the chain is a
  # hyphen-joined list of specifiers (mirrors Elixir):
  #
  #   integer | float | bits | bitstring | bytes | binary | utf8 | utf16 | utf32
  #   signed | unsigned
  #   big | little | native
  #   size(expr)
  #   unit(n)
  #   <integer>           (shorthand for size(<integer>))
  #
  # The segment is emitted as
  #   {:bin_segment, [type:, signedness:, endianness:, size:, unit:, line:, col:], [value]}
  # with each keyword omitted when the caller did not supply one. The enclosing
  # literal keeps its historical shape
  #   {:literal, [subtype: :bytes, line:, col:], [bin_segment, ...]}
  # so downstream consumers that only care about the outer shape are unaffected.
  defp parse_binary_literal(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :binary_close} ->
        {{:literal, [subtype: :bytes, line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {segments, state} = parse_bin_segments(state, [])
        state = expect(state, :binary_close)
        ast = {:literal, [subtype: :bytes, line: token.line, col: token.col], segments}
        {ast, state}
    end
  end

  defp parse_bin_segments(state, acc) do
    {segment, state} = parse_bin_segment(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        parse_bin_segments(state, [segment | acc])

      _ ->
        {Enum.reverse([segment | acc]), state}
    end
  end

  defp parse_bin_segment(state) do
    start_token = peek(state)
    {value, state} = parse_expr(state, 0)

    {specifier_meta, state} =
      case peek(state) do
        %Token{type: :colon_colon} ->
          state = advance(state)
          parse_bin_specifier_chain(state, [])

        _ ->
          {[], state}
      end

    meta =
      [line: start_token.line, col: start_token.col] ++ specifier_meta

    {{:bin_segment, meta, [value]}, state}
  end

  defp parse_bin_specifier_chain(state, acc) do
    {entry, state} = parse_bin_specifier(state)
    acc = merge_specifier(acc, entry)

    case peek(state) do
      %Token{type: :minus} ->
        state = advance(state)
        parse_bin_specifier_chain(state, acc)

      _ ->
        {acc, state}
    end
  end

  # A single specifier fragment. Accepts:
  #   * identifiers (`integer`, `binary`, `utf8`, `size`, `unit`, etc.)
  #   * `size(expr)` and `unit(n)` call-style forms
  #   * bare integer literals as shorthand for `size(n)`
  # Returns `{:type | :signedness | :endianness | :size | :unit, value}`.
  defp parse_bin_specifier(state) do
    token = peek(state)

    case token.type do
      :integer ->
        state = advance(state)
        {{:size, {:literal, [subtype: :integer, line: token.line, col: token.col], token.value}}, state}

      :identifier ->
        name = to_string(token.value)
        state = advance(state)

        case peek(state) do
          %Token{type: :lparen} when name in ["size", "unit"] ->
            state = advance(state)
            state = skip_newlines(state)
            {arg, state} = parse_expr(state, 0)
            state = skip_newlines(state)
            state = expect(state, :rparen)
            {{String.to_atom(name), arg}, state}

          _ ->
            {classify_bin_specifier_name(name), state}
        end

      _ ->
        # Unknown specifier token -- consume and ignore so we don't deadlock.
        state = advance(state)
        {{:type, :any}, state}
    end
  end

  defp classify_bin_specifier_name(name) do
    type_names = ~w(integer float bits bitstring bytes binary utf8 utf16 utf32)
    sign_names = ~w(signed unsigned)
    endian_names = ~w(big little native)

    cond do
      name in type_names -> {:type, String.to_atom(name)}
      name in sign_names -> {:signedness, String.to_atom(name)}
      name in endian_names -> {:endianness, String.to_atom(name)}
      true -> {:type, String.to_atom(name)}
    end
  end

  # Merge a single specifier entry into the meta-accumulator. Later
  # entries override earlier entries for the same axis, matching
  # Elixir's "last wins" behaviour for duplicate specifiers.
  defp merge_specifier(acc, {key, value}) do
    Keyword.put(acc, key, value)
  end

  # -- Comprehensions --------------------------------------------------------

  defp parse_comprehension(state, body, open_token) do
    # Already consumed body, currently at `for` keyword
    state = advance(state)
    state = skip_newlines(state)
    {generators_and_filters, state} = parse_generators(state)
    state = skip_newlines(state)
    state = expect(state, :rbracket)
    ast = {:comprehension, [line: open_token.line, col: open_token.col], [body | generators_and_filters]}
    {ast, state}
  end

  defp parse_generators(state) do
    {item, state} = parse_generator_or_filter(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_generators(state)
        {[item | rest], state}

      _ ->
        {[item], state}
    end
  end

  defp parse_generator_or_filter(state) do
    # The lexer emits `<` and `-` as separate tokens for `<-`.
    # Strategy: parse LHS at BP above comparison (42) so `<` is not consumed,
    # then check if `< -` follows (generator) or fall back to a full-BP filter.
    # v0.22.0: a leading `:binary_open` (`<<`) opens a binary-pattern
    # generator (`for <<b <- buf>>`) that otherwise mis-tokenises as
    # a less-than comparison inside the `<<...>>` literal.
    case peek(state) do
      %Token{type: :binary_open} -> parse_binary_generator(state)
      _ -> parse_non_binary_generator_or_filter(state)
    end
  end

  defp parse_non_binary_generator_or_filter(state) do
    saved_pos = state.pos
    {expr, state} = parse_expr(state, 42)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :lt} ->
        next = peek_at(state, 1)

        if next != nil and next.type == :minus do
          # Generator: pattern <- collection
          state = advance(state) |> advance()
          state = skip_newlines(state)
          {collection, state} = parse_expr(state, 0)
          {{:generator, [], [expr, collection]}, state}
        else
          # Not a generator. Re-parse from saved position at BP 0 for full filter expression.
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          {{:filter, [], [filter_expr]}, state}
        end

      _ ->
        # Check if the high-BP parse left something behind (e.g. `x > 0`).
        # If the expression was just a variable and there's an operator next, re-parse at BP 0.
        token = peek(state)

        if Precedence.infix_bp(token.type) != :not_infix do
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          {{:filter, [], [filter_expr]}, state}
        else
          {{:filter, [], [expr]}, state}
        end
    end
  end

  # v0.22.0: binary-pattern generator `<<seg1, seg2, ... <- source>>`.
  # Elixir-style surface syntax wraps the whole generator in `<<...>>`:
  # the pattern segments, the `<-` arrow, and the source expression all
  # live between the opening `<<` and the closing `>>`. The `<-` itself
  # is emitted by the lexer as `:lt` followed by `:minus`; we parse
  # segments at BP 42 so the leading `<` of `<-` is not consumed as a
  # less-than comparison. The resulting AST is
  # `{:binary_generator, meta, [pattern, source]}` where `pattern` is
  # a `{:literal, [subtype: :bytes], segments}` (reusing the v0.21.0
  # pattern-compiler path) and the codegen lowers it to Erlang's
  # `b_generate` qualifier.
  defp parse_binary_generator(state) do
    open_token = peek(state)
    state = advance(state)
    state = skip_newlines(state)
    {segments, state} = parse_binary_generator_segments(state, [])

    # Consume `<-` (lexed as `:lt` + `:minus`).
    state =
      case {peek(state), peek_at(state, 1)} do
        {%Token{type: :lt}, %Token{type: :minus}} ->
          state |> advance() |> advance()

        _ ->
          expect(state, :lt) |> expect(:minus)
      end

    state = skip_newlines(state)
    {source, state} = parse_expr(state, 0)
    state = skip_newlines(state)
    state = expect(state, :binary_close)

    pattern =
      {:literal, [subtype: :bytes, line: open_token.line, col: open_token.col], segments}

    meta = [line: open_token.line, col: open_token.col]
    {{:binary_generator, meta, [pattern, source]}, state}
  end

  # Parse `seg1, seg2, ...` inside a binary-generator, stopping when the
  # next token is either the closing `>>` (`:binary_close`) or the
  # generator arrow `<-` (`:lt` + `:minus`). Each segment is parsed via
  # `parse_bin_generator_segment/1` so specifier chains (`::integer`,
  # `::size(n)`, ...) carry through.
  defp parse_binary_generator_segments(state, acc) do
    case peek(state) do
      %Token{type: :binary_close} ->
        {Enum.reverse(acc), state}

      %Token{type: :lt} ->
        next = peek_at(state, 1)

        if next != nil and next.type == :minus do
          {Enum.reverse(acc), state}
        else
          advance_into_segment(state, acc)
        end

      _ ->
        advance_into_segment(state, acc)
    end
  end

  defp advance_into_segment(state, acc) do
    {segment, state} = parse_bin_generator_segment(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        parse_binary_generator_segments(state, [segment | acc])

      _ ->
        {Enum.reverse([segment | acc]), state}
    end
  end

  # Variant of `parse_bin_segment/1` that stops before `<` (BP 40) so
  # the trailing `<-` of a binary generator is not mis-tokenised as a
  # less-than comparison operator.
  defp parse_bin_generator_segment(state) do
    start_token = peek(state)
    {value, state} = parse_expr(state, 42)

    {specifier_meta, state} =
      case peek(state) do
        %Token{type: :colon_colon} ->
          state = advance(state)
          parse_bin_specifier_chain(state, [])

        _ ->
          {[], state}
      end

    meta =
      [line: start_token.line, col: start_token.col] ++ specifier_meta

    {{:bin_segment, meta, [value]}, state}
  end

  # -- Keyword-Triggered Prefix Expressions ----------------------------------

  defp parse_keyword_prefix(state, token) do
    case token.value do
      :let ->
        parse_let(state)

      :if ->
        parse_if(state)

      :match ->
        parse_match(state)

      :pickup ->
        parse_pickup(state)

      :return ->
        parse_keyword_unary(state, :early_return)

      :throw ->
        parse_keyword_unary(state, :throw)

      :yield ->
        parse_keyword_unary(state, :yield)

      :spawn ->
        parse_keyword_unary(state, :async_operation)

      :send ->
        parse_send(state)

      :receive ->
        parse_receive(state)

      :try ->
        parse_try(state)

      # Structural constructs (Milestone 3)
      :fn ->
        parse_fn_or_lambda(state)

      :local ->
        parse_local(state)

      :mod ->
        parse_module(state)

      :rec ->
        parse_record(state)

      :type ->
        parse_type_def(state)

      # `opaque type Name(params)` — a constructor-less, non-eliminable carrier
      # type. Consume `opaque`, then parse the type head with the opaque flag.
      :opaque ->
        parse_type_def(advance(state), opaque: true)

      # `primitive Name` — an irreducible machine base type (Int/Float/Binary).
      # No constructors, no `=`; the `@builtin(:tag)` marker names its Core node.
      :primitive ->
        parse_primitive_def(state)

      :typealias ->
        parse_typealias(state)

      :proto ->
        parse_proto(state)

      :proof ->
        parse_proof_container(state)

      :impl ->
        parse_impl(state)

      :interface ->
        parse_interface(state)

      :implementation ->
        parse_implementation(state)

      :fsm ->
        parse_fsm(state)

      :actor ->
        parse_actor(state)

      :use ->
        parse_use(state)

      _ ->
        # Treat unknown keywords as identifiers (e.g., type names used as values)
        {variable(token), advance(state)}
    end
  end

  # -- Let Binding -----------------------------------------------------------

  defp parse_let(state) do
    token = peek(state)
    state = advance(state)

    # Parse pattern (LHS) at high enough BP to NOT consume `=`
    # Assignment has BP 5, so parsing at BP 6 stops before `=`
    {pattern, state} = parse_expr(state, 6)

    # `: Type`, or a graded `:g [Type]` — the type is optional after a grade because
    # `let_inferred/8` synthesises it from the rhs (Idris `letBinder` does the same).
    let_name = case pattern do
      {:variable, _, n} -> n
      _ -> "let binding"
    end
    {grade, type_ann, state} = parse_binder_annotation(state, let_name, [:assign])

    # A grade attaches to a SIMPLE VARIABLE binder only. A destructuring `let` lowers
    # to a `case`, whose binders take their grades from the constructor's field
    # quantities, so there is no single Core binder for this grade to land on. Reject
    # it here rather than parse it and silently ignore the annotation.
    state =
      if grade && not match?({:variable, _, _}, pattern) do
        add_error(state, {:graded_let_requires_variable, grade, token.line, token.col})
      else
        state
      end

    # Expect =
    state = expect(state, :assign)
    state = skip_newlines(state)

    # Parse value (RHS) -- might be an indented block
    {value, state} = parse_expr_or_block(state)

    meta = [let: true, line: token.line, col: token.col]
    meta = if type_ann, do: Keyword.put(meta, :type_annotation, type_ann), else: meta
    meta = if grade, do: Keyword.put(meta, :grade, grade), else: meta

    assignment = {:assignment, meta, [pattern, value]}

    # Optional ML-style `let <pat> = <value> in <body>`: an expression-position
    # binder. Desugar to the same two-statement `{:block, …}` node a block-form
    # `let` followed by a trailing expression produces, which the elaborator
    # already lowers to a β-redex `(λ x:T. body) value`. Without `in`, `let`
    # stays a block statement (the enclosing block collects the following
    # statements), exactly as before.
    case peek(state) do
      %Token{type: :keyword, value: :in} ->
        state = advance(state)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)
        block = {:block, [line: token.line, col: token.col], [assignment, body]}
        {block, state}

      _ ->
        {assignment, state}
    end
  end

  # -- If / Elif / Else
  #
  # The legacy `if`/`elif` construct has been removed by the v1.0.0
  # branching specs (PICKUP §17, MATCH §10). It is still parsed for
  # source migration purposes but every encounter emits a deprecation
  # event (`Cure.Pipeline.Events`, payload `:if_deprecated`) so editors,
  # the LSP, and `mix cure.rewrite` can surface the migration hint. The
  # spec-mandated diagnostic code `E-IF-REMOVED` is reserved by the
  # error catalogue but not yet emitted as a hard error.

  defp parse_if(state) do
    token = peek(state)
    state = advance(state)
    state = emit_if_deprecation(state, token)

    # Parse condition
    {condition, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: if cond then a else b
    # Block form: if cond <newline> <indent> ... <dedent> [elif ...] [else ...]
    case peek(state) do
      %Token{type: :keyword, value: :then} ->
        state = advance(state)
        {then_branch, state} = parse_expr(state, 0)

        {else_branch, state} =
          case peek(state) do
            %Token{type: :keyword, value: :else} ->
              state = advance(state)
              parse_expr(state, 0)

            _ ->
              {{:literal, [subtype: :null], nil}, state}
          end

        ast = {:conditional, [line: token.line, col: token.col], [condition, then_branch, else_branch]}
        {ast, state}

      _ ->
        # Block form
        {then_branch, state} = parse_block(state)

        state = skip_newlines(state)

        {else_branch, state} =
          case peek(state) do
            %Token{type: :keyword, value: :elif} ->
              # Desugar elif to nested conditional
              parse_if(state)

            %Token{type: :keyword, value: :else} ->
              state = advance(state)
              state = skip_newlines(state)
              parse_block(state)

            _ ->
              {{:literal, [subtype: :null], nil}, state}
          end

        ast = {:conditional, [line: token.line, col: token.col], [condition, then_branch, else_branch]}
        {ast, state}
    end
  end

  # -- Match Expression ------------------------------------------------------

  defp parse_match(state) do
    token = peek(state)
    state = advance(state)

    # Parse scrutinee
    {scrutinee, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: match x { pat -> body, ... }
    # Block form: match x <newline> <indent> arms <dedent>
    case peek(state) do
      %Token{type: :lbrace} ->
        state = advance(state)
        {arms, state} = parse_inline_match_arms(state)
        state = expect(state, :rbrace)
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee | arms]}
        {ast, state}

      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee | arms]}
        {ast, state}

      _ ->
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee]}
        {ast, state}
    end
  end

  # -- With-abstraction (capability A) ---------------------------------------
  #
  # `with <expr>` matches on an intermediate expression and refines the GOAL by
  # the scrutinee's VALUE (not just its type indices) — what plain `match`
  # cannot do. Mirrors `parse_match/1` and reuses its arm parsers, producing a
  # distinct `{:with_abs, meta, [scrut | arms]}` node the dependent elaborator
  # dispatches on. Only capability A (single scrutinee, block/inline form) is
  # parsed; the `proof` clause and multiple with-expressions are out of scope.
  defp parse_with_abs(state, token) do
    state = advance(state)

    {scrutinee, state} = parse_expr(state, 0)
    # Multiple with-scrutinees (Idris `foo a b with (g a) | (g b)`) are written
    # space-separated in Cure surface syntax: `with g(a) g(b)`. Juxtaposition is
    # not application here (`g(a) g(b)` parses as two exprs because `parse_expr`
    # stops at the second callee), so we simply keep pulling scrutinees while the
    # next token can begin one. A single scrutinee leaves `scruts == [scrutinee]`
    # and the legacy path below is taken byte-for-byte unchanged.
    {scruts, state} = collect_with_scrutinees([scrutinee], state)
    # Optional `proof <ident>` (capability B): binds the scrutinee equation
    # `Eq(T, e, pat)` in each branch. `proof` is a soft keyword recognised only
    # in this slot; elsewhere it stays an ordinary identifier.
    {proof, state} = parse_optional_with_proof(state)
    state = skip_newlines(state)

    base_meta = [line: token.line, col: token.col]
    meta = if proof, do: Keyword.put(base_meta, :proof, proof), else: base_meta

    case scruts do
      [single] ->
        case peek(state) do
          %Token{type: :lbrace} ->
            state = advance(state)
            {arms, state} = parse_inline_match_arms(state)
            state = expect(state, :rbrace)
            {{:with_abs, meta, [single | arms]}, state}

          %Token{type: :indent} ->
            state = advance(state)
            {arms, state} = parse_with_block_arms(state)
            state = expect_dedent(state)
            {{:with_abs, meta, [single | arms]}, state}

          _ ->
            {{:with_abs, meta, [single]}, state}
        end

      _ ->
        parse_multi_with_abs(scruts, proof, base_meta, state)
    end
  end

  # Pull the second and subsequent space-separated with-scrutinees. Each call
  # peeks the current token: if it can start an expression we parse one more
  # scrutinee and recurse; otherwise we stop. `proof`/`:newline`/`:indent`/
  # `:lbrace` are not expression starters, so they terminate the scrutinee list.
  defp collect_with_scrutinees(acc, state) do
    if with_scrutinee_start?(peek(state)) do
      {expr, state} = parse_expr(state, 0)
      collect_with_scrutinees(acc ++ [expr], state)
    else
      {acc, state}
    end
  end

  defp with_scrutinee_start?(%Token{type: type})
       when type in [
              :identifier,
              :integer,
              :float,
              :string,
              :bool,
              :atom,
              :char,
              :lparen,
              :lbracket,
              :tuple_open,
              :map_open,
              :binary_open
            ],
       do: true

  defp with_scrutinee_start?(_), do: false

  # Multiple-with surface sugar. `with e1 e2 … eN` with arms
  # `p1, p2, …, pN -> body` desugars to nested single-scrutinee `:with_abs`
  # nodes so the dependent elaborator's existing (single-scrutinee) handling
  # covers it unchanged — this parser produces exactly the `{:with_abs, meta,
  # [scrut | arms]}` shape it already dispatches on. Combining an LHS re-match
  # (`| pat`) or a `proof` binding with multiple scrutinees is out of scope in
  # this first slice and is reported as a clean parse error.
  defp parse_multi_with_abs(scruts, proof, base_meta, state) do
    n = length(scruts)

    {arms, state} =
      case peek(state) do
        %Token{type: :lbrace} ->
          state = advance(state)
          {arms, state} = parse_multi_with_inline_arms(state, n)
          state = expect(state, :rbrace)
          {arms, state}

        %Token{type: :indent} ->
          state = advance(state)
          {arms, state} = parse_multi_with_block_arms(state, n)
          state = expect_dedent(state)
          {arms, state}

        _ ->
          {[], state}
      end

    cond do
      proof != nil ->
        state =
          add_error(
            state,
            {:with_multi_proof_unsupported, "`proof` binding is not supported together with multiple with-scrutinees",
             base_meta}
          )

        {{:with_abs, base_meta, [hd(scruts)]}, state}

      arms == [] ->
        state =
          add_error(
            state,
            {:with_multi_no_arms, "with-abstraction over multiple scrutinees requires at least one arm", base_meta}
          )

        {{:with_abs, base_meta, [hd(scruts)]}, state}

      true ->
        build_multi_with(scruts, arms, base_meta, state)
    end
  end

  # Block-form arms for a multiple-with. Each arm is a list of `n` comma-
  # separated patterns and a body; results are `{patterns, body}` tuples that
  # `build_multi_with/4` later desugars.
  defp parse_multi_with_block_arms(state, n) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_multi_with_arm(state, n)
        state = skip_newlines(state)
        {rest, state} = parse_multi_with_block_arms(state, n)
        {[arm | rest], state}
    end
  end

  # Inline (`{ … }`) form. Arms are separated by `,`; the pattern commas within
  # an arm are consumed by `parse_comma_pattern_list/1`, which stops at the `->`.
  defp parse_multi_with_inline_arms(state, n) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {[], state}

      _ ->
        {arm, state} = parse_multi_with_arm(state, n)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_multi_with_inline_arms(state, n)
            {[arm | rest], state}

          _ ->
            {[arm], state}
        end
    end
  end

  # A single multiple-with arm: `p1, …, pk -> body`. A trailing `| pat` marks the
  # rematch form, which is out of scope combined with multiple-with; a pattern
  # count other than `n` is an arity error. Both are reported but recovery still
  # consumes through the body so parsing continues.
  defp parse_multi_with_arm(state, n) do
    {patterns, state} = parse_comma_pattern_list(state)

    {patterns, state} =
      case peek(state) do
        %Token{type: :bar} ->
          state =
            add_error(
              state,
              {:with_multi_rematch_unsupported,
               "LHS re-match (`| pat`) combined with multiple with-scrutinees is not supported", []}
            )

          # Recover: consume the `| with-pattern` remainder before the body.
          state = advance(state)
          state = skip_newlines(state)
          {_wp, state} = parse_expr(state, 0)
          {patterns, state}

        _ ->
          {patterns, state}
      end

    state =
      if length(patterns) != n do
        add_error(
          state,
          {:with_multi_arity_mismatch, "with-arm has #{length(patterns)} pattern(s) but there are #{n} with-scrutinees",
           []}
        )
      else
        state
      end

    state = skip_newlines(state)
    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)
    {{patterns, body}, state}
  end

  # Comma-separated pattern list for one multiple-with arm. A top-level `,` never
  # occurs inside a single pattern (tuples are parenthesised), so it reliably
  # separates the per-scrutinee patterns; parsing stops at the first non-comma
  # (the `->`, or a `|` handled by the caller).
  defp parse_comma_pattern_list(state) do
    {first, state} = parse_expr(state, 0)
    {first, state} = maybe_wrap_as(first, state)
    parse_comma_pattern_list([first], state)
  end

  defp parse_comma_pattern_list(acc, state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {pat, state} = parse_expr(state, 0)
        {pat, state} = maybe_wrap_as(pat, state)
        parse_comma_pattern_list(acc ++ [pat], state)

      _ ->
        {acc, state}
    end
  end

  # Desugar `n` scrutinees + `{patterns, body}` arms into nested single-scrutinee
  # `:with_abs` nodes. Base case (one scrutinee left): a flat `:with_abs` whose
  # arms are ordinary `{:match_arm, [pattern: p], [body]}`. Recursive case: group
  # arms by their FIRST pattern (structural equality, first-appearance order) and
  # emit one outer `{:match_arm, [pattern: p1], [inner]}` per group, where `inner`
  # is the desugar of the remaining scrutinees over that group's arms with their
  # first pattern stripped.
  defp build_multi_with([last], arms, meta, state) do
    match_arms =
      Enum.map(arms, fn {[p], body} -> {:match_arm, [pattern: p], [body]} end)

    {{:with_abs, meta, [last | match_arms]}, state}
  end

  defp build_multi_with([s | rest], arms, meta, state) do
    groups = group_arms_by_first(arms)
    state = check_group_head_consistency(groups, meta, state)

    {outer_arms, state} =
      Enum.map_reduce(groups, state, fn {p1, sub_arms}, st ->
        {inner, st} = build_multi_with(rest, sub_arms, meta, st)
        {{:match_arm, [pattern: p1], [inner]}, st}
      end)

    {{:with_abs, meta, [s | outer_arms]}, state}
  end

  # Group arms by their first pattern using structural equality that ignores
  # positional metadata (line/col), so e.g. two `S(j)` arms on different lines
  # share one outer branch. Preserves first-appearance order. Each group's
  # sub-arms have the grouped-on first pattern removed.
  defp group_arms_by_first(arms) do
    Enum.reduce(arms, [], fn {[p1 | rest_pats], body}, groups ->
      key = strip_meta(p1)

      case Enum.find_index(groups, fn {gp, _} -> strip_meta(gp) == key end) do
        nil ->
          groups ++ [{p1, [{rest_pats, body}]}]

        idx ->
          {gp, subs} = Enum.at(groups, idx)
          List.replace_at(groups, idx, {gp, subs ++ [{rest_pats, body}]})
      end
    end)
  end

  # First-slice consistency guard. Because groups are keyed by structural
  # equality, two distinct groups sharing one constructor head can only differ in
  # their sub-patterns/variable names — sharing an outer branch would require
  # renaming, which this slice does not do. Reject rather than risk mis-binding.
  defp check_group_head_consistency(groups, meta, state) do
    ctor_heads =
      groups
      |> Enum.map(fn {p1, _} -> pattern_ctor_head(p1) end)
      |> Enum.filter(&match?({:ctor, _}, &1))

    if length(Enum.uniq(ctor_heads)) == length(ctor_heads) do
      state
    else
      add_error(
        state,
        {:with_multi_inconsistent_pattern,
         "multiple-with arms share a constructor head with differing sub-patterns; this first " <>
           "slice requires structurally identical outer patterns (rename to a common form)", meta}
      )
    end
  end

  defp pattern_ctor_head({:function_call, meta, _args}), do: {:ctor, Keyword.get(meta, :name)}
  defp pattern_ctor_head(_), do: :other

  # Structural-equality normaliser for pattern ASTs: drop the metadata slot of
  # every `{tag, meta, payload}` node so patterns compare on constructor head and
  # argument structure (including variable names) only.
  defp strip_meta({tag, meta, payload}) when is_atom(tag) and is_list(meta) do
    {tag, strip_meta(payload)}
  end

  defp strip_meta(list) when is_list(list), do: Enum.map(list, &strip_meta/1)

  defp strip_meta(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&strip_meta/1) |> List.to_tuple()
  end

  defp strip_meta(other), do: other

  # Block-form with-clause arms. Distinct from `parse_block_match_arms` (used by
  # plain `match`) because a with-clause arm may RESTATE the parent LHS patterns
  # before the with-pattern — the Idris-parity LHS re-match form. Each arm is
  # either the ordinary `{:match_arm, …}` (no `… |` prefix) or the new
  # `{:with_rematch_arm, …}` (parent patterns `|` with-pattern).
  defp parse_with_block_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_with_clause_arm(state)
        state = skip_newlines(state)
        {rest, state} = parse_with_block_arms(state)
        {[arm | rest], state}
    end
  end

  # A single with-clause arm. Parse the first pattern, then disambiguate by the
  # following token (only in this with-clause-LHS position):
  #   - `|`      → rematch arm restating one parent pattern
  #   - `,` … `|`→ rematch arm restating several (comma-separated) parent patterns
  #   - anything → ordinary `{:match_arm}` (the existing no-rematch form)
  # A top-level `,` before `->` never occurs in a plain arm pattern (tuples are
  # parenthesised), so it unambiguously signals a multi-pattern rematch here.
  defp parse_with_clause_arm(state) do
    {first, state} = parse_expr(state, 0)

    case peek(state) do
      %Token{type: :bar} ->
        finish_with_rematch_arm([first], state)

      %Token{type: :comma} ->
        {parent_patterns, state} = parse_more_parent_patterns([first], state)
        finish_with_rematch_arm(parent_patterns, state)

      _ ->
        parse_match_arm_tail(first, state)
    end
  end

  # Collect the remaining comma-separated parent patterns (the first is already
  # parsed). Stops at the `|` separator (consumed by `finish_with_rematch_arm`).
  defp parse_more_parent_patterns(acc, state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {pat, state} = parse_expr(state, 0)
        parse_more_parent_patterns(acc ++ [pat], state)

      _ ->
        {acc, state}
    end
  end

  # After the parent patterns: consume `|`, parse the with-pattern, then the
  # `->` body. Guards and `impossible` in rematch arms are deferred (out of the
  # faithful first slice). Produces `{:with_rematch_arm, meta, [body]}` with the
  # restated `:parent_patterns` and the with-`:pattern` in meta.
  defp finish_with_rematch_arm(parent_patterns, state) do
    state = expect(state, :bar)
    state = skip_newlines(state)
    {with_pattern, state} = parse_expr(state, 0)
    state = skip_newlines(state)
    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    meta = [parent_patterns: parent_patterns, pattern: with_pattern]
    {{:with_rematch_arm, meta, [body]}, state}
  end

  # `proof <ident>` after a with-scrutinee. Returns `{name, state}` (name a
  # string) when present, else `{nil, state}` leaving the stream untouched.
  defp parse_optional_with_proof(state) do
    case peek(state) do
      %Token{type: :keyword, value: :proof} ->
        case peek_at(state, 1) do
          %Token{type: :identifier, value: name} ->
            {name, state |> advance() |> advance()}

          _ ->
            {nil, state}
        end

      _ ->
        {nil, state}
    end
  end

  # True iff the token after `with` can begin a scrutinee expression. Keeps
  # `with` an ordinary identifier when it is a bare operand (`with + 1`, a
  # trailing `with`, etc.), so the contextual keyword never captures a value
  # named `with`.
  defp with_scrutinee_ahead?(state) do
    case peek_at(state, 1) do
      %Token{type: type}
      when type in [
             :identifier,
             :integer,
             :float,
             :string,
             :bool,
             :atom,
             :char,
             :lparen,
             :lbracket,
             :tuple_open,
             :map_open,
             :binary_open
           ] ->
        true

      _ ->
        false
    end
  end

  defp parse_inline_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_inline_match_arms(state)
            {[arm | rest], state}

          _ ->
            {[arm], state}
        end
    end
  end

  defp parse_block_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)
        {rest, state} = parse_block_match_arms(state)
        {[arm | rest], state}
    end
  end

  defp parse_match_arm(state) do
    # Parse pattern
    {pattern, state} = parse_expr(state, 0)
    {pattern, state} = maybe_wrap_as(pattern, state)
    parse_match_arm_tail(pattern, state)
  end

  # As-pattern: `name @ <pattern>` binds the whole matched value to `name` in
  # addition to destructuring it. `@` (`:at`) is a decorator prefix only at
  # declaration position, so in value/pattern position it is unambiguously an
  # as-binding. Used both at a match arm's top level and inside constructor
  # arguments (`Cons(h, t @ Cons(x, y))`), so as-patterns nest.
  defp maybe_wrap_as({:variable, vm, name}, state) do
    case peek(state) do
      %Token{type: :at} ->
        state = advance(state)
        {inner, state} = parse_expr(state, 0)
        {inner, state} = maybe_wrap_as(inner, state)
        {{:as_pattern, vm, [name, inner]}, state}

      _ ->
        {{:variable, vm, name}, state}
    end
  end

  defp maybe_wrap_as(pattern, state), do: {pattern, state}

  # The tail of a match arm after its pattern has been parsed: optional `when`
  # guard, the `->`, and the body (or `impossible`). Factored out so with-clause
  # arms can fall through to it once they have decided they are NOT a rematch arm
  # (see `parse_with_clause_arm`).
  defp parse_match_arm_tail(pattern, state) do
    state = skip_newlines(state)

    # Optional guard: when expr
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    # Expect ->
    state = expect(state, :arrow)
    state = skip_newlines(state)

    # `impossible` is a soft keyword recognized only as an entire arm body
    # (spec §4): `pat -> impossible`. Any other use stays an ordinary identifier.
    if impossible_body?(state) do
      state = advance(state)

      meta =
        if guard, do: [pattern: pattern, guard: guard, impossible: true], else: [pattern: pattern, impossible: true]

      {{:match_arm, meta, [nil]}, state}
    else
      {body, state} = parse_expr_or_block(state)
      meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]
      {{:match_arm, meta, [body]}, state}
    end
  end

  # True iff the next token is the identifier `impossible` AND the token after it
  # ends the arm — so `impossible` alone is the body, but `impossible + 1` is not.
  defp impossible_body?(state) do
    case peek(state) do
      %Token{type: :identifier, value: "impossible"} ->
        case peek_at(state, 1) do
          %Token{type: type} when type in [:newline, :comma, :rbrace, :dedent, :eof] -> true
          nil -> true
          _ -> false
        end

      _ ->
        false
    end
  end

  # -- Pickup Expression -----------------------------------------------------
  #
  # `pickup` is the predicate-dispatch counterpart to `match` (see
  # `docs/PICKUP.md`). Grammar (PICKUP §4):
  #
  #   pickup_expr     ::= "pickup" NEWLINE INDENT clause_list DEDENT
  #   clause_list     ::= guard_clause { NEWLINE guard_clause } NEWLINE
  #                       terminal_clause [ NEWLINE ]
  #                     | terminal_clause [ NEWLINE ]
  #   guard_clause    ::= expression "->" expression
  #   terminal_clause ::= "else" "->" expression
  #                     | "true" "->" expression
  #
  # The AST shape is `{:pickup, meta, clauses}` where each clause is
  # either `{:pickup_clause, meta, [guard, body]}` (a guard clause) or
  # `{:pickup_else, meta, [body]}` (the mandatory terminator). The parser
  # itself enforces the well-formedness rules of PICKUP §5.2 and §4.1
  # (non-empty block, single terminator, terminator-last) so downstream
  # stages can rely on the structural shape; spec-mandated diagnostic
  # codes are surfaced with the same `add_error/2` channel the rest of
  # the parser uses.

  defp parse_pickup(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {clauses, state} = parse_pickup_clauses(state)
          state = expect_dedent(state)
          {clauses, state}

        _ ->
          # Inline form is not part of the spec, but we accept a
          # single-line `pickup else -> expr` so REPL one-liners still
          # parse. The well-formedness pass below will still catch a
          # missing terminator. `parse_pickup_inline/1` already wraps
          # the single clause in a list so the calling shape matches
          # the indented case below.
          parse_pickup_inline(state)
      end

    state = validate_pickup_clauses(clauses, token, state)

    meta = [line: token.line, col: token.col]
    {{:pickup, meta, clauses}, state}
  end

  defp parse_pickup_inline(state) do
    {clause, state} = parse_pickup_clause(state)
    {[clause], state}
  end

  defp parse_pickup_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {clause, state} = parse_pickup_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_pickup_clauses(state)
        {[clause | rest], state}
    end
  end

  defp parse_pickup_clause(state) do
    case peek(state) do
      %Token{type: :keyword, value: :else} = tok ->
        state = advance(state)
        state = expect(state, :arrow)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)
        meta = [line: tok.line, col: tok.col]
        {{:pickup_else, meta, [body]}, state}

      tok ->
        {guard, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        state = expect(state, :arrow)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)
        meta = [line: tok.line, col: tok.col]
        {{:pickup_clause, meta, [guard, body]}, state}
    end
  end

  # PICKUP §5.2 / §4.1 enforcement. The four well-formedness errors
  # carried here (E-PICKUP-NO-ELSE, E-PICKUP-ELSE-NOT-LAST,
  # E-PICKUP-MULTIPLE-ELSE, and the empty-body case) are raised at the
  # parser tier so a malformed `pickup` never leaks into the type checker
  # or codegen.
  defp validate_pickup_clauses([], token, state) do
    add_error(
      state,
      {:pickup_no_else,
       "pickup block must contain at least one clause and a terminating `else ->` arm (E-PICKUP-NO-ELSE)",
       [line: token.line, col: token.col]}
    )
  end

  defp validate_pickup_clauses(clauses, token, state) do
    {else_count, _last_else?, has_terminator?, after_terminator?} =
      clauses
      |> Enum.with_index()
      |> Enum.reduce({0, false, false, false}, fn {clause, idx}, {ec, last_e, term, after_t} ->
        is_last = idx == length(clauses) - 1
        terminator? = pickup_terminator?(clause, is_last)

        ec = if pickup_else?(clause), do: ec + 1, else: ec
        last_e = if pickup_else?(clause), do: is_last, else: last_e

        # Anything after a real terminator clause counts as `after_t`
        # for the diagnostic below, mirroring PICKUP §4.1.
        term = term or terminator?
        after_t = after_t or (term and not terminator?)

        {ec, last_e, term, after_t}
      end)

    state =
      cond do
        else_count > 1 ->
          add_error(
            state,
            {:pickup_multiple_else, "pickup block has more than one `else ->` arm (E-PICKUP-MULTIPLE-ELSE)",
             [line: token.line, col: token.col]}
          )

        after_terminator? ->
          add_error(
            state,
            {:pickup_else_not_last, "pickup `else ->` must be the final clause (E-PICKUP-ELSE-NOT-LAST)",
             [line: token.line, col: token.col]}
          )

        not has_terminator? ->
          add_error(
            state,
            {:pickup_no_else, "pickup block must end in `else -> ...` (or trailing `true -> ...`) (E-PICKUP-NO-ELSE)",
             [line: token.line, col: token.col]}
          )

        true ->
          state
      end

    state
  end

  defp pickup_else?({:pickup_else, _, _}), do: true
  defp pickup_else?(_), do: false

  defp pickup_terminator?({:pickup_else, _, _}, _is_last), do: true

  defp pickup_terminator?({:pickup_clause, _meta, [guard, _body]}, true) do
    # Trailing `true ->` is the alternative form admitted by PICKUP §5.2.
    case guard do
      {:literal, _, true} -> true
      _ -> false
    end
  end

  defp pickup_terminator?(_, _), do: false

  # -- fn: named function or lambda ------------------------------------------

  defp parse_fn_or_lambda(state) do
    token = peek(state)
    state = advance(state)

    # fn followed by ( -> lambda
    # fn followed by identifier or (soft) keyword -> named function definition
    #
    # Some Cure keywords (spawn, send, receive, after) are ordinary
    # function names in other languages, and `Std.Fsm` defines e.g.
    # `fn spawn(fsm_module: Atom) -> Pid`. Let those keywords double as
    # function-definition names; they still behave as keywords in
    # statement position.
    case peek(state) do
      %Token{type: :lparen} ->
        parse_lambda_body(state, token)

      %Token{type: :identifier} ->
        parse_fn_def(state, token, :public)

      %Token{type: :keyword} ->
        parse_fn_def(state, token, :public)

      _ ->
        parse_lambda_body(state, token)
    end
  end

  # local fn name(...) -> private function
  defp parse_local(state) do
    token = peek(state)
    state = advance(state)

    # Expect fn keyword next
    case peek(state) do
      %Token{type: :keyword, value: :fn} ->
        state = advance(state)
        # After `local fn`, a name (identifier or soft keyword) must follow.
        case peek(state) do
          %Token{type: type} when type in [:identifier, :keyword] ->
            parse_fn_def(state, token, :private)

          _ ->
            parse_lambda_body(state, token)
        end

      _ ->
        error = {:expected, :fn, :got, peek(state).type, token.line, token.col}
        state = add_error(state, error)
        {error_node(token), state}
    end
  end

  # -- Named Function Definition ---------------------------------------------

  defp parse_fn_def(state, fn_token, visibility) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Parse parameter list
    state = expect(state, :lparen)
    {params, state} = parse_typed_params(state)
    state = expect(state, :rparen)

    # Optional return type: -> Type
    {return_type, state} =
      case peek(state) do
        %Token{type: :arrow} ->
          state = advance(state)
          parse_type_expr(state)

        _ ->
          {nil, state}
      end

    # Optional effect annotation: ! Effect, Effect2
    {effects, state} =
      case peek(state) do
        %Token{type: :bang} ->
          state = advance(state)
          parse_effect_list(state)

        _ ->
          {nil, state}
      end

    # Optional guard: when expr
    # Parse at BP 6 to stop before `=` (BP 5) so the guard doesn't consume the body
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 6)
          {g, state}

        _ ->
          {nil, state}
      end

    # Optional constraints: where Proto(T), ...
    {constraints, state} =
      case peek(state) do
        %Token{type: :keyword, value: :where} ->
          state = advance(state)
          parse_constraint_list(state)

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Check for multi-clause form (indented | patterns) or = body
    case peek(state) do
      %Token{type: :assign} ->
        state = advance(state)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)
        {body, state} = parse_expression_let_chain_body(body, state)

        meta = build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)
        ast = {:function_def, meta, [body]}
        {ast, state}

      %Token{type: :indent} ->
        state = advance(state)

        case peek(skip_newlines(state)) do
          %Token{type: :assign} ->
            state = skip_newlines(state)
            state = advance(state)
            state = skip_newlines(state)
            {body, state} = parse_expr_or_block(state)
            {body, state} = parse_expression_let_chain_body(body, state)
            state = expect_dedent(state)

            meta =
              build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)

            ast = {:function_def, meta, [body]}
            {ast, state}

          _ ->
            # Could be multi-clause: indented | pattern -> body lines
            {clauses, state} = parse_fn_clauses(state)
            state = expect_dedent(state)

            meta =
              build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)

            meta = Keyword.put(meta, :clauses, clauses)
            ast = {:function_def, meta, []}
            {ast, state}
        end

      _ ->
        # Function signature only (no body, e.g. in protocol)
        meta = build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)
        ast = {:function_def, meta, []}
        {ast, state}
    end
  end

  defp build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects) do
    meta = [
      name: name,
      params: params,
      visibility: visibility,
      arity: length(params),
      line: fn_token.line,
      col: fn_token.col
    ]

    meta = if return_type, do: Keyword.put(meta, :return_type, return_type), else: meta
    meta = if guard, do: Keyword.put(meta, :guards, guard), else: meta
    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    meta = if effects, do: Keyword.put(meta, :effects, effects), else: meta
    meta
  end

  defp parse_fn_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      %Token{type: :bar} ->
        state = advance(state)
        {clause, state} = parse_single_fn_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_fn_clauses(state)
        {[clause | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_single_fn_clause(state) do
    # Parse pattern(s) until -> or when
    {patterns, state} = parse_clause_patterns(state, [])

    # Optional guard
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    clause = %{params: patterns, guard: guard, body: [body]}
    {clause, state}
  end

  defp parse_clause_patterns(state, acc) do
    case peek(state) do
      %Token{type: :arrow} ->
        {Enum.reverse(acc), state}

      %Token{type: :keyword, value: :when} ->
        {Enum.reverse(acc), state}

      _ ->
        {pat, state} = parse_expr(state, 42)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            parse_clause_patterns(state, [pat | acc])

          _ ->
            {Enum.reverse([pat | acc]), state}
        end
    end
  end

  # -- Typed Parameters  name: Type [= default] ------------------------------

  defp parse_typed_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} -> {[], state}
      _ -> parse_typed_params_list(state)
    end
  end

  defp parse_typed_params_list(state) do
    {param, state} = parse_single_typed_param(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_typed_params_list(state)
        {[param | rest], state}

      _ ->
        {[param], state}
    end
  end

  defp parse_single_typed_param(state) do
    case peek(state) do
      %Token{type: :lbrace} -> parse_implicit_param(state)
      _ -> parse_explicit_param(state)
    end
  end

  # QTT grades (plan slice 5). A grade REPLACES the binder's colon and sits at the
  # binding site: `c :linear Chan(Cmd)`, `{n :erased Nat}`. An absent grade means
  # `ω`, so every existing program is unchanged.
  #
  # The grade belongs to the ARROW, not to the name and not to the type: Core spells
  # it `{:pi, g, dom, cod}` and `Conv` compares `g` as part of the Pi while `dom` is
  # an ordinary type. `linear c` would decorate the name; `c: linear T` would claim
  # `linear T` is a type, and Core has no modality former.
  #
  # Idris spells quantities as bare numerals (`Idris/Parser.idr:647-653`) and Cure
  # cannot: `fn f(x: 1)` already parses with `1` as a literal type, and `?` is
  # already the hole token, so neither `:1` nor `1?` is free. Idris has no affine
  # grade to port a spelling from anyway. These atoms already lex as single tokens,
  # are unambiguous after a binder name, and — being atoms, not keywords — steal no
  # identifiers.
  #
  # `:unrestricted` is deliberately NOT a spelling: `ω` is written by omission, so
  # each grade has exactly ONE surface form.
  @grade_atoms [:erased, :linear, :affine]

  # After a binder NAME, an ATOM token is unambiguously a grade slot — a type
  # annotation needs a colon first (`x: :ok`), whereas the grade's fused `:name`
  # form lexes as one atom. So `:erased/:linear/:affine` → that grade; any OTHER
  # atom (`:bogus`, or `:unrestricted`, which has no spelling) → a NAMED
  # `{:unknown_grade, …}` rather than a silent no-op that desyncs the param list.
  defp parse_grade(state) do
    case peek(state) do
      %Token{type: :atom, value: g} when g in @grade_atoms ->
        {:grade, g, advance(state)}

      %Token{type: :atom, value: bad} = tok ->
        {:unknown, bad, tok, advance(state)}

      _ ->
        {:none, state}
    end
  end

  # Tokens that cannot begin a type — after a grade, one of these means the required
  # type is missing, so name THAT rather than let `parse_type_expr` swallow the token.
  @non_type_tokens [:rparen, :rbrace, :rbracket, :comma, :assign, :newline, :indent, :dedent, :eof]

  # A binder's annotation: `: Type`, or the graded `:g Type`. `name` labels the binder
  # for diagnostics.
  #
  # `stop_on` names the tokens that may legally FOLLOW a grade in place of a type. A
  # parameter has none, so `c :linear` is an error — there is nothing to grade. A
  # `let` stops on `=`, because Idris's `letBinder` leaves the type optional even when
  # graded (`Idris/Parser.idr:821-824`) and `let_inferred/8` will synthesise it.
  defp parse_binder_annotation(state, name, stop_on \\ []) do
    case parse_grade(state) do
      {:none, state} ->
        case peek(state) do
          %Token{type: :colon} ->
            {type_ast, state} = parse_type_expr(advance(state))
            {nil, type_ast, state}

          _ ->
            {nil, nil, state}
        end

      {:unknown, bad, tok, state} ->
        # Consume the stray atom (already advanced past it) and name it, so the error
        # points at the grade rather than cascading onto the next real token.
        {nil, nil, add_error(state, {:unknown_grade, bad, tok.line, tok.col})}

      {:grade, grade, state} ->
        cond do
          peek(state).type in stop_on ->
            {grade, nil, state}

          peek(state).type in @non_type_tokens ->
            tok = peek(state)
            {grade, nil, add_error(state, {:grade_requires_type, name, grade, tok.line, tok.col})}

          true ->
            {type_ast, state} = parse_type_expr(state)
            {grade, type_ast, state}
        end
    end
  end

  defp put_binder_meta(meta, grade, type_ast) do
    meta = if type_ast, do: Keyword.put(meta, :type, type_ast), else: meta
    if grade, do: Keyword.put(meta, :grade, grade), else: meta
  end

  # `{name}` or `{name: Type}` — an implicit, erased argument (design spec §6).
  # Its type may be omitted and inferred by the elaborator from later parameter
  # types / the return type. `{name :g Type}` overrides the erased default.
  defp parse_implicit_param(state) do
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {grade, type_ast, state} = parse_binder_annotation(state, name)

    state = expect(state, :rbrace)

    {{:param, put_binder_meta([implicit: true], grade, type_ast), name}, state}
  end

  defp parse_explicit_param(state) do
    # Check for variadic: *name or **name
    {kind, state} =
      case peek(state) do
        %Token{type: :star} ->
          next = peek_at(state, 1)

          if next && next.type == :star do
            {_, state} = {nil, advance(state) |> advance()}
            {:keyword_variadic, state}
          else
            {_, state} = {nil, advance(state)}
            {:variadic, state}
          end

        _ ->
          {:positional, state}
      end

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type annotation `: Type`, or a graded one `:g Type`.
    {grade, type_ast, state} = parse_binder_annotation(state, name)

    # Optional default value: = expr
    {default, state} =
      case peek(state) do
        %Token{type: :assign} ->
          state = advance(state)
          state = skip_newlines(state)
          {d, state} = parse_expr(state, 6)
          {d, state}

        _ ->
          {nil, state}
      end

    param_meta = put_binder_meta([], grade, type_ast)
    param_meta = if default, do: Keyword.put(param_meta, :default, default), else: param_meta
    param_meta = if kind != :positional, do: Keyword.put(param_meta, :kind, kind), else: param_meta

    {{:param, param_meta, name}, state}
  end

  # -- Lambda (anonymous fn) -------------------------------------------------
  #
  # v0.22.0 introduces two new multi-statement body shapes in addition
  # to the historical indented-block and single-expression forms:
  #
  #   fn (x) -> { stmt1; stmt2; final }     (brace-delimited)
  #   fn (x) ->
  #     stmt1
  #     stmt2
  #   end                                   (end-terminated)
  #
  # Both compile to the same `{:block, meta, exprs}` AST node that the
  # v0.19.0 indented form already produces; the only user-visible
  # difference is that these two forms work inside argument lists,
  # where the lexer suppresses newlines and `:indent`/`:dedent` are
  # never emitted.
  defp parse_lambda_body(state, token) do
    state = expect(state, :lparen)
    {params, state} = parse_lambda_params(state)
    state = expect(state, :rparen)
    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_lambda_block_body(state, token)

    param_nodes = Enum.map(params, fn name -> {:param, [], name} end)
    ast = {:lambda, [params: param_nodes, line: token.line, col: token.col], [body]}
    {ast, state}
  end

  # Route the lambda body to one of four shapes: indented block, brace
  # block, end-terminated block, or single expression. The brace and end
  # forms emit a `{:block, [block_shape: :brace | :end, ...], exprs}`
  # node so the Printer and AlgebraFormatter can round-trip the
  # author's chosen shape.
  defp parse_lambda_block_body(state, token) do
    case peek(state) do
      %Token{type: :indent} ->
        parse_indented_lambda_body(state, token)

      %Token{type: :lbrace} ->
        parse_brace_lambda_body(state, token)

      _ ->
        parse_bare_lambda_body(state, token)
    end
  end

  # Indented block, optionally followed by an `end` terminator:
  #
  #   fn (x) ->
  #     stmt1
  #     stmt2
  #   end
  #
  # The `end` is optional; when present the block shape is tagged so
  # the formatter can keep it. Without `end` the block reverts to the
  # v0.19.0 indented form.
  defp parse_indented_lambda_body(state, token) do
    {body, state} = parse_block(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {tag_block_shape(body, :end, token), state}

      _ ->
        {body, state}
    end
  end

  # Brace block `{ stmt1; stmt2; final }`. Statement separator is `;`,
  # with newlines accepted as a synonym when the brace body happens to
  # live outside a paren scope. Empty braces compile to `:ok`.
  defp parse_brace_lambda_body(state, token) do
    state = expect(state, :lbrace)
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        state = advance(state)
        {{:literal, [subtype: :null, line: token.line, col: token.col], nil}, state}

      _ ->
        {exprs, state} = parse_brace_block_body(state, [])
        state = expect(state, :rbrace)
        {build_block(exprs, :brace, token), state}
    end
  end

  # Bare (no leading `{` or `:indent`) body. When the first expression
  # is followed by a statement separator *and* an `end` keyword
  # eventually appears, treat the sequence as an end-terminated block;
  # otherwise parse a single expression as the lambda body.
  defp parse_bare_lambda_body(state, token) do
    saved_pos = state.pos
    {first, state} = parse_expr(state, 0)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {build_block([first], :end, token), state}

      %Token{type: :semicolon} ->
        state = %{state | pos: saved_pos}
        parse_end_terminated_lambda_body(state, token)

      _ ->
        {first, state}
    end
  end

  # `fn (x) -> stmt1; stmt2; ... end` -- explicit `end` terminator, with
  # `;` (and when available, newlines) as the statement separator.
  defp parse_end_terminated_lambda_body(state, token) do
    {exprs, state} = parse_brace_block_body(state, [])
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {build_block(exprs, :end, token), state}

      other ->
        line = if is_nil(other), do: token.line, else: other.line
        col = if is_nil(other), do: token.col, else: other.col
        error = {:lambda_block_unterminated, line, col, "E035"}
        state = add_error(state, error)
        {build_block(exprs, :end, token), state}
    end
  end

  # Parse a sequence of statements separated by `;` or newlines. Stops
  # when the next token is `:rbrace`, `:keyword :end`, or `:eof`.
  defp parse_brace_block_body(state, acc) do
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: type} when type in [:rbrace, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :keyword, value: :end} ->
        {Enum.reverse(acc), state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_stmt_seps(state)
        parse_brace_block_body(state, [expr | acc])
    end
  end

  defp skip_stmt_seps(state) do
    case peek(state) do
      %Token{type: :semicolon} -> skip_stmt_seps(advance(state))
      %Token{type: :newline} -> skip_stmt_seps(advance(state))
      _ -> state
    end
  end

  defp build_block(exprs, shape, token) do
    case exprs do
      [] -> {:literal, [subtype: :null, line: token.line, col: token.col], nil}
      [single] -> single
      many -> {:block, [block_shape: shape, line: token.line, col: token.col], many}
    end
  end

  defp tag_block_shape({:block, meta, exprs}, shape, _token) when is_list(meta) do
    {:block, Keyword.put(meta, :block_shape, shape), exprs}
  end

  defp tag_block_shape(expr, shape, token) do
    {:block, [block_shape: shape, line: token.line, col: token.col], [expr]}
  end

  defp parse_lambda_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        name = peek(state).value
        state = advance(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_lambda_params(state)
            {[to_string(name) | rest], state}

          _ ->
            {[to_string(name)], state}
        end
    end
  end

  # -- Module  mod Name.Path -------------------------------------------------

  defp parse_module(state) do
    token = peek(state)
    state = advance(state)

    # Parse module name (dotted path)
    {name, state} = parse_dotted_name(state)
    state = skip_newlines(state)

    # Parse indented body. Leading `##` docs immediately after `mod Name`
    # describe the *module* itself, not the first definition inside the
    # body, so pull them back onto the container's `:doc` meta.
    {body_stmts, leading_doc, state} = parse_definition_block_with_lead_doc(state)

    meta = [container_type: :module, name: name, language: :cure, line: token.line, col: token.col]
    meta = if leading_doc != "", do: Keyword.put(meta, :doc, leading_doc), else: meta
    ast = {:container, meta, body_stmts}
    {ast, state}
  end

  # -- Proof container  proof Name.Path (v0.19.0) ----------------------------
  #
  # Mirrors `parse_module/1` but emits `container_type: :proof`. Every
  # binding inside a proof container is expected to elaborate to an
  # `Eq(T, a, b)` proof; the type checker reports mismatches under code `E026`.
  defp parse_proof_container(state) do
    token = peek(state)
    state = advance(state)

    {name, state} = parse_dotted_name(state)
    state = skip_newlines(state)
    {body_stmts, state} = parse_definition_block(state)

    meta = [
      container_type: :proof,
      name: name,
      language: :cure,
      line: token.line,
      col: token.col
    ]

    {{:container, meta, body_stmts}, state}
  end

  # -- Record  rec Name [(TypeParams)] ---------------------------------------

  defp parse_record(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type params: (A, B)
    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Parse indented fields: name: Type
    {fields, state} = parse_record_fields(state)

    meta = [container_type: :struct, name: name, line: token.line, col: token.col]
    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
    ast = {:container, meta, fields}
    {ast, state}
  end

  defp parse_record_fields(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {fields, state} = parse_record_field_list(state)
        state = expect_dedent(state)
        {fields, state}

      _ ->
        {[], state}
    end
  end

  defp parse_record_field_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        name_token = peek(state)
        state = advance(state)
        state = expect(state, :colon)
        {type_ast, state} = parse_type_expr(state)

        # v0.19.0: optional `= default_expr` per record field.
        {default_ast, state} =
          case peek(state) do
            %Token{type: :assign} ->
              state = advance(state)
              state = skip_newlines(state)
              parse_expr(state, 0)

            _ ->
              {nil, state}
          end

        state = skip_newlines(state)

        meta = [type: type_ast]
        meta = if default_ast, do: Keyword.put(meta, :default, default_ast), else: meta

        field = {:param, meta, to_string(name_token.value)}
        {rest, state} = parse_record_field_list(state)
        {[field | rest], state}
    end
  end

  # -- Type  type Name[(Params)] = ... ---------------------------------------
  #
  # v0.21.0: the RHS of a `type` declaration may span multiple lines with
  # the canonical ADT `|` separator on continuation lines, and accept an
  # optional leading `|` before the first variant:
  #
  #     type Shape =
  #       | Circle(Int)
  #       | Square(Int)
  #       | Triangle(Int, Int, Int)
  #
  #     type Shape =
  #       Circle(Int)
  #       | Square(Int)
  #
  # Both are equivalent to the single-line form `type Shape = Circle(Int) | Square(Int)`.
  # The lexer emits a single `:indent`/`:dedent` pair around the continuation
  # block; `parse_type_def/1` absorbs it so the variants themselves can be
  # parsed by the existing `parse_type_variant/1` / `parse_more_variants/1`.

  # `typealias NAME(type_params?) = RHS` — a TRANSPARENT type synonym. Unlike
  # `type NAME = Ctor(...)` (a nominal single-constructor ADT), the RHS is always
  # parsed as a type EXPRESSION and the result is a `:type_annotation` node, which
  # the elaborator lowers to a nullary def whose δ-unfolding makes `NAME`
  # definitionally interchangeable with `RHS`. This disambiguates the applied-type
  # synonym `typealias Char = Bounded(1114112)` from the identically-shaped
  # single-variant ADT `type Color = RGB(Int)`, without disturbing the ADT path.
  defp parse_typealias(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_typed_params(state)
          state = expect(state, :rparen)
          {Enum.map(tp, fn {:param, _meta, n} -> n end), state}

        _ ->
          {[], state}
      end

    state = expect(state, :assign)
    state = skip_newlines(state)
    {rhs, state} = parse_type_expr(state)

    meta = [name: name, line: token.line, col: token.col]
    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
    {{:type_annotation, meta, [rhs]}, state}
  end

  # `primitive Name` → a constructor-less primitive-type container. The optional
  # `@builtin(:tag)` decorator is threaded on by `attach_decorator/3` when the
  # form is written `@builtin(:tag) primitive Name`.
  defp parse_primitive_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = skip_newlines(state)

    meta = [
      container_type: :primitive,
      name: name,
      language: :cure,
      line: token.line,
      col: token.col
    ]

    {{:container, meta, []}, state}
  end

  defp parse_type_def(state, opts \\ []) do
    opaque? = Keyword.get(opts, :opaque, false)
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional head params, parsed permissively (typed `a: Type` or bare `a`).
    # The ordinary-ADT path projects out just the names; the indexed-family path
    # (`type NAME(params) indices (idx)`) keeps the full typed telescope.
    {head_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_typed_params(state)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    cond do
      # `opaque type Name(params)` — no `= …` body, no indices, no ctors. The
      # head params become the family's uniform parameters; the empty variant
      # list plus the `:opaque` container tag drive the non-eliminable marker.
      opaque? ->
        type_params = Enum.map(head_params, fn {:param, _meta, n} -> n end)
        meta = [container_type: :opaque, name: name, line: token.line, col: token.col]
        meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
        {{:container, meta, []}, state}

      match?(%Token{type: :keyword, value: :indices}, peek(state)) ->
        parse_indexed_family(state, name, head_params, token)

      true ->
        type_params = Enum.map(head_params, fn {:param, _meta, n} -> n end)
        parse_type_def_adt(state, name, type_params, token)
    end
  end

  # Indexed (GADT) family: `type NAME(params) indices (idx)` followed by an
  # indentation-delimited block of constructor signatures. Head-paren args are
  # parameters (uniform, never matched); the `indices (…)` clause are indices.
  defp parse_indexed_family(state, name, params, token) do
    state = advance(state)
    state = expect(state, :lparen)
    {idx_tele, state} = parse_typed_params(state)
    state = expect(state, :rparen)
    state = skip_newlines(state)

    {opened_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    {ctors, state} = parse_gadt_ctors(state, [])

    state =
      if opened_block do
        state |> skip_newlines() |> expect_dedent()
      else
        state
      end

    meta = [name: name, params: params, indices: idx_tele, line: token.line, col: token.col]
    {{:indexed_type, meta, ctors}, state}
  end

  # Ordinary ADT / alias body: `type NAME(type_params) = …`.
  defp parse_type_def_adt(state, name, type_params, token) do
    state = skip_newlines(state)

    {pre_assign_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    state = expect(state, :assign)
    state = skip_newlines(state)

    # v0.21.0: allow the RHS to live inside an indented block so the
    # multi-line ADT layout parses. Track whether we entered a block so
    # we can consume the matching `:dedent` on exit.
    {opened_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    state = skip_newlines(state)

    {ast, state} =
      case {peek(state), peek_at(state, 1)} do
        {%Token{type: :lparen}, %Token{type: :rparen}} ->
          # `type Unit = ()` — the Swift-style unit type: `Unit` is the type, `()`
          # its sole value. `= ()` is RESERVED to `Unit`; `()` names the one
          # built-in unit type and is not a spelling other types may borrow, so
          # any other name declared as `()` is a hard error. When permitted, this
          # builds exactly the nullary single-`unit`-ctor family the compiler
          # seeds into every module (see program.ex seed_with_telescope_support/1).
          state = advance(advance(state))

          meta = [container_type: :enum, name: name, line: token.line, col: token.col]
          meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta

          if name == "Unit" do
            {{:container, meta, [{:variable, [variant: true], "unit"}]}, state}
          else
            state = add_error(state, {:unit_type_reserved, name})
            {{:container, meta, []}, state}
          end

        {%Token{type: :lparen}, _} ->
          # A function-type (or grouped/tuple) alias RHS: `type Endo = (Nat) -> Nat`.
          # The full type-expression parser handles the arrow; the result is a plain
          # type alias (`:type_annotation`).
          {rhs, state} = parse_type_expr(state)
          meta = [name: name, line: token.line, col: token.col]
          meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
          {{:type_annotation, meta, [rhs]}, state}

        _ ->
          # v0.21.0: accept an optional leading `|` before the first variant.
          {had_leading_bar, state} =
            case peek(state) do
              %Token{type: :bar} ->
                s = advance(state)
                {true, skip_newlines(s)}

              _ ->
                {false, state}
            end

          # `type Empty = |` declares an explicit CONSTRUCTOR-LESS (uninhabited)
          # type. After the leading bar, end-of-declaration — a dedent/eof or the
          # keyword/decorator that starts the next sibling declaration — means there
          # are no variants at all. The leading bar is required so a bare
          # `type Foo =` (a genuinely missing RHS) still errors rather than silently
          # becoming an empty type.
          if had_leading_bar and no_more_variants?(state) do
            meta = [container_type: :enum, name: name, line: token.line, col: token.col]
            meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
            {{:container, meta, []}, state}
          else
            # Parse as ADT variants (A(T) | B | C) or type alias
            {first_variant, state} = parse_type_variant(state)
            state = skip_newlines(state)

            case peek(state) do
              %Token{type: :bar} ->
                # ADT: multiple variants separated by |
                {rest_variants, state} = parse_more_variants(state)
                variants = [first_variant | rest_variants]
                meta = [container_type: :enum, name: name, line: token.line, col: token.col]
                meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                {{:container, meta, variants}, state}

              _ ->
                if variant_ctor?(first_variant) do
                  # Single-constructor ADT: `type Box = MkBox(Nat)` is a one-ctor
                  # inductive family, not a type alias. (A constructor variant carries
                  # `variant: true`; a genuine alias RHS — `type Celsius = Int` — is a
                  # plain type expression and stays a `:type_annotation`.)
                  meta = [container_type: :enum, name: name, line: token.line, col: token.col]
                  meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                  {{:container, meta, [first_variant]}, state}
                else
                  # Type alias: type Name = ExistingType
                  meta = [name: name, line: token.line, col: token.col]
                  meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                  {{:type_annotation, meta, [first_variant]}, state}
                end
            end
          end
      end

    # An optional `deriving Iface{, Iface}` suffix follows the last variant on
    # the same line, so it must be consumed BEFORE the block-closing dedent.
    {ast, state} = maybe_attach_deriving(ast, state)

    # Close the optional wrapping block by consuming the matching `:dedent`.
    # Surrounding newlines are skipped for us by the caller's own
    # `skip_newlines` but we also tolerate any trailing newline inside the
    # block.
    close_count = layout_block_count(opened_block, pre_assign_block)

    state =
      Enum.reduce(1..close_count//1, state, fn
        _, acc when close_count > 0 -> acc |> skip_newlines() |> expect_dedent()
        _, acc -> acc
      end)

    {ast, state}
  end

  defp layout_block_count(opened_block, pre_assign_block) do
    Enum.count([opened_block, pre_assign_block], & &1)
  end

  # `deriving` attaches a list of interface names to a constructor-bearing type
  # (`:container` with `:enum` container_type). Type aliases can't derive, so
  # non-container asts pass through untouched.
  defp maybe_attach_deriving({:container, meta, body}, state) do
    case peek(state) do
      %Token{type: :keyword, value: :deriving} ->
        state = advance(state)
        {names, state} = parse_deriving_names(state, [])
        {{:container, Keyword.put(meta, :deriving, names), body}, state}

      _ ->
        {{:container, meta, body}, state}
    end
  end

  defp maybe_attach_deriving(ast, state), do: {ast, state}

  defp parse_deriving_names(state, acc) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    case peek(state) do
      %Token{type: :comma} ->
        parse_deriving_names(advance(state), [name | acc])

      _ ->
        {Enum.reverse([name | acc]), state}
    end
  end

  defp parse_gadt_ctors(state, acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        cname_token = peek(state)
        cname = to_string(cname_token.value)
        state = advance(state)
        state = expect(state, :colon)
        {sig, state} = parse_ctor_signature(state)
        meta = [name: cname, line: cname_token.line, col: cname_token.col]
        parse_gadt_ctors(state, [{:gadt_ctor, meta, sig} | acc])
    end
  end

  # A constructor signature is an arrow chain `Dom -> Dom -> ... -> Result`
  # where each element is a full type application (`SF(as, bs, d1)`). The
  # general `parse_type_expr` is unusable here: its `maybe_parse_function_type`
  # splices a domain application's *arguments* into the arrow's parameter list
  # and discards the head (so `SF(as, bs, d1) -> …` loses `SF`). This dedicated
  # parser keeps each application intact and yields `{:arrow_chain, [atoms]}`
  # with the last atom as the result type.
  defp parse_ctor_signature(state) do
    {first, state} = parse_ctor_dom(state)
    collect_arrow_chain(state, [first])
  end

  defp collect_arrow_chain(state, acc) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {atom, state} = parse_ctor_dom(state)
        collect_arrow_chain(state, [atom | acc])

      _ ->
        {{:arrow_chain, Enum.reverse(acc)}, state}
    end
  end

  # A single element of a constructor's arrow chain. Ordinarily a bare type
  # application (`SNat(k)`), but a DOMAIN position may carry a NAMED dependent
  # binder `(name: Type)` — needed when a later argument type or the result
  # index depends on this explicit argument (`(k: Nat) -> SNat(k) -> NVv(S(k))`).
  # The named form yields `{:named_dom, name, inner_type_atom}`; everything else
  # falls through to `parse_type_atom` byte-for-byte (unnamed args unchanged).
  defp parse_ctor_dom(state) do
    la2 = peek_at(state, 2)

    case {peek(state), la2} do
      {%Token{type: :lparen}, %Token{type: :colon}} ->
        state = advance(state)
        name_token = peek(state)
        name = to_string(name_token.value)
        state = advance(state)
        state = expect(state, :colon)
        {inner, state} = parse_type_atom(state)
        state = expect(state, :rparen)
        {{:named_dom, name, inner}, state}

      _ ->
        parse_type_atom(state)
    end
  end

  # A single type application: `Name`, `Name(arg, ...)`, or `(atom)`.
  defp parse_type_atom(state) do
    token = peek(state)

    case token.type do
      :lparen ->
        state = advance(state)
        {inner, state} = parse_type_atom(state)
        state = expect(state, :rparen)
        {inner, state}

      _ ->
        name = to_string(token.value)
        state = advance(state)

        case peek(state) do
          %Token{type: :lparen} ->
            state = advance(state)
            {args, state} = parse_type_atom_args(state)
            state = expect(state, :rparen)
            {{:function_call, [name: name], args}, state}

          _ ->
            {{:variable, [scope: :local], name}, state}
        end
    end
  end

  defp parse_type_atom_args(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} -> {[], state}
      _ -> parse_type_atom_args_list(state)
    end
  end

  defp parse_type_atom_args_list(state) do
    {arg, state} = parse_type_atom(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_type_atom_args_list(state)
        {[arg | rest], state}

      _ ->
        {[arg], state}
    end
  end

  # A parsed type-body variant that is genuinely a constructor (has fields, so it
  # carries `variant: true`) rather than a type-alias RHS.
  defp variant_ctor?({:function_def, meta, _}), do: Keyword.get(meta, :variant, false)
  defp variant_ctor?(_), do: false

  # True when the parser is positioned at end-of-declaration rather than at a
  # constructor variant: a closing dedent/eof, the keyword/decorator that begins
  # the next sibling declaration, or a comment (a doc/line comment can never
  # start a variant — it belongs to the following declaration). Used to recognise
  # the constructor-less `type Empty = |` form. Omitting the comment tokens here
  # let a `## doc` on the *next* declaration be mis-parsed as a variant of the
  # empty type, silently turning `type Empty = |` into `type Empty = <docword>`.
  defp no_more_variants?(state) do
    case peek(state) do
      %Token{type: t} when t in [:dedent, :eof, :keyword, :at, :doc_comment, :line_comment] -> true
      _ -> false
    end
  end

  defp parse_type_variant(state) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    case peek(state) do
      %Token{type: :lparen} ->
        # Constructor with params: Some(T)
        state = advance(state)
        {params, state} = parse_type_param_list(state)
        state = expect(state, :rparen)
        ast = {:function_def, [name: name, params: params, variant: true], []}
        {ast, state}

      _ ->
        # Nullary constructor: None
        {{:variable, [variant: true], name}, state}
    end
  end

  # v0.21.0: skip any newlines before peeking for the next `|` so multi-line
  # ADT declarations parse identically to their single-line counterparts.
  defp parse_more_variants(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state)
        state = skip_newlines(state)
        {variant, state} = parse_type_variant(state)
        state = skip_newlines(state)
        {rest, state} = parse_more_variants(state)
        {[variant | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_type_param_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {t, state} = parse_type_expr(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_type_param_list(state)
            {[t | rest], state}

          _ ->
            {[t], state}
        end
    end
  end

  # Like `parse_type_param_list`, but each element may carry an optional binder
  # name (`x: A`). Used only for a standalone parenthesised type that may become a
  # dependent function type `(x: A) -> …`. Returns `{binder | nil, type_ast}`
  # pairs so the caller can build a dependent Π (binders present) or the existing
  # non-dependent arrow (all binders nil).
  defp parse_paren_type_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {binder, state} = parse_optional_binder(state)
        {t, state} = parse_type_expr(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_paren_type_list(state)
            {[{binder, t} | rest], state}

          _ ->
            {[{binder, t}], state}
        end
    end
  end

  # An optional `name :` binder prefix inside a parenthesised arrow domain. Only
  # consumes when an identifier is immediately followed by `:` — so `(N)` stays a
  # plain domain while `(n: N)` binds `n`. (A type element in this position is
  # never otherwise followed by `:`.)
  defp parse_optional_binder(state) do
    case {peek(state), peek(advance(state))} do
      {%Token{type: :identifier, value: v}, %Token{type: :colon}} ->
        {to_string(v), advance(advance(state))}

      _ ->
        {nil, state}
    end
  end

  # -- Protocol  proto Name(T) -----------------------------------------------

  defp parse_proto(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Type params: (T) or (T, U)
    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    meta = [
      container_type: :protocol,
      name: name,
      type_params: type_params,
      line: token.line,
      col: token.col
    ]

    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Implementation  impl Proto for Type -----------------------------------

  defp parse_impl(state) do
    token = peek(state)
    state = advance(state)

    # Protocol name
    {proto_name, state} = parse_dotted_name(state)

    # Expect `for`
    state = expect_keyword(state, :for)

    # Type being implemented
    {for_type, state} = parse_type_expr(state)

    # Optional where clause
    {constraints, state} =
      case peek(state) do
        %Token{type: :keyword, value: :where} ->
          state = advance(state)
          parse_constraint_list(state)

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    for_name =
      case for_type do
        {:variable, _, n} -> n
        {:function_call, m, _} -> Keyword.get(m, :name, "unknown")
        _ -> "unknown"
      end

    meta = [
      container_type: :trait,
      name: "#{proto_name}.#{for_name}",
      protocol: proto_name,
      for: for_name,
      line: token.line,
      col: token.col
    ]

    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Interface  interface Name(a) ------------------------------------------
  #
  # Compile-time typeclass declaration (the successor to `proto`). The head
  # params are the type/higher-kinded variables the interface is indexed by
  # (`interface Functor(f)`). The body is a definition block of method
  # signatures; any method that carries a `= body` is a DEFAULT, captured
  # separately in `meta[:defaults]` (name → body expr) so the elaborator can
  # fill it into implementations that omit the method. The full body list is
  # returned as the node's methods (each a `{:function_def, meta, exprs}`,
  # `exprs == []` for a bare signature).
  defp parse_interface(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    defaults =
      body
      |> Enum.flat_map(fn
        {:function_def, m, [expr | _]} -> [{Keyword.get(m, :name), expr}]
        _ -> []
      end)
      |> Map.new()

    meta = [
      name: name,
      params: params,
      defaults: defaults,
      line: token.line,
      col: token.col
    ]

    {{:interface, meta, body}, state}
  end

  # -- Implementation  implementation Iface for Type [as Name] ----------------
  #
  # An instance of an interface for a concrete head type. `as Name` marks a
  # NAMED implementation (selectable explicitly, exempt from global coherence);
  # its absence is an anonymous instance keyed on `(interface, head ctor)`.
  defp parse_implementation(state) do
    token = peek(state)
    state = advance(state)

    {iface_name, state} = parse_dotted_name(state)

    # Consume the `for` keyword.
    state = expect_keyword(state, :for)

    {for_type, state} = parse_type_expr(state)

    {as_name, state} =
      case peek(state) do
        %Token{type: :keyword, value: :as} ->
          s = advance(state)
          as_token = peek(s)
          {to_string(as_token.value), advance(s)}

        _ ->
          {nil, state}
      end

    {constraints, state} =
      case peek(state) do
        %Token{type: :keyword, value: :where} ->
          s = advance(state)
          parse_constraint_list(s)

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    for_name =
      case for_type do
        {:variable, _, n} -> n
        {:function_call, m, _} -> Keyword.get(m, :name, "unknown")
        _ -> "unknown"
      end

    meta = [
      interface: iface_name,
      for: for_name,
      for_type: for_type,
      as: as_name,
      line: token.line,
      col: token.col
    ]

    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    {{:implementation, meta, body}, state}
  end

  # -- Import  use Path.{items} [as Alias] -----------------------------------

  defp parse_use(state) do
    token = peek(state)
    state = advance(state)

    # Parse module path
    {path, state} = parse_dotted_name(state)

    # Check for selective import: .{a, b, c}
    {items, state} =
      case peek(state) do
        %Token{type: :dot} ->
          next = peek_at(state, 1)

          if next && next.type == :lbrace do
            state = advance(state) |> advance()
            {names, state} = parse_name_list(state, :rbrace)
            state = expect(state, :rbrace)
            {names, state}
          else
            {[], state}
          end

        _ ->
          {[], state}
      end

    # Check for alias: as Name
    {alias_name, state} =
      case peek(state) do
        %Token{type: :keyword, value: :as} ->
          state = advance(state)
          a = peek(state)
          state = advance(state)
          {to_string(a.value), state}

        _ ->
          {nil, state}
      end

    meta = [source: path, import_type: :use, language: :cure, line: token.line, col: token.col]
    meta = if items != [], do: Keyword.put(meta, :items, items), else: meta
    meta = if alias_name, do: Keyword.put(meta, :alias, alias_name), else: meta
    ast = {:import, meta, []}
    {ast, state}
  end

  # -- FSM  fsm Name with Payload{...} --------------------------------------

  # -- macro container (SP1) --------------------------------------------------
  # `macro Name` … indented `syntax`/`literal` rules. Soft-keyword; closes by
  # dedent (no `end`). Mirrors parse_fsm/parse_fsm_block; emits {:macro_def, …}.
  defp parse_macro_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    state = skip_macro_trivia(state)
    {rules, state} = parse_macro_block(state)

    meta = [name: name, line: token.line, col: token.col]
    {{:macro_def, meta, rules}, state}
  end

  defp parse_macro_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {rules, state} = parse_macro_rules(state, [])
        state = expect_dedent(state)
        {rules, state}

      _ ->
        {[], state}
    end
  end

  # `##`/`###` doc-comments are ALWAYS emitted as `:doc_comment` tokens
  # (independent of `preserve_comments`; see Lexer moduledoc), and plain `#`
  # comments surface as `:line_comment` tokens whenever the caller sets
  # `preserve_comments: true` (e.g. the source formatter). Neither is captured
  # as a rule-attached AST node in this milestone — they are trivia here — but
  # they MUST be skipped rather than mistaken for the end of the macro's
  # indented block (would silently empty it) or for a malformed rule line
  # (would raise a spurious :expected/:syntax_rule error).
  defp skip_macro_trivia(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_macro_trivia(advance(state))
      %Token{type: :doc_comment} -> skip_macro_trivia(advance(state))
      %Token{type: :line_comment} -> skip_macro_trivia(advance(state))
      _ -> state
    end
  end

  defp parse_macro_rules(state, acc) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "syntax"} ->
        {rule, state} = parse_macro_rule(state)
        parse_macro_rules(state, [rule | acc])

      other ->
        state = add_error(state, {:expected, :syntax_rule, :got, other.type, other.line, other.col})
        # Recover: skip a token so one bad line does not eat the block.
        parse_macro_rules(advance(state), acc)
    end
  end

  defp parse_macro_rule(state) do
    kw_token = peek(state)
    state = advance(state)

    keyword_token = peek(state)
    keyword = to_string(keyword_token.value)
    state = advance(state)

    {segments, state} = parse_rule_segments(state, [])

    state =
      case peek(state) do
        %Token{type: :identifier, value: "becomes"} -> advance(state)
        t -> add_error(state, {:expected, :becomes, :got, t.type, t.line, t.col})
      end

    {template, state} = parse_expr(state, 0)

    rule = %{
      kind: :syntax,
      keyword: keyword,
      segments: segments,
      template: template,
      progress: nil,
      line: kw_token.line
    }

    {rule, state}
  end

  # Ordered segments between a rule's keyword and `becomes`: literal tokens and
  # typed holes `<name: Kind>` (window: :lt identifier :colon identifier :gt).
  defp parse_rule_segments(state, acc) do
    case peek(state) do
      %Token{type: :identifier, value: "becomes"} ->
        {Enum.reverse(acc), state}

      %Token{type: type} when type in [:newline, :dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :lt} ->
        with %Token{type: :identifier, value: name} <- peek_at(state, 1),
             %Token{type: :colon} <- peek_at(state, 2),
             %Token{type: :identifier, value: kind} <- peek_at(state, 3),
             %Token{type: :gt} <- peek_at(state, 4) do
          hole = {:hole, %{name: name, kind: kind, line: peek(state).line}}
          state = state |> advance() |> advance() |> advance() |> advance() |> advance()
          parse_rule_segments(state, [hole | acc])
        else
          _ ->
            t = peek(state)
            state = add_error(state, {:malformed_hole, t.line, t.col})
            {Enum.reverse(acc), advance(state)}
        end

      %Token{value: v} ->
        parse_rule_segments(advance(state), [{:lit, to_string(v)} | acc])
    end
  end

  defp parse_fsm(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Expect `with`
    {payload, state} =
      case peek(state) do
        %Token{type: :keyword, value: :in} ->
          # `with` is not a keyword; reuse `in` or handle identifier
          state = advance(state)
          {p, state} = parse_expr(state, 0)
          {p, state}

        %Token{type: :identifier, value: "with"} ->
          state = advance(state)
          {p, state} = parse_expr(state, 0)
          {p, state}

        _ ->
          {nil, state}
      end

    state = skip_newlines(state)

    # Parse indented body: transitions, @terminal, @invariant, @verify
    {fsm_body, meta_additions, state} = parse_fsm_block(state)

    meta =
      [container_type: :fsm, name: name, line: token.line, col: token.col] ++ meta_additions

    meta = if payload, do: Keyword.put(meta, :payload, payload), else: meta
    ast = {:container, meta, fsm_body}
    {ast, state}
  end

  defp parse_fsm_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {items, meta_acc, state} = parse_fsm_items(state, [], [])
        state = expect_dedent(state)
        {items, meta_acc, state}

      _ ->
        {[], [], state}
    end
  end

  @fsm_callback_names ~w(on_transition on_enter on_exit on_failure on_timer on_start on_stop)

  defp parse_fsm_items(state, items_acc, meta_acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(items_acc), meta_acc, state}

      %Token{type: :at} ->
        # @terminal, @invariant, @verify, @timer
        {new_meta, state} = parse_fsm_annotation(state)
        state = skip_newlines(state)
        parse_fsm_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: cb_name} when cb_name in @fsm_callback_names ->
        # Callback block: on_transition, on_enter, on_exit, on_failure, on_timer
        {new_meta, state} = parse_fsm_callback(state)
        state = skip_newlines(state)
        parse_fsm_items(state, items_acc, meta_acc ++ new_meta)

      _ ->
        # Transition line: Source --event--> Target
        {transition, state} = parse_fsm_transition(state)
        state = skip_newlines(state)
        parse_fsm_items(state, [transition | items_acc], meta_acc)
    end
  end

  defp parse_fsm_annotation(state) do
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    case name do
      "terminal" ->
        val_token = peek(state)
        state = advance(state)
        {[terminal_states: [to_string(val_token.value)]], state}

      "invariant" ->
        {expr, state} = parse_expr(state, 0)
        {[invariants: [expr]], state}

      "verify" ->
        {expr, state} = parse_expr(state, 0)
        {[verify: [expr]], state}

      "timer" ->
        val_token = peek(state)
        state = advance(state)

        ms =
          case val_token do
            %Token{type: :integer, value: v} -> v
            _ -> String.to_integer(to_string(val_token.value))
          end

        {[timer: ms], state}

      "initial" ->
        # @initial :state_name  (optional: payload: expr, meta: expr)
        state_name_token = peek(state)

        initial_name =
          case state_name_token do
            %Token{type: :symbol, value: v} -> to_string(v)
            _ -> to_string(state_name_token.value)
          end

        state = advance(state)
        {[initial_state: initial_name], state}

      "notify_transitions" ->
        {[notify_transitions: true], state}

      "auto_caller" ->
        {[auto_caller: true], state}

      _ ->
        {[], state}
    end
  end

  # -- FSM callback blocks: on_transition, on_enter, on_exit, on_failure, on_timer
  #
  # Clauses are written as:
  #   (pattern1, pattern2, ...) -> body
  # or with a guard:
  #   (pattern1, pattern2, ...) when guard -> body
  #
  # The parenthesized patterns are parsed as comma-separated expressions and
  # assembled into a {:tuple, [], [patterns...]} node to match the callback arity.

  defp parse_fsm_callback(state) do
    name_token = peek(state)
    cb_name = String.to_atom(name_token.value)
    state = advance(state)
    state = skip_newlines(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {arms, state} = parse_fsm_callback_clauses(state)
          state = expect_dedent(state)
          {arms, state}

        _ ->
          {arm, state} = parse_fsm_callback_clause(state)
          {[arm], state}
      end

    {[{cb_name, clauses}], state}
  end

  defp parse_fsm_callback_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_fsm_callback_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_fsm_callback_clauses(state)
        {[arm | rest], state}
    end
  end

  # Parse a single FSM callback clause: (pat1, pat2, ...) [when guard] -> body
  defp parse_fsm_callback_clause(state) do
    # Expect opening paren
    state = expect(state, :lparen)

    # Parse comma-separated pattern expressions
    {patterns, state} = parse_fsm_callback_params(state)

    # Expect closing paren
    state = expect(state, :rparen)
    state = skip_newlines(state)

    # Optional guard: when expr
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    # Expect ->
    state = expect(state, :arrow)
    state = skip_newlines(state)

    # Parse body
    {body, state} = parse_expr_or_block(state)

    # Assemble patterns into a tuple node
    pattern = {:tuple, [], patterns}
    meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]

    {{:match_arm, meta, [body]}, state}
  end

  defp parse_fsm_callback_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_fsm_callback_params(state)
            {[expr | rest], state}

          _ ->
            {[expr], state}
        end
    end
  end

  defp parse_fsm_transition(state) do
    # Source --event[!?] [when guard] [do actions]--> Target
    # or * --event--> Target (wildcard)
    from_token = peek(state)

    from =
      case from_token.type do
        :star -> "*"
        _ -> to_string(from_token.value)
      end

    state = advance(state)

    # Expect transition_open (--)
    state = expect(state, :transition_open)

    # Event name and optional guard/action are lexed as tokens between -- and -->
    {event, guard, action, state} = parse_transition_body(state)

    # Detect event kind from suffix: ! = hard, ? = soft, otherwise normal
    {event_base, event_kind} = classify_event(event)

    # After transition_close (-->), parse target
    target_token = peek(state)
    target = to_string(target_token.value)
    state = advance(state)

    meta = [name: "transition", from: from, event: event_base, to: target, event_kind: event_kind]
    meta = if guard, do: Keyword.put(meta, :guard, guard), else: meta
    meta = if action, do: Keyword.put(meta, :action, action), else: meta

    ast = {:function_call, meta, []}
    {ast, state}
  end

  defp classify_event(event) when is_binary(event) do
    cond do
      String.ends_with?(event, "!") -> {String.trim_trailing(event, "!"), :hard}
      String.ends_with?(event, "?") -> {String.trim_trailing(event, "?"), :soft}
      true -> {event, :normal}
    end
  end

  defp classify_event(event), do: {to_string(event), :normal}

  defp parse_transition_body(state) do
    # Read tokens until :transition_close
    {event_name, state} = read_transition_event(state)

    # Check for guard: when ...
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_until_transition_close_or_do(state)
          {g, state}

        _ ->
          {nil, state}
      end

    # Check for action: do ...
    {action, state} =
      case peek(state) do
        %Token{type: :keyword, value: :do} ->
          state = advance(state)
          {a, state} = parse_until_transition_close(state)
          {a, state}

        _ ->
          {nil, state}
      end

    # Consume transition_close
    state = expect(state, :transition_close)
    state = skip_newlines(state)

    {event_name, guard, action, state}
  end

  defp read_transition_event(state) do
    token = peek(state)

    case token.type do
      :transition_close -> {"", state}
      :keyword -> {to_string(token.value), advance(state)}
      :identifier -> {token.value, advance(state)}
      _ -> {to_string(token.value), advance(state)}
    end
  end

  defp parse_until_transition_close_or_do(state) do
    # Parse an expression, stopping before --> or `do`
    {expr, state} = parse_expr(state, 0)
    {expr, state}
  end

  defp parse_until_transition_close(state) do
    {expr, state} = parse_expr(state, 0)
    {expr, state}
  end

  # -- Actor container  actor Name [with InitExpr] --------------------------
  #
  # An `actor` introduces a typed process. The minimal grammar is:
  #
  #     actor Counter
  #       on_start
  #         (state) -> notify(:ready); state
  #       on_message
  #         (:inc, n) -> n + 1
  #         (:dec, n) -> n - 1
  #         (:get, n) -> notify(n); n
  #       on_stop
  #         (reason, state) -> ok
  #
  # Callback blocks are parsed with the existing `parse_fsm_callback/1`
  # machinery so patterns, guards, and bodies behave exactly as they do
  # for FSM lifecycle hooks. `@initial` (or `with Expr` after the
  # header) selects the initial payload. The Cure.Actor.Compiler
  # translates this container into a GenServer via string-template
  # codegen, mirroring the FSM callback-mode path.
  defp parse_actor(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional initial payload: `with expr`.
    {init, state} =
      case peek(state) do
        %Token{type: :identifier, value: "with"} ->
          state = advance(state)
          parse_expr(state, 0)

        _ ->
          {nil, state}
      end

    state = skip_newlines(state)
    {body, meta_additions, state} = parse_actor_block(state)

    meta =
      [container_type: :actor, name: name, line: token.line, col: token.col] ++ meta_additions

    meta = if init, do: Keyword.put(meta, :init, init), else: meta
    ast = {:container, meta, body}
    {ast, state}
  end

  @actor_callback_names ~w(on_message on_start on_stop)

  defp parse_actor_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {items, meta_acc, state} = parse_actor_items(state, [], [])
        state = expect_dedent(state)
        {items, meta_acc, state}

      _ ->
        {[], [], state}
    end
  end

  defp parse_actor_items(state, items_acc, meta_acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(items_acc), meta_acc, state}

      %Token{type: :at} ->
        # `@initial expr` and the same annotations an FSM supports.
        {new_meta, state} = parse_fsm_annotation(state)
        state = skip_newlines(state)
        parse_actor_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: cb_name} when cb_name in @actor_callback_names ->
        {new_meta, state} = parse_fsm_callback(state)
        state = skip_newlines(state)
        parse_actor_items(state, items_acc, meta_acc ++ new_meta)

      _ ->
        # Tolerate unknown top-level lines by consuming a single expression
        # and discarding it. This keeps the parser forward-compatible
        # with future actor directives (e.g. `inbox = A | B`, `state: T`).
        {_expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        parse_actor_items(state, items_acc, meta_acc)
    end
  end

  # -- Supervisor container  sup Name ---------------------------------------
  #
  # Declares a supervisor module. The minimal grammar is:
  #
  #     sup MyApp.Root
  #       strategy = :one_for_one
  #       intensity = 3
  #       period = 5
  #       children
  #         Counter as counter
  #         Gateway as gateway (restart: :transient)
  #         sup Workers as workers
  #
  # `strategy`, `intensity`, `period` are parsed as `name = value` lines
  # and hoisted onto the container meta. The `children` block contains
  # one `child_spec` node per line, each emitted as
  # `{:child_spec, [module:, id:, restart:, shutdown:, ...], []}`.
  defp parse_supervisor(state) do
    token = peek(state)
    state = advance(state)

    {name, state} = parse_dotted_name(state)
    state = skip_newlines(state)
    {body, meta_additions, state} = parse_sup_block(state)

    meta =
      [container_type: :supervisor, name: name, line: token.line, col: token.col] ++
        meta_additions

    ast = {:container, meta, body}
    {ast, state}
  end

  defp parse_sup_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {items, meta_acc, state} = parse_sup_items(state, [], [])
        state = expect_dedent(state)
        {items, meta_acc, state}

      _ ->
        {[], [], state}
    end
  end

  @sup_settings ~w(strategy intensity period)

  defp parse_sup_items(state, items_acc, meta_acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(items_acc), meta_acc, state}

      %Token{type: :identifier, value: setting} when setting in @sup_settings ->
        {new_meta, state} = parse_sup_setting(state, setting)
        state = skip_newlines(state)
        parse_sup_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: "children"} ->
        state = advance(state)
        state = skip_newlines(state)
        {specs, state} = parse_sup_children_block(state)
        state = skip_newlines(state)
        parse_sup_items(state, Enum.reverse(specs) ++ items_acc, meta_acc)

      _ ->
        # Unknown leading token inside a supervisor body -- skip one
        # expression and keep going so we don't deadlock.
        {_, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        parse_sup_items(state, items_acc, meta_acc)
    end
  end

  defp parse_sup_setting(state, name) do
    # Consume the identifier and the `=`.
    state = advance(state)
    state = expect(state, :assign)
    state = skip_newlines(state)
    {value, state} = parse_expr(state, 0)
    {[{String.to_atom(name), value}], state}
  end

  defp parse_sup_children_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {specs, state} = parse_sup_child_specs(state, [])
        state = expect_dedent(state)
        {specs, state}

      _ ->
        {[], state}
    end
  end

  defp parse_sup_child_specs(state, acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        {spec, state} = parse_sup_child_spec(state)
        state = skip_newlines(state)
        parse_sup_child_specs(state, [spec | acc])
    end
  end

  # A child spec line takes one of the forms:
  #
  #     Counter as counter
  #     Counter as counter (restart: :transient, shutdown: 5000)
  #     sup Workers as workers
  #
  # Emits `{:child_spec, meta, []}` where `meta` carries the child's
  # `:module`, `:id`, and any options parsed from the trailing
  # parenthesised keyword list.
  defp parse_sup_child_spec(state) do
    token = peek(state)

    {module_kind, state} =
      case token do
        %Token{type: :identifier, value: "sup"} ->
          {:supervisor, advance(state)}

        _ ->
          {:worker, state}
      end

    {module_path, state} = parse_dotted_name(state)

    # Expect `as child_id`.
    state = expect_keyword(state, :as)
    id_token = peek(state)
    id_name = to_string(id_token.value)
    state = advance(state)

    # Optional options: `(restart: :transient, shutdown: 5000)`.
    {opts, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {pairs, state} = parse_sup_child_opts(state)
          state = expect(state, :rparen)
          {pairs, state}

        _ ->
          {[], state}
      end

    meta =
      [
        module: module_path,
        id: id_name,
        kind: module_kind,
        line: token.line,
        col: token.col
      ] ++ opts

    {{:child_spec, meta, []}, state}
  end

  defp parse_sup_child_opts(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {pair, state} = parse_sup_child_opt(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_sup_child_opts(state)
            {[pair | rest], state}

          _ ->
            {[pair], state}
        end
    end
  end

  defp parse_sup_child_opt(state) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = expect(state, :colon)
    state = skip_newlines(state)
    {value, state} = parse_expr(state, 0)
    {{String.to_atom(name), value}, state}
  end

  # -- Application container  app Name.Path ---------------------------------
  #
  # Declares an OTP application. The minimal grammar is:
  #
  #     app MyApp
  #       vsn          = "0.1.0"
  #       description  = "My humble application"
  #       root         = sup MyApp.Root
  #       applications = [:logger, :crypto]
  #       env          = %{port: 4000, name: "dev"}
  #       on_start
  #         (type, args) -> do_start(type, args)
  #       on_stop
  #         (state) -> cleanup(state)
  #       on_phase :init
  #         (args, type, start_args) -> init_phase(args)
  #       on_phase :warm_cache
  #         (_args, _type, _start_args) -> Std.Cache.warm()
  #
  # `vsn`, `description`, `root`, `applications`, `included_applications`,
  # `env`, and `registered` are parsed as `name = value` lines and hoisted
  # onto the container meta. `on_start`, `on_stop`, and `on_phase :name`
  # reuse the `parse_fsm_callback/1` machinery so patterns, guards, and
  # bodies behave exactly as they do for FSM/actor lifecycle hooks.
  #
  # Compilation is handled by `Cure.App.Compiler` and produces an Elixir
  # module `:"Cure.App.<Name>"` that `use Application` with `start/2`,
  # `stop/1`, and `start_phase/3` callbacks.
  defp parse_app_container(state) do
    token = peek(state)
    state = advance(state)

    {name, state} = parse_dotted_name(state)
    state = skip_newlines(state)
    {body, meta_additions, state} = parse_app_block(state)

    meta =
      [container_type: :app, name: name, line: token.line, col: token.col] ++
        meta_additions

    ast = {:container, meta, body}
    {ast, state}
  end

  defp parse_app_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {items, meta_acc, state} = parse_app_items(state, [], [])
        state = expect_dedent(state)
        {items, meta_acc, state}

      _ ->
        {[], [], state}
    end
  end

  @app_settings ~w(vsn description root applications included_applications env registered)
  @app_callback_names ~w(on_start on_stop)

  defp parse_app_items(state, items_acc, meta_acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(items_acc), meta_acc, state}

      %Token{type: :identifier, value: setting} when setting in @app_settings ->
        {new_meta, state} = parse_app_setting(state, setting)
        state = skip_newlines(state)
        parse_app_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: cb_name} when cb_name in @app_callback_names ->
        {new_meta, state} = parse_fsm_callback(state)
        state = skip_newlines(state)
        parse_app_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: "on_phase"} ->
        {new_meta, state} = parse_app_on_phase(state)
        state = skip_newlines(state)
        parse_app_items(state, items_acc, meta_acc ++ new_meta)

      _ ->
        # Unknown leading token inside an app body -- skip one expression
        # and keep going so we don't deadlock.
        {_, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        parse_app_items(state, items_acc, meta_acc)
    end
  end

  defp parse_app_setting(state, name) do
    # Consume the identifier and the `=`.
    state = advance(state)
    state = expect(state, :assign)
    state = skip_newlines(state)
    {value, state} = parse_expr(state, 0)
    {[{String.to_atom(name), value}], state}
  end

  # `on_phase :phase_name` introduces a single callback whose arity is
  # three: `(args, start_type, start_args)`. The phase atom is hoisted
  # onto the container meta under `:on_phase => [{phase_atom, [clauses]}]`
  # so verifier and compiler can dispatch by phase.
  defp parse_app_on_phase(state) do
    state = advance(state)
    state = skip_newlines(state)

    {phase_atom, state} =
      case peek(state) do
        %Token{type: :atom, value: v} ->
          {String.to_atom(to_string(v)), advance(state)}

        %Token{type: :identifier, value: v} ->
          {String.to_atom(to_string(v)), advance(state)}

        other ->
          {String.to_atom(to_string(other.value)), advance(state)}
      end

    state = skip_newlines(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {arms, state} = parse_fsm_callback_clauses(state)
          state = expect_dedent(state)
          {arms, state}

        _ ->
          {arm, state} = parse_fsm_callback_clause(state)
          {[arm], state}
      end

    {[{:on_phase, [{phase_atom, clauses}]}], state}
  end

  # -- Enhanced Type Expression Parser ----------------------------------------

  # Replaces the simple version from Milestone 2.
  # Handles: PascalCase, Type(A, B), A -> B, (A, B) -> C, {x: T | pred}
  defp parse_type_expr(state) do
    token = peek(state)

    case token.type do
      :lparen ->
        # Grouped/tuple type `(A, B)` or function type `(A, B) -> C`. Each element
        # may carry an optional binder name `(x: A) -> …` — a DEPENDENT arrow whose
        # codomain (and later domains) may mention `x`.
        state = advance(state)
        {inner, state} = parse_paren_type_list(state)
        state = expect(state, :rparen)

        case peek(state) do
          %Token{type: :arrow} ->
            state = advance(state)
            {ret, state} = parse_type_expr(state)
            binders = Enum.map(inner, &elem(&1, 0))
            doms = Enum.map(inner, &elem(&1, 1))

            ast =
              if Enum.all?(binders, &is_nil/1) do
                # No named domain — the existing non-dependent arrow, unchanged.
                {:function_call, [name: "Function", function_type: true], doms ++ [ret]}
              else
                # At least one named domain — a dependent Π; carry the binder names
                # (nil for anonymous domains) for the elaborator to scope.
                {:pi_type, [binders: binders], doms ++ [ret]}
              end

            {ast, state}

          _ ->
            # Grouped type or tuple type — binders (if any) are not meaningful here.
            case Enum.map(inner, &elem(&1, 1)) do
              [single] -> {single, state}
              many -> {{:tuple, [], many}, state}
            end
        end

      _ ->
        # Simple type: Name or Name(A, B)
        state = advance(state)
        base_name = to_string(token.value)

        cond do
          base_name == "Sigma" and match?(%Token{type: :lparen}, peek(state)) ->
            parse_sigma_type(state)

          base_name == "Tuple" and match?(%Token{type: :lparen}, peek(state)) ->
            parse_tuple_type(state)

          match?(%Token{type: :lparen}, peek(state)) ->
            state = advance(state)
            {params, state} = parse_type_param_list(state)
            state = expect(state, :rparen)
            ast = {:function_call, [name: base_name], params}
            maybe_parse_function_type(state, ast)

          match?(%Token{type: :arrow}, peek(state)) ->
            # A -> B  (unary function type)
            state = advance(state)
            {ret, state} = parse_type_expr(state)
            base = {:variable, [scope: :local], base_name}
            ast = {:function_call, [name: "Function", function_type: true], [base, ret]}
            {ast, state}

          true ->
            base = {:variable, [scope: :local], base_name}
            maybe_parse_type_projection(base, state)
        end
    end
  end

  # A type-position projection `p.1` / `p.2` (used in dependent index positions,
  # e.g. `SF(as, bs, p.1)`).
  defp maybe_parse_type_projection(inner, state) do
    case peek(state) do
      %Token{type: :dot} ->
        state = advance(state)
        attr_token = peek(state)
        attr = to_string(attr_token.value)
        state = advance(state)
        node = {:attribute_access, [attribute: attr], [inner]}
        maybe_parse_type_projection(node, state)

      _ ->
        {inner, state}
    end
  end

  # Sigma(x: DomType, BodyType) — a dependent-pair type (design spec §4.7). The
  # body type may mention the binder `x`.
  defp parse_sigma_type(state) do
    state = advance(state)
    name_token = peek(state)
    binder = to_string(name_token.value)
    state = advance(state)
    state = expect(state, :colon)
    {dom_type, state} = parse_type_expr(state)
    state = expect(state, :comma)
    {body_type, state} = parse_type_expr(state)
    state = expect(state, :rparen)
    {{:sigma_type, [binder: binder], [dom_type, body_type]}, state}
  end

  # Tuple(T1, …, Tn) — the honest surface tuple (spec 2026-07-09-unified-tuple §3).
  # Parse a comma-separated list of `[binder?:] type` positions (≥ 2). EVERY arity
  # (including 2) becomes `{:tuple_type, [arity: n, binders: bs], [t1…tn]}` — the
  # elaborator unfolds it to a UNIT-TERMINATED nested Σ telescope
  # (`Sigma(T1, λb1. … Sigma(Tn, λbn. Unit))`) which emit flattens to a flat BEAM
  # tuple. This is DELIBERATELY distinct from bare `Sigma(x:T, U)` (`:sigma_type`,
  # NOT unit-terminated): the terminator is what lets emit tell "flatten the whole
  # spine" from "this element is itself a nested tuple". Per-position binders are
  # retained so a later position may depend on an earlier one (dependent telescope);
  # an anonymous position is binder `"_"`.
  defp parse_tuple_type(state) do
    state = advance(state)
    {positions, state} = parse_tuple_positions(state, [])
    state = expect(state, :rparen)

    binders = Enum.map(positions, &elem(&1, 0))
    types = Enum.map(positions, &elem(&1, 1))
    ast = {:tuple_type, [arity: length(positions), binders: binders], types}

    {ast, state}
  end

  # A `[binder?:] type` position list, comma-separated, terminated by `:rparen`.
  defp parse_tuple_positions(state, acc) do
    {binder, state} =
      case {peek(state), peek_at(state, 1)} do
        {%Token{} = t, %Token{type: :colon}} ->
          {to_string(t.value), advance(advance(state))}

        _ ->
          {"_", state}
      end

    {type, state} = parse_type_expr(state)
    acc = [{binder, type} | acc]

    case peek(state) do
      %Token{type: :comma} -> parse_tuple_positions(advance(state), acc)
      _ -> {Enum.reverse(acc), state}
    end
  end

  defp maybe_parse_function_type(state, left) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {ret, state} = parse_type_expr(state)

        params =
          case left do
            {:function_call, _, p} -> p
            _ -> [left]
          end

        ast = {:function_call, [name: "Function", function_type: true], params ++ [ret]}
        {ast, state}

      _ ->
        {left, state}
    end
  end

  # -- Effect List  ! Io, Exception ------------------------------------------

  defp parse_effect_list(state) do
    state = skip_newlines(state)
    {first, state} = parse_single_effect(state)

    {rest, state} =
      case peek(state) do
        %Token{type: :comma} ->
          state = advance(state)
          state = skip_newlines(state)
          {more, state} = parse_effect_list_tail(state)
          {more, state}

        _ ->
          {[], state}
      end

    {[first | rest], state}
  end

  defp parse_effect_list_tail(state) do
    {eff, state} = parse_single_effect(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_effect_list_tail(state)
        {[eff | rest], state}

      _ ->
        {[eff], state}
    end
  end

  defp parse_single_effect(state) do
    token = peek(state)
    state = advance(state)
    name = to_string(token.value)

    effect =
      case String.downcase(name) do
        "io" -> :io
        "state" -> :state
        "exception" -> :exception
        "spawn" -> :spawn
        "extern" -> :extern
        _ -> String.to_atom(String.downcase(name))
      end

    {effect, state}
  end

  # -- Constraint List  Proto(T), Proto2(U) ----------------------------------

  defp parse_constraint_list(state) do
    {first, state} = parse_single_constraint(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_constraint_list(state)
        {[first | rest], state}

      _ ->
        {[first], state}
    end
  end

  defp parse_single_constraint(state) do
    # Proto(T) form
    name_token = peek(state)
    state = advance(state)
    name = to_string(name_token.value)

    case peek(state) do
      %Token{type: :lparen} ->
        state = advance(state)
        {params, state} = parse_type_param_list(state)
        state = expect(state, :rparen)
        {{:function_call, [name: name, constraint: true], params}, state}

      _ ->
        {{:variable, [constraint: true], name}, state}
    end
  end

  # -- Helpers: dotted names, name lists, definition blocks ------------------

  defp parse_dotted_name(state) do
    first = peek(state)
    state = advance(state)
    parse_dotted_name(state, to_string(first.value))
  end

  defp parse_dotted_name(state, acc) do
    case peek(state) do
      %Token{type: :dot} ->
        # Don't consume dot if next token is { (selective import syntax)
        next = peek_at(state, 1)

        if next && next.type in [:lbrace, :lbracket] do
          {acc, state}
        else
          state = advance(state)
          next_token = peek(state)
          state = advance(state)
          parse_dotted_name(state, acc <> "." <> to_string(next_token.value))
        end

      _ ->
        {acc, state}
    end
  end

  defp parse_name_list(state, closing) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], state}

      _ ->
        token = peek(state)
        state = advance(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, state} = parse_name_list(state, closing)
            {[to_string(token.value) | rest], state}

          _ ->
            {[to_string(token.value)], state}
        end
    end
  end

  # Parse an indented block of definitions (for mod, proto, impl bodies)
  #
  # Tolerates doc_comment tokens that precede the leading `:indent` --
  # the lexer emits fenced `###...###` docstrings *before* measuring the
  # indentation of the line that follows, so a module body like
  #
  #     mod M
  #       ###
  #       description
  #       ###
  #       fn f() -> Int = 0
  #
  # will have the token stream `[mod, M, newline, doc_comment, indent,
  # fn, ...]`. Prior to v0.17.0 we would bail out with an empty body.
  # Now we carry the doc forward to attach to the first definition
  # inside the block (if any).
  defp parse_definition_block(state) do
    {stmts, leading_doc, state} = parse_definition_block_with_lead_doc(state)
    {attach_leading_doc(stmts, leading_doc), state}
  end

  # Variant of `parse_definition_block/1` used by container parsers that
  # want to interpret the leading `##` block as the container's own doc
  # (e.g. `mod Name`). Returns the doc separately so the caller can
  # attach it to the container meta instead of the first body statement.
  #
  # The lexer doesn't emit `:indent` for doc-comment-only lines, so a
  # module whose first body definition is preceded by its own `##`
  # block has a token stream of the shape
  #
  #     [mod, Name, newline, doc_module..., doc_first..., indent, def...]
  #
  # `collect_leading_docs/1` honours blank-line gaps and only consumes
  # the contiguous module-doc run, leaving `doc_first` in the stream.
  # To let parsing continue into the indented body, we look past any
  # further doc comments when searching for `:indent`, and feed the
  # first-definition doc back in via `attach_leading_doc/2` so it
  # binds to the first body statement.
  defp parse_definition_block_with_lead_doc(state) do
    {leading_doc, state} = collect_leading_docs(state)
    {pending_first_doc, state} = collect_leading_docs(state)
    {leading_comments, state} = collect_leading_line_comments(state)

    case peek(state) do
      %Token{type: :indent} ->
        token = peek(state)
        state = advance(state)
        {stmts, state} = parse_block_body(state, token.value)
        state = expect_dedent(state)

        stmts = prepend_line_comments(stmts, leading_comments)
        stmts = attach_leading_doc(stmts, pending_first_doc)

        {stmts, leading_doc, state}

      _ ->
        {[], leading_doc, state}
    end
  end

  # Collect any doc_comment tokens (intermixed with newlines) and return
  # their concatenated text plus the advanced state. Returns `{"", state}`
  # when there are no doc comments to consume.
  defp collect_leading_docs(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :doc_comment} ->
        {text, state} = collect_doc_comments(state)
        state = skip_newlines(state)
        {text, state}

      _ ->
        {"", state}
    end
  end

  # Collect `:line_comment` tokens that appear on indented comment-only
  # lines before the block's `:indent` token. The lexer emits them at
  # their measured column but *ahead* of the indent push (to avoid
  # treating a comment-only line as starting the block), so we route
  # them back inside the block body here.
  defp collect_leading_line_comments(state) do
    state = skip_newlines(state)
    collect_leading_line_comments(state, [])
  end

  defp collect_leading_line_comments(state, acc) do
    case peek(state) do
      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        collect_leading_line_comments(state, [node | acc])

      _ ->
        {Enum.reverse(acc), state}
    end
  end

  defp prepend_line_comments(stmts, []), do: stmts
  defp prepend_line_comments(stmts, comments), do: comments ++ stmts

  defp attach_leading_doc([first | rest], doc) when doc != "" do
    [attach_doc(first, doc) | rest]
  end

  defp attach_leading_doc(stmts, _doc), do: stmts

  # -- Decorator Attachment (@name before fn) --------------------------------

  defp parse_at(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    state = advance(state)
    dec_name = to_string(name_token.value)

    # Check if it's a call: @name(args) or @name value (bare boolean)
    {args, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {a, state} = parse_call_args(state)
          {a, state}

        %Token{type: :bool, value: bval} ->
          state = advance(state)
          arg = {:literal, [subtype: :boolean], bval}
          {[arg], state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Module-level decorators (e.g. `@group(:core)`) describe the MODULE. The
    # canonical form is `@group(:g)` directly above `mod`, where it attaches to
    # the module container (spec 2026-07-10-group-decorator-placement). The
    # in-body form is deprecated, not fatal: hard-failing would make a file using
    # the old placement unparseable — and therefore un-migratable — so we mirror
    # the `if`→`pickup` path (emit a deprecation event, keep the decorator node)
    # and let `cure migrate`'s @group-hoist rule relocate it to the canonical spot.
    if dec_name in @module_level_decorators do
      case peek(state) do
        %Token{type: :keyword, value: :mod} ->
          {mod_ast, state} = parse_module(state)
          {attach_decorator(mod_ast, dec_name, args), state}

        _ ->
          state = emit_group_placement_deprecation(state, token, dec_name)
          ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
          {ast, state}
      end
    else
      parse_at_attach(state, token, dec_name, args)
    end
  end

  # Attach `@name(args)` to a following fn/rec/type declaration, or emit a
  # standalone decorator/property node when nothing attachable follows.
  defp parse_at_attach(state, token, dec_name, args) do
    # Check if the next thing is a function definition -- if so, attach decorator
    case peek(state) do
      %Token{type: :keyword, value: kw} when kw in [:fn, :local] ->
        {fn_ast, state} = parse_expr(state, 0)
        fn_ast = attach_decorator(fn_ast, dec_name, args)
        {fn_ast, state}

      # v0.19.0: `@derive(Show, Eq, ...) rec Name` attaches the
      # derive list to the record container.
      %Token{type: :keyword, value: :rec} ->
        {rec_ast, state} = parse_expr(state, 0)
        rec_ast = attach_decorator(rec_ast, dec_name, args)
        {rec_ast, state}

      # `@builtin(:key) type Name = ...` attaches the decorator to the type
      # container (an enum ADT → {:container, container_type: :enum, ...}, which
      # attach_decorator/3's generic clause threads into :decorator meta).
      # `@builtin(:key) type Name indices (...)` attaches to the {:indexed_type}
      # meta (Bounded's GADT family). A @builtin on an alias ({:type_annotation})
      # form is still silently dropped — no attach_decorator clause today.
      %Token{type: :keyword, value: :type} ->
        {type_ast, state} = parse_type_def(state)
        type_ast = attach_decorator(type_ast, dec_name, args)
        {type_ast, state}

      # `@builtin(:tag) primitive Name` attaches the decorator to the primitive
      # container (the generic {:container, …} attach_decorator clause writes it
      # into :decorator meta, like `@builtin(:key) type Name`).
      %Token{type: :keyword, value: :primitive} ->
        {prim_ast, state} = parse_primitive_def(state)
        prim_ast = attach_decorator(prim_ast, dec_name, args)
        {prim_ast, state}

      _ ->
        # Standalone decorator or property
        if args != [] do
          ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
          {ast, state}
        else
          ast = {:property, [name: dec_name, line: token.line, col: token.col], dec_name}
          {ast, state}
        end
    end
  end

  defp attach_decorator(fn_ast, dec_name, args) do
    case fn_ast do
      {:container, meta, body} ->
        # Record container with @derive(Show, Eq, Ord).
        case Keyword.get(meta, :container_type) do
          :struct when dec_name == "derive" ->
            derive_names =
              Enum.map(args, fn
                {:variable, _, n} -> String.downcase(n) |> String.to_atom()
                {:function_call, m, _} -> Keyword.get(m, :name, "") |> String.downcase() |> String.to_atom()
                other -> extract_literal_value(other)
              end)

            {:container, Keyword.put(meta, :derive, derive_names), body}

          _ ->
            {:container, Keyword.put(meta, :decorator, {String.to_atom(dec_name), args}), body}
        end

      # `@builtin(:key) type Name indices (...)` — a GADT / indexed family.
      # Thread the decorator into the indexed_type meta so
      # program.ex's maybe_register_builtin can see it (mirrors the
      # {:container} enum-ADT clause above).
      {:indexed_type, meta, ctors} ->
        {:indexed_type, Keyword.put(meta, :decorator, {String.to_atom(dec_name), args}), ctors}

      {:function_def, meta, body} ->
        decoration =
          case dec_name do
            "extern" ->
              # @extern(:mod, :fun, arity) -> extern: {mod, fun, arity}
              extern_val =
                case args do
                  [m, f, a] -> {extract_literal_value(m), extract_literal_value(f), extract_literal_value(a)}
                  _ -> args
                end

              [extern: extern_val]

            _ ->
              [decorator: {String.to_atom(dec_name), args}]
          end

        {:function_def, meta ++ decoration, body}

      other ->
        other
    end
  end

  defp extract_literal_value({:literal, _, val}), do: val

  # `@extern(Elixir.Cure.FSM.Builtins, :f, 1)` parses the first argument
  # as a chain of attribute accesses rooted in a PascalCase variable.
  # Collapse that chain to an atom so codegen receives a literal atom.
  defp extract_literal_value({:attribute_access, _, _} = ast) do
    case attribute_access_to_dotted(ast) do
      nil -> ast
      name -> String.to_atom(name)
    end
  end

  defp extract_literal_value({:variable, _, name}) when is_binary(name) do
    case name do
      <<c, _::binary>> when c in ?A..?Z -> String.to_atom(name)
      _ -> name
    end
  end

  defp extract_literal_value(other), do: other

  defp attribute_access_to_dotted({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute)

    case attribute_access_to_dotted(parent) do
      nil -> nil
      path -> path <> "." <> to_string(attr)
    end
  end

  defp attribute_access_to_dotted({:variable, _, name}) when is_binary(name), do: name
  defp attribute_access_to_dotted(_), do: nil

  # -- Keyword unary (return, throw, yield, spawn) ---------------------------

  defp parse_keyword_unary(state, node_type) do
    token = peek(state)
    state = advance(state)
    {expr, state} = parse_expr(state, 0)
    ast = {node_type, [line: token.line, col: token.col], [expr]}
    {ast, state}
  end

  # -- Send ------------------------------------------------------------------

  # The keyword statement form `send target, message` desugars to the
  # same `{:send, meta, [target, message]}` node emitted by the
  # Melquiades operator so downstream stages (type checker, codegen,
  # effects) have a single shape to reason about. `:melquiades_form` is
  # set to `:keyword` to let the printer round-trip the statement form.
  defp parse_send(state) do
    token = peek(state)
    state = advance(state)
    {target, state} = parse_expr(state, 0)
    state = expect(state, :comma)
    {message, state} = parse_expr(state, 0)
    meta = [line: token.line, col: token.col, melquiades_form: :keyword]
    ast = {:send, meta, [target, message]}
    {ast, state}
  end

  # -- Receive ---------------------------------------------------------------

  defp parse_receive(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    # Parse like match arms
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)

        # Optional after timeout
        {timeout, state} =
          case peek(state) do
            %Token{type: :keyword, value: :after} ->
              state = advance(state)
              {timeout_expr, state} = parse_expr(state, 0)
              state = skip_newlines(state)
              {timeout_body, state} = parse_block(state)
              {{timeout_expr, timeout_body}, state}

            _ ->
              {nil, state}
          end

        meta = [line: token.line, col: token.col]
        meta = if timeout, do: Keyword.put(meta, :timeout, timeout), else: meta
        ast = {:async_operation, meta, arms}
        {ast, state}

      _ ->
        ast = {:async_operation, [line: token.line, col: token.col], []}
        {ast, state}
    end
  end

  # -- Try / Catch / Finally -------------------------------------------------

  defp parse_try(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    {try_body, state} = parse_block(state)
    state = skip_newlines(state)

    # catch clause
    {catch_arms, state} =
      case peek(state) do
        %Token{type: :keyword, value: :catch} ->
          state = advance(state)
          state = skip_newlines(state)

          case peek(state) do
            %Token{type: :indent} ->
              state = advance(state)
              {arms, state} = parse_block_match_arms(state)
              state = expect_dedent(state)
              {arms, state}

            _ ->
              {[], state}
          end

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # finally clause
    {finally_body, state} =
      case peek(state) do
        %Token{type: :keyword, value: :finally} ->
          state = advance(state)
          state = skip_newlines(state)
          {body, state} = parse_block(state)
          {body, state}

        _ ->
          {nil, state}
      end

    children = [try_body | catch_arms]
    children = if finally_body, do: children ++ [finally_body], else: children
    ast = {:exception_handling, [line: token.line, col: token.col], children}
    {ast, state}
  end

  # -- Block Parsing ---------------------------------------------------------

  defp parse_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        token = peek(state)
        state = advance(state)
        {exprs, state} = parse_block_body(state, token.value)
        state = expect_dedent(state)

        case exprs do
          [single] -> {single, state}
          many -> {{:block, [line: token.line, col: token.col], many}, state}
        end

      _ ->
        # Single expression as body (no indent)
        parse_expr(state, 0)
    end
  end

  defp parse_block_body(state, indent) do
    state = skip_newlines(state)
    parse_block_body(state, [], indent)
  end

  defp parse_block_body(state, acc, indent) do
    case peek(state) do
      %Token{type: :dedent, value: value}
      when is_integer(indent) and is_integer(value) and value > indent ->
        state
        |> advance()
        |> skip_newlines()
        |> parse_block_body(acc, indent)

      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        parse_block_body(state, [node | acc], indent)

      %Token{type: :doc_comment} ->
        # Collect consecutive doc comment blocks -- including ones
        # separated by blank-line gaps -- so that prose split across
        # paragraphs (or intermixed with plain `#` comments the lexer
        # drops) still attaches to the following definition as a
        # single docstring.
        {doc_text, state} = collect_all_doc_comments(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: type} when type in [:dedent, :eof] ->
            {Enum.reverse(acc), state}

          _ ->
            prev_errors = length(state.errors)
            {expr, state} = parse_expr(state, 0)
            expr = attach_doc(expr, doc_text)
            # If this expression introduced new parse errors, skip to the next
            # statement boundary (E063 recovery) so the broken statement cannot
            # consume tokens that belong to subsequent well-formed definitions.
            state =
              if length(state.errors) > prev_errors,
                do: synchronize_to_statement(state),
                else: state

            state = skip_newlines(state)
            parse_block_body(state, [expr | acc], indent)
        end

      _ ->
        prev_errors = length(state.errors)
        {expr, state} = parse_expr(state, 0)
        # Recovery: if this expression introduced parse errors, synchronize to
        # the next statement boundary before continuing so subsequent
        # well-formed definitions are not consumed as part of the failed parse.
        state =
          if length(state.errors) > prev_errors,
            do: synchronize_to_statement(state),
            else: state

        state = skip_newlines(state)
        parse_block_body(state, [expr | acc], indent)
    end
  end

  # Parse either a block (if indent follows) or a single expression
  defp parse_expr_or_block(state) do
    case peek(state) do
      %Token{type: :indent} -> parse_block(state)
      _ -> parse_expr(state, 0)
    end
  end

  defp parse_expression_let_chain_body({:assignment, meta, _} = assignment, state) do
    if Keyword.get(meta, :let) do
      parse_expression_let_chain_tail([assignment], state, meta)
    else
      {assignment, state}
    end
  end

  defp parse_expression_let_chain_body(body, state), do: {body, state}

  defp parse_expression_let_chain_tail(acc, state, meta) do
    state = skip_newlines(state)

    if expression_let_chain_tail?(state) do
      {expr, state} = parse_expr_or_block(state)
      acc = [expr | acc]

      case expr do
        {:assignment, expr_meta, _} ->
          if Keyword.get(expr_meta, :let) do
            parse_expression_let_chain_tail(acc, state, meta)
          else
            {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], Enum.reverse(acc)}, state}
          end

        _ ->
          {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], Enum.reverse(acc)}, state}
      end
    else
      case Enum.reverse(acc) do
        [single] -> {single, state}
        many -> {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], many}, state}
      end
    end
  end

  defp expression_let_chain_tail?(state) do
    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof, :bar, :comma, :rparen, :rbracket, :rbrace] ->
        false

      %Token{type: :keyword, value: value}
      when value in [:fn, :local, :type, :proto, :impl, :mod, :use, :actor, :fsm, :app, :supervisor] ->
        false

      _ ->
        true
    end
  end

  # -- Comma-separated expressions -------------------------------------------

  defp parse_comma_exprs(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {expr, state} = parse_expr(state, 0)
        {rest, state} = parse_comma_exprs(state)
        {[expr | rest], state}

      _ ->
        {[], state}
    end
  end

  # -- Token Helpers ---------------------------------------------------------

  defp peek(%{tokens: tokens, pos: pos}) when pos >= length(tokens) do
    Token.new(:eof, nil, 1, 1)
  end

  defp peek(%{tokens: tokens, pos: pos}), do: Enum.at(tokens, pos)

  defp peek_at(%{tokens: tokens, pos: pos}, offset) do
    idx = pos + offset
    if idx >= 0 and idx < length(tokens), do: Enum.at(tokens, idx), else: nil
  end

  defp advance(state), do: %{state | pos: state.pos + 1}

  # `:line_comment` tokens are emitted by the lexer only when
  # `preserve_comments: true` is set. In that mode `parse_program/2`
  # and `parse_block_body/2` peek for them explicitly *before* calling
  # `skip_newlines/1` and turn them into `{:comment, meta, text}` AST
  # nodes. Inside expressions they are absent from the stream because
  # the lexer places them at line boundaries.
  defp skip_newlines(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_newlines(advance(state))
      _ -> state
    end
  end

  defp expect(state, expected_type) do
    token = peek(state)

    if token.type == expected_type do
      advance(state)
    else
      error = {:expected, expected_type, :got, token.type, token.line, token.col}
      add_error(state, error)
    end
  end

  defp expect_keyword(state, expected_value) do
    token = peek(state)

    if token.type == :keyword and token.value == expected_value do
      advance(state)
    else
      error = {:expected, expected_value, :got, token.type, token.line, token.col}
      add_error(state, error)
    end
  end

  defp expect_dedent(state) do
    case peek(state) do
      %Token{type: :dedent} -> advance(state)
      _ -> state
    end
  end

  defp add_error(state, error) do
    if state.emit_events do
      Events.emit(:parser, :error, error, Events.meta(state.file, 1))
    end

    %{state | errors: [error | state.errors]}
  end

  # PICKUP §17 / MATCH §10: emit a deprecation event whenever the
  # legacy `if` keyword is parsed. The event payload identifies the
  # spec-reserved diagnostic code `E-IF-REMOVED` so subscribers (the
  # LSP, the `mix cure.rewrite` task) can surface the migration hint.
  # Subsequent `elif` branches reuse the same `parse_if/1` recursive
  # call site -- and therefore the same emission point -- so a chained
  # `if/elif/elif/else` produces one event per branch, which is the
  # right granularity for editor diagnostics.
  defp emit_if_deprecation(state, token) do
    if state.emit_events do
      payload =
        {:if_deprecated, "`if`/`elif` are deprecated; rewrite as `pickup` (E-IF-REMOVED, see docs/PICKUP.md §17)",
         line: token.line, col: token.col}

      Events.emit(:parser, :deprecation, payload, Events.meta(state.file, token.line))
    end

    state
  end

  # A module-level decorator (`@group`) placed somewhere other than directly above
  # `mod` is the deprecated in-body form. Mirroring `emit_if_deprecation/2`, emit a
  # deprecation event (spec-reserved code `E-GROUP-PLACEMENT`) rather than a hard
  # error, so the file still parses and the @group-hoist migration can relocate it.
  defp emit_group_placement_deprecation(state, token, dec_name) do
    if state.emit_events do
      payload =
        {:group_not_above_module,
         "@#{dec_name}(...) belongs directly above `mod`; rewrite via `cure migrate` " <>
           "(E-GROUP-PLACEMENT, see docs/superpowers/specs/2026-07-10-group-decorator-placement)",
         line: token.line, col: token.col}

      Events.emit(:parser, :deprecation, payload, Events.meta(state.file, token.line))
    end

    state
  end

  # After a parse error, skip forward until a safe statement boundary:
  # a newline, dedent, or eof ends the current statement, and a
  # definition-opening keyword (fn, mod, rec, ...) starts the next one.
  # This prevents a broken statement from silently consuming tokens that
  # belong to subsequent well-formed definitions (E063 recovery).
  defp synchronize_to_statement(state) do
    case peek(state) do
      %Token{type: type} when type in [:eof, :dedent, :newline] ->
        state

      %Token{type: :keyword, value: kw} when kw in @definition_keywords ->
        state

      _ ->
        synchronize_to_statement(advance(state))
    end
  end

  # -- Doc Comment Helpers -----------------------------------------------------

  defp collect_doc_comments(state) do
    collect_doc_comments(state, [], nil)
  end

  # Collect a contiguous run of `:doc_comment` tokens, using the source
  # line numbers already on the tokens to break on a blank-line gap.
  # Blank lines don't produce tokens (the lexer eats them silently), so
  # consecutive doc comments appear adjacent in the stream; compare
  # their source lines to tell `## foo\n## bar` (adjacent, line delta 1
  # for single-line `##` tokens) from `## foo\n\n## bar` (separated,
  # line delta 2+). A gap terminates the run so the next `##` block
  # binds to the following definition rather than to the leading doc.
  #
  # Split into two clauses so the integer arithmetic on `prev_line` is
  # never evaluated against `nil`; dialyzer (rightly) rejects
  # `line - prev_line` in the combined-guard form because it narrows
  # `prev_line` to `nil` across the first entry call.
  defp collect_doc_comments(state, acc, nil) do
    case peek(state) do
      %Token{type: :doc_comment, value: text, line: line} ->
        state = advance(state)
        state = skip_newlines(state)
        collect_doc_comments(state, [text | acc], line)

      _ ->
        doc = acc |> Enum.reverse() |> Enum.join("\n")
        {doc, state}
    end
  end

  defp collect_doc_comments(state, acc, prev_line) when is_integer(prev_line) do
    case peek(state) do
      %Token{type: :doc_comment, value: text, line: line}
      when line - prev_line <= 1 ->
        state = advance(state)
        state = skip_newlines(state)
        collect_doc_comments(state, [text | acc], line)

      _ ->
        doc = acc |> Enum.reverse() |> Enum.join("\n")
        {doc, state}
    end
  end

  # Collect every consecutive `:doc_comment` block, merging blocks
  # separated by blank-line gaps (or by plain `#` comments, which the
  # lexer drops when `preserve_comments: false`) with a paragraph
  # break. Used by `parse_program/2` and `parse_block_body/2` where any
  # leftover doc-comment tokens ahead of the next statement must bind
  # to that statement -- otherwise the parser would try to recurse
  # into `parse_expr/2` on a `:doc_comment` prefix and raise an
  # "unexpected doc_comment" error.
  defp collect_all_doc_comments(state) do
    {first, state} = collect_doc_comments(state)
    collect_all_doc_comments(state, first)
  end

  defp collect_all_doc_comments(state, acc) do
    state_after_ws = skip_newlines(state)

    case peek(state_after_ws) do
      %Token{type: :doc_comment} ->
        {next, state_after_ws} = collect_doc_comments(state_after_ws)

        merged =
          case {acc, next} do
            {"", n} -> n
            {a, ""} -> a
            {a, n} -> a <> "\n\n" <> n
          end

        collect_all_doc_comments(state_after_ws, merged)

      _ ->
        {acc, state}
    end
  end

  defp attach_doc({type, meta, children}, doc) when is_list(meta) do
    {type, Keyword.put(meta, :doc, doc), children}
  end

  defp attach_doc(ast, _doc), do: ast

  # -- Line Comment Helper ----------------------------------------------------

  # Consume a `:line_comment` token and return an AST node.
  # Emits `{:comment, [line: n, col: c], text}` so downstream consumers
  # (the algebra formatter, documentation tools) can reproduce the
  # comment in source order. Plain `#` comments preserved this way are
  # never attached as `:doc` metadata; they remain free-standing nodes.
  defp consume_line_comment(state) do
    token = peek(state)
    meta = [line: token.line, col: token.col]
    node = {:comment, meta, token.value}
    {node, advance(state)}
  end
end
