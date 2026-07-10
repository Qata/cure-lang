defmodule Cure.Compiler.Printer do
  @moduledoc """
  Converts a MetaAST tree back into Cure source code.

  This is the inverse of `Cure.Compiler.Parser`. Given a well-formed MetaAST
  (the `{type, keyword_meta, children_or_value}` 3-tuples produced by the
  parser), it emits a Cure source string that round-trips through the
  lexer/parser pipeline.

  ## Options

  - `:indent` -- indentation unit (default: `"  "`)
  """

  @default_indent "  "

  # Reserved words (keywords + operator words) that lex as non-identifier
  # tokens. A definition or reference that uses one of these as an ordinary
  # name must be re-emitted backtick-quoted (`` `not` ``) to round-trip, since
  # the lexer only yields them as an `:identifier` inside backticks.
  @reserved_words ~w(
    mod fn let type typealias indexed indices rec proto impl fsm local use as
    interface implementation deriving
    match pickup if elif else then for do end
    in try catch finally throw return yield
    spawn send receive after
    actor
    when where and or not
    true false nil
    extern proof
  )

  # Spec-defined formatting parameters (PICKUP §8.7 / MATCH §9.7).
  # Aligned form is dropped if the longest clause head exceeds the
  # alignment limit, falling back to the unaligned form. Wrapping is
  # triggered by either a multi-line right-hand side or a final
  # rendered line exceeding `max_line_width`.
  @alignment_limit 40
  @max_line_width 100

  @doc """
  Render a MetaAST node as a Cure source string.
  """
  @spec quoted_to_string(term(), keyword()) :: String.t()
  def quoted_to_string(ast, opts \\ []) do
    indent = Keyword.get(opts, :indent, @default_indent)

    case ast do
      # The outermost node of a multi-definition file is the program's
      # top-level statement list. Apply the §5.4 top-of-file policy here (rule 3:
      # exactly one blank line between every top-level definition; rule 1: no
      # leading blanks) — NOT in the generic `{:block, …}` clause, because a
      # function body is also a `:block` and may itself render at depth 0.
      {:block, meta, exprs} -> render_program(exprs, meta, indent)
      _ -> render(ast, 0, indent)
    end
  end

  # Render the whole-file statement list, then re-apply the *block's own* trivia:
  # a `:leading` comment at the very top of the file, a `:trailing` comment on the
  # file's last line (a genuine end-of-file trailing comment — spec §5.2 forbids
  # dropping it), and any `:trailer` lines after the last statement. All three
  # helpers no-op on `nil`, and blank runs render to nothing, so a file whose
  # block carries no trivia (the corpus fixpoint gate, and every file the plain
  # Printer sees) is byte-identical to before.
  defp render_program(exprs, meta, indent) do
    body =
      exprs
      |> flatten_top_level()
      |> Enum.map(&render(&1, 0, indent))
      |> Enum.with_index()
      |> Enum.map(fn {rendered, i} -> {rendered, i > 0} end)
      |> join_statements("")

    body
    |> prepend_leading(Keyword.get(meta, :leading), 0, indent)
    |> append_trailing(Keyword.get(meta, :trailing))
    |> append_trailer(Keyword.get(meta, :trailer), 0, indent)
  end

  # A bare `mod Name` header leaves its sibling definitions wrapped in a single
  # `:block` node. That wrapper has NO surface syntax (it renders as a plain
  # statement list) and is dropped on reparse — the definitions become top-level
  # siblings. Flatten it here so the §5.4 top-of-file rule-3 blank policy sees the
  # same statement set the reparse will; otherwise `print∘reparse∘print` inserts
  # blanks the first print did not, and the corpus fixpoint gate fails. The
  # wrapper's OWN trivia (a section-header comment attached to the block's
  # `:leading`, a `:trailer` after its last statement) is carried onto the edge
  # statements so flattening the syntax-less wrapper loses no comment.
  defp flatten_top_level(exprs) do
    Enum.flat_map(exprs, fn
      {:block, bmeta, inner} when is_list(inner) and inner != [] ->
        inner |> flatten_top_level() |> carry_block_trivia(bmeta)

      other ->
        [other]
    end)
  end

  defp carry_block_trivia(inner, bmeta) do
    inner
    |> prepend_node_trivia(:leading, Keyword.get(bmeta, :leading))
    |> append_node_trivia(:trailer, Keyword.get(bmeta, :trailer))
    |> append_node_trivia(:trailing, Keyword.get(bmeta, :trailing))
  end

  defp prepend_node_trivia(list, _key, nil), do: list

  defp prepend_node_trivia([{tag, meta, ch} | rest], key, items) when is_list(meta),
    do: [{tag, Keyword.update(meta, key, items, &(items ++ &1)), ch} | rest]

  defp prepend_node_trivia(list, _key, _items), do: list

  defp append_node_trivia(list, _key, nil), do: list

  defp append_node_trivia(list, key, items) when is_list(items) and items != [] do
    case List.pop_at(list, -1) do
      {{tag, meta, ch}, front} when is_list(meta) ->
        front ++ [{tag, Keyword.update(meta, key, items, &(&1 ++ items)), ch}]

      _ ->
        list
    end
  end

  defp append_node_trivia(list, _key, _items), do: list

  # Render a block body / statement list applying §5.4 rule 4: a single author
  # blank between two statements is preserved (a run capped at 1), signalled by a
  # `:blank` item in either the preceding statement's `:trailer` or the following
  # statement's `:leading`; blanks adjacent to the block's open/close are dropped
  # (never injected before the first or after the last statement). `child_depth`
  # is the depth at which the statements render; the caller supplies the leading
  # pad for the first line. With no trivia attached (e.g. the corpus fixpoint
  # gate) every `blank?` is false, so output is byte-identical to a plain
  # "\n"<>pad join.
  defp render_stmt_list(exprs, child_depth, indent) do
    pad = String.duplicate(indent, child_depth)

    case exprs do
      [] ->
        ""

      [only] ->
        coerce(render(only, child_depth, indent))

      [first | rest] ->
        {pairs, _prev} =
          Enum.reduce(rest, {[{render(first, child_depth, indent), false}], first}, fn e,
                                                                                       {acc, prev} ->
            blank? = trailer_blank?(prev) or leading_blank?(e)
            {[{render(e, child_depth, indent), blank?} | acc], e}
          end)

        join_statements(Enum.reverse(pairs), pad)
    end
  end

  # Join rendered statements, inserting exactly one blank line before any
  # statement flagged `blank?` (§5.4 rules 3/4). `pad` indents each statement
  # after the first; the blank line itself is emitted empty. Elements are
  # coerced to strings (mirroring `Enum.join`), since a stray keyword-named
  # `:variable` renders to a bare atom (e.g. a dangling `end`).
  defp join_statements([], _pad), do: ""

  defp join_statements([{first, _} | rest], pad) do
    Enum.reduce(rest, coerce(first), fn {rendered, blank?}, acc ->
      sep = if blank?, do: "\n\n" <> pad, else: "\n" <> pad
      acc <> sep <> coerce(rendered)
    end)
  end

  defp coerce(s) when is_binary(s), do: s
  defp coerce(other), do: Kernel.to_string(other)

  # True when a node carries a blank-run item in its attached `:leading` /
  # `:trailer` trivia, respectively.
  defp leading_blank?(node), do: has_blank?(trivia_meta(node), :leading)
  defp trailer_blank?(node), do: has_blank?(trivia_meta(node), :trailer)

  defp has_blank?(meta, key) do
    case Keyword.get(meta, key) do
      nil -> false
      items -> Enum.any?(items, &match?({:blank, _, _}, &1))
    end
  end

  # -- Trivia-aware dispatch wrapper ------------------------------------------
  #
  # Every node is rendered through this single `render/3` clause, which
  # delegates the actual syntax to the per-kind `to_string/3` clauses and then
  # layers on any attached trivia (spec §5.2 / §5.4): `:leading` comment lines
  # emitted (each at the node's own indent) before the node, `:trailing`
  # comments appended on the node's own line, and `:trailer` lines emitted
  # after the node at the node's indent. Every recursive child render also goes
  # through `render/3`, so trivia is applied uniformly at every depth.
  #
  # CRITICAL: when a node carries NONE of `:leading` / `:trailing` /
  # `:trailer`, this returns the per-kind `to_string/3` output byte-for-byte.
  # An AST printed without `Trivia.attach/2` (e.g. the corpus fixpoint gate)
  # has no trivia keys anywhere, so its output is identical to the pre-trivia
  # Printer.
  defp render(node, depth, indent) do
    meta = trivia_meta(node)
    leading = Keyword.get(meta, :leading)
    trailing = Keyword.get(meta, :trailing)
    trailer = Keyword.get(meta, :trailer)

    if leading == nil and trailing == nil and trailer == nil do
      to_string(node, depth, indent)
    else
      to_string(node, depth, indent)
      |> prepend_leading(leading, depth, indent)
      |> append_trailing(trailing)
      |> append_trailer(trailer, depth, indent)
    end
  end

  defp trivia_meta({_k, meta, _}) when is_list(meta), do: meta
  defp trivia_meta({_k, meta, _, _}) when is_list(meta), do: meta
  defp trivia_meta(_), do: []

  # `:leading` items become full lines emitted before the node. The first line
  # takes the pad supplied by the parent join site; every subsequent line (and
  # the node itself) is re-padded here. Blank lines are emitted empty.
  defp prepend_leading(rendered, nil, _depth, _indent), do: rendered

  defp prepend_leading(rendered, items, depth, indent) do
    pad = String.duplicate(indent, depth)

    case Enum.flat_map(items, &trivia_lines/1) do
      [] ->
        rendered

      [first | rest] ->
        rest_str = Enum.map_join(rest, "", fn l -> "\n" <> pad_or_empty(l, pad) end)
        first <> rest_str <> "\n" <> pad <> rendered
    end
  end

  # `:trailing` comments sit on the node's own final line.
  defp append_trailing(rendered, nil), do: rendered

  defp append_trailing(rendered, items) do
    Enum.reduce(items, rendered, fn item, acc -> acc <> "  " <> comment_text(item) end)
  end

  # `:trailer` items become full lines after the node, at the node's indent.
  defp append_trailer(rendered, nil, _depth, _indent), do: rendered

  defp append_trailer(rendered, items, depth, indent) do
    pad = String.duplicate(indent, depth)

    items
    |> Enum.flat_map(&trivia_lines/1)
    |> Enum.reduce(rendered, fn l, acc -> acc <> "\n" <> pad_or_empty(l, pad) end)
  end

  # Physical lines for a trivia item. Blank runs emit NOTHING: the Trivia
  # classifier attaches a blank to the innermost/deepest container that ends
  # before it (spec §5.2), which is routinely a node buried inside an
  # expression (a call in a cons cell, an operand in a `%[...]` tuple, …).
  # Cure has no way to write a blank line there -- a collection literal cannot
  # span a newline without failing to reparse -- so a blank is dropped rather
  # than emitted into a position that cannot hold it. Comments are never
  # dropped; they attach to statement-level nodes where a full line is legal.
  defp trivia_lines({:blank, _count, _}), do: []
  defp trivia_lines({:comment, text, _, _}), do: ["# " <> text]

  defp trivia_lines({:doc_comment, text, _, _}) do
    text |> String.split("\n") |> Enum.map(&("## " <> &1))
  end

  defp comment_text({:comment, text, _, _}), do: "# " <> text
  defp comment_text({:doc_comment, text, _, _}), do: "## " <> text

  defp pad_or_empty("", _pad), do: ""
  defp pad_or_empty(line, pad), do: pad <> line

  # A comma-separated expression span (map/record pairs, list/tuple elements,
  # call args). Cure has NO multi-line collection literals -- a `[`, `(`, `%{`
  # spanning a newline fails to reparse (the layout lexer emits a DEDENT the
  # bracket parser rejects) -- so a span is always emitted on one line, exactly
  # as before trivia support. Each element is rendered with the per-kind
  # `to_string/3` directly rather than the trivia-aware `render/3`, so an
  # element's OWN attached trivia is skipped (there is no single-line position
  # for a comment or blank there). The element's inner subtree still recurses
  # through `render/3`, so e.g. statement comments inside a lambda body are
  # kept. In the std corpus the only trivia that lands on a span element is a
  # blank run (never a comment), so nothing a lossless reprint must keep is
  # lost. Trivia attached to the span CONTAINER node itself flows normally
  # through `render/3` at the enclosing statement level.
  defp render_span(children, sep, depth, indent) do
    Enum.map_join(children, sep <> " ", &to_string(&1, depth, indent))
  end

  # -- Literals --------------------------------------------------------------

  defp to_string({:literal, meta, value}, _depth, _indent) do
    case Keyword.get(meta, :subtype) do
      :integer -> Integer.to_string(value)
      :float -> float_to_string(value)
      :string -> ~s("#{escape_string(value)}")
      :boolean -> Atom.to_string(value)
      :null -> "nil"
      :symbol -> ":#{value}"
      :regex -> regex_to_string(value)
      :char -> char_to_string(value)
      :bytes -> bytes_to_string(meta, value)
      _ -> inspect(value)
    end
  end

  # -- Variables -------------------------------------------------------------

  defp to_string({:variable, _meta, name}, _depth, _indent), do: name

  # -- Block -----------------------------------------------------------------

  # A block body (§5.4 rule 4): cap blank runs at 1 and trim blanks adjacent to
  # the block's open/close; otherwise preserve the author's single blank between
  # two statements. A blank between statements S[i-1] and S[i] is attached (per
  # the Trivia classifier) to *either* S[i-1]'s `:trailer` or S[i]'s `:leading`,
  # so we check both sides of each pair. A run of N blanks is one `:blank` item,
  # so this caps at exactly one line; blanks adjacent to open/close attach to the
  # block/last-statement and are dropped here (never injected before the first or
  # after the last statement). With no trivia attached (e.g. the corpus fixpoint
  # gate), every `blank?` is false, so output is byte-identical to a plain
  # "\n"<>pad join.
  defp to_string({:block, _meta, exprs}, depth, indent) do
    render_stmt_list(exprs, depth, indent)
  end

  # -- Binary Operators ------------------------------------------------------

  defp to_string({:binary_op, meta, [left, right]}, depth, indent) do
    op = Keyword.get(meta, :operator)
    op_str = operator_to_string(op)
    parent = op_prec(op)
    left_s = operand_str(left, depth, indent, parent, :left)
    right_s = operand_str(right, depth, indent, parent, :right)
    "#{left_s} #{op_str} #{right_s}"
  end

  # -- Unary Operators -------------------------------------------------------

  defp to_string({:unary_op, meta, [operand]}, depth, indent) do
    op = Keyword.get(meta, :operator)
    # A prefix operator binds at level 90 (see the precedence table below): its
    # operand needs parentheses whenever it is a lower-precedence expression, or
    # `-(x + 1)` would reprint as `-x + 1` (= `(-x) + 1`) and `not (a and b)` as
    # `not a and b` (= `(not a) and b`) — both meaning-changing.
    inner = operand_str(operand, depth, indent, {90, :right}, :right)

    case op do
      :not -> "not #{inner}"
      :- -> "-#{inner}"
      _ -> "#{op}#{inner}"
    end
  end

  # -- Assignment (let binding) -----------------------------------------------

  defp to_string({:assignment, meta, [pattern, value]}, depth, indent) do
    type_ann =
      case Keyword.get(meta, :type_annotation) do
        nil -> ""
        type_ast -> ": #{render(type_ast, depth, indent)}"
      end

    lhs = render(pattern, depth, indent)
    rhs = rhs_to_string(value, depth, indent)

    if Keyword.get(meta, :let) do
      "let #{lhs}#{type_ann} = #{rhs}"
    else
      "#{lhs} = #{rhs}"
    end
  end

  # -- Augmented Assignment --------------------------------------------------

  defp to_string({:augmented_assignment, meta, [lhs, rhs]}, depth, indent) do
    op = Keyword.get(meta, :operator)

    op_str =
      case op do
        :+ -> "+="
        :- -> "-="
        :* -> "*="
        :/ -> "/="
      end

    "#{render(lhs, depth, indent)} #{op_str} #{render(rhs, depth, indent)}"
  end

  # -- Conditional -----------------------------------------------------------

  defp to_string({:conditional, _meta, [condition, then_br, else_br]}, depth, indent) do
    cond_str = render(condition, depth, indent)

    case {then_br, else_br} do
      {_, {:literal, [subtype: :null], nil}} ->
        # No else branch
        "if #{cond_str} then #{render(then_br, depth, indent)}"

      {_, {:conditional, _, _}} ->
        # elif chain
        then_str = render(then_br, depth, indent)
        elif_str = conditional_to_elif(else_br, depth, indent)
        "if #{cond_str} then #{then_str} #{elif_str}"

      _ ->
        then_str = render(then_br, depth, indent)
        else_str = render(else_br, depth, indent)
        "if #{cond_str} then #{then_str} else #{else_str}"
    end
  end

  # -- Pattern Match (MATCH §9 -- Canonical Block Form) ---------------------
  #
  # Per the formal spec (`docs/MATCH.md` §9), the canonical surface form
  # of a `match` expression is a block: the keyword and its scrutinee on
  # one line, followed by clauses indented one `indent_step` deeper. The
  # `->` tokens are aligned within a single block (§9.2, §9.14).
  #
  # Single-clause matches whose pattern is irrefutable are rewritten to
  # the equivalent `let` binding (MATCH §9.6, hint H-MATCH-USE-LET).
  # Multi-line right-hand sides force every clause in the block into the
  # wrapped form (§9.9).

  defp to_string({:pattern_match, _meta, [scrutinee | arms]}, depth, indent) do
    cond do
      arms == [] ->
        # An empty `match` is malformed (E-MATCH-EMPTY), but the
        # printer must still produce some surface text so type-checker
        # diagnostics can attach to the keyword.
        "match #{render(scrutinee, depth, indent)}"

      true ->
        # MATCH §9.6 also describes a single-arm-irrefutable -> `let`
        # rewrite hint (`H-MATCH-USE-LET`). Since Cure's surface has no
        # `let … in …` form, the canonical printer leaves the `match`
        # unchanged here; a dedicated formatter pass may surface the
        # rewrite hint without altering the AST.
        render_match_block(scrutinee, arms, depth, indent)
    end
  end

  # -- Pickup (PICKUP §8 -- Canonical Block Form) ---------------------------
  #
  # Per the formal spec (`docs/PICKUP.md` §8), the canonical surface
  # form of a `pickup` expression is a block: the keyword on its own
  # line, followed by clauses indented one `indent_step` deeper. The
  # `->` tokens are aligned within a single block (§8.2, §8.14).
  #
  # A degenerate `pickup` -- whose only clause is the terminator -- is
  # rewritten to the body expression (§8.6, hint H-PICKUP-DEGENERATE).
  # A trailing `true ->` clause is normalised to `else ->` (§8.3, hint
  # H-PICKUP-PREFER-ELSE). Multi-line right-hand sides force every
  # clause into the wrapped form (§8.9).

  defp to_string({:pickup, _meta, clauses}, depth, indent) do
    clauses = normalize_pickup_terminator(clauses)

    case clauses do
      [{:pickup_else, _, [body]}] ->
        # PICKUP §8.6: degenerate `pickup` -- single terminator only --
        # collapses to the body.
        render(body, depth, indent)

      [] ->
        # The parser rejects this with E-PICKUP-NO-ELSE; for
        # defensive printing we still emit the keyword.
        "pickup"

      _ ->
        render_pickup_block(clauses, depth, indent)
    end
  end

  # -- Match Arm -------------------------------------------------------------

  defp to_string({:match_arm, meta, [body]}, depth, indent) do
    match_arm_to_string({:match_arm, meta, [body]}, depth, indent)
  end

  # Inline pickup clauses are not normally rendered on their own (the
  # `:pickup` clause above always handles them as a list), but we keep a
  # safe fallback so trees produced by macro expansion or partial
  # quoting still print legibly.
  defp to_string({:pickup_clause, _meta, [guard, body]}, depth, indent) do
    "#{render(guard, depth, indent)} -> #{render(body, depth, indent)}"
  end

  defp to_string({:pickup_else, _meta, [body]}, depth, indent) do
    "else -> #{render(body, depth, indent)}"
  end

  # -- Function Call ---------------------------------------------------------

  defp to_string({:function_call, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name, "unknown")

    cond do
      # Record construction: Name{field: val}
      Keyword.get(meta, :record) == true ->
        fields_str = pairs_to_string(args, depth, indent)
        "#{name}{#{fields_str}}"

      # Send: send target, message
      name == "send" and not Keyword.has_key?(meta, :pipe) ->
        case args do
          [target, message] ->
            "send #{render(target, depth, indent)}, #{render(message, depth, indent)}"

          _ ->
            "#{name}(#{args_to_string(args, depth, indent)})"
        end

      # FSM transition
      Keyword.get(meta, :from) != nil ->
        fsm_transition_to_string(meta, depth, indent)

      # Pipe call. `|>` binds loosest (level 10, left-assoc), so a left operand
      # whose own precedence is lower — a bare `<-|` send, a conditional — must
      # be parenthesised or the reprint reparses differently.
      Keyword.get(meta, :pipe) == true ->
        pipe_parent = {10, :left}

        case args do
          [piped | rest] when rest != [] ->
            "#{operand_str(piped, depth, indent, pipe_parent, :left)} |> #{name}(#{args_to_string(rest, depth, indent)})"

          [piped] ->
            "#{operand_str(piped, depth, indent, pipe_parent, :left)} |> #{name}"

          [] ->
            name
        end

      true ->
        "#{quote_if_reserved(name)}(#{args_to_string(args, depth, indent)})"
    end
  end

  # -- Record Update ----------------------------------------------------------

  defp to_string({:record_update, meta, [base | fields]}, depth, indent) do
    name = Keyword.get(meta, :name)
    base_str = render(base, depth, indent)
    fields_str = pairs_to_string(fields, depth, indent)
    "#{name}{#{base_str} | #{fields_str}}"
  end

  # -- Attribute Access (dot) ------------------------------------------------

  defp to_string({:attribute_access, meta, [parent]}, depth, indent) do
    attr = Keyword.get(meta, :attribute)
    # Dot access binds at level 100 (highest); a lower-precedence base needs
    # parens or `(a + b).x` reprints as `a + b.x` (= `a + (b.x)`).
    "#{operand_str(parent, depth, indent, {100, :left}, :left)}.#{attr}"
  end

  # -- Range -----------------------------------------------------------------

  defp to_string({:range, meta, [left, right]}, depth, indent) do
    op = if Keyword.get(meta, :inclusive), do: "..=", else: ".."
    # Range binds at level 50 (non-associative); operands that bind looser need
    # parens or `(a == b)..c` reprints as `a == b..c` (= `a == (b .. c)`).
    parent = {50, :none}

    "#{operand_str(left, depth, indent, parent, :left)}#{op}#{operand_str(right, depth, indent, parent, :right)}"
  end

  # -- Collections -----------------------------------------------------------

  defp to_string({:list, meta, elements}, depth, indent) do
    if Keyword.get(meta, :cons) do
      case elements do
        [head, tail] ->
          "[#{render(head, depth, indent)} | #{render(tail, depth, indent)}]"

        _ ->
          "[#{args_to_string(elements, depth, indent)}]"
      end
    else
      "[#{args_to_string(elements, depth, indent)}]"
    end
  end

  defp to_string({:tuple, meta, elements}, depth, indent) do
    # A tuple in TYPE position (`(A, B)`, e.g. `List((String, String))`) is
    # parsed with empty meta, whereas a VALUE tuple `%[a, b]` carries the
    # lexer's line/col. Render each back in its own surface syntax so a type
    # tuple round-trips as `(A, B)` rather than the value form `%[A, B]`
    # (which is not valid in a type position).
    if meta == [] do
      "(#{args_to_string(elements, depth, indent)})"
    else
      "%[#{args_to_string(elements, depth, indent)}]"
    end
  end

  defp to_string({:map, _meta, pairs}, depth, indent) do
    "%{#{pairs_to_string(pairs, depth, indent)}}"
  end

  defp to_string({:pair, _meta, [key, value]}, depth, indent) do
    pair_to_string(key, value, depth, indent)
  end

  # -- Comprehension ---------------------------------------------------------

  defp to_string({:comprehension, _meta, [body | generators_and_filters]}, depth, indent) do
    body_str = render(body, depth, indent)
    clauses = Enum.map(generators_and_filters, &gen_or_filter_to_string(&1, depth, indent))
    "[#{body_str} for #{Enum.join(clauses, ", ")}]"
  end

  defp to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    gen_or_filter_to_string({:generator, [], [pattern, collection]}, depth, indent)
  end

  defp to_string({:filter, _meta, [expr]}, depth, indent) do
    gen_or_filter_to_string({:filter, [], [expr]}, depth, indent)
  end

  # -- String Interpolation --------------------------------------------------

  defp to_string({:string_interpolation, _meta, parts}, depth, indent) do
    inner =
      Enum.map_join(parts, fn
        {:literal, [subtype: :string], s} -> escape_string(s)
        {:literal, _, s} when is_binary(s) -> escape_string(s)
        expr -> "\#{#{render(expr, depth, indent)}}"
      end)

    ~s("#{inner}")
  end

  # -- Lambda ----------------------------------------------------------------

  defp to_string({:lambda, meta, [body]}, depth, indent) do
    params = Keyword.get(meta, :params, [])
    params_str = Enum.map_join(params, ", ", fn {:param, _, name} -> name end)
    body_str = lambda_body_to_string(body, depth, indent)
    "fn(#{params_str}) -> #{body_str}"
  end

  # -- Function Definition ---------------------------------------------------

  defp to_string({:function_def, meta, body}, depth, indent) do
    fn_def_to_string(meta, body, depth, indent)
  end

  # -- Container (module, record, enum, protocol, trait, fsm) ----------------

  defp to_string({:container, meta, body}, depth, indent) do
    container_to_string(meta, body, depth, indent)
  end

  # -- Type Annotation -------------------------------------------------------

  defp to_string({:type_annotation, meta, children}, depth, indent) do
    type_annotation_to_string(meta, children, depth, indent)
  end

  # -- Import ----------------------------------------------------------------

  defp to_string({:import, meta, _children}, _depth, _indent) do
    source = Keyword.get(meta, :source)
    items = Keyword.get(meta, :items)
    alias_name = Keyword.get(meta, :alias)

    base = "use #{source}"

    base =
      if items && items != [] do
        base <> ".{#{Enum.join(items, ", ")}}"
      else
        base
      end

    if alias_name do
      base <> " as #{alias_name}"
    else
      base
    end
  end

  # -- Early Return / Throw / Yield / Spawn ---------------------------------

  defp to_string({:early_return, _meta, [expr]}, depth, indent) do
    "return #{render(expr, depth, indent)}"
  end

  # Melquiades send node. The author's chosen surface form is carried on
  # meta[:melquiades_form]:
  #
  #   :ascii    -> `target <-| message`
  #   :unicode  -> `target ✉ message`
  #   :keyword  -> `send target, message` (the statement form)
  #
  # Any other value falls back to the ASCII operator form.
  defp to_string({:send, meta, [target, message]}, depth, indent) do
    # The Melquiades send operator binds at level 8 (non-associative); operands
    # that bind looser need parens or `(pid <-| msg) + 1` reprints as
    # `pid <-| msg + 1` (= `pid <-| (msg + 1)`).
    parent = {8, :none}
    target_str = operand_str(target, depth, indent, parent, :left)
    message_str = operand_str(message, depth, indent, parent, :right)

    case Keyword.get(meta, :melquiades_form, :ascii) do
      :unicode -> "#{target_str} ✉ #{message_str}"
      :keyword -> "send #{target_str}, #{message_str}"
      _ -> "#{target_str} <-| #{message_str}"
    end
  end

  defp to_string({:throw, _meta, [expr]}, depth, indent) do
    "throw #{render(expr, depth, indent)}"
  end

  defp to_string({:yield, _meta, [expr]}, depth, indent) do
    "yield #{render(expr, depth, indent)}"
  end

  defp to_string({:async_operation, meta, children}, depth, indent) do
    case Keyword.get(meta, :timeout) do
      nil when children == [] ->
        "receive"

      nil ->
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"

      _ ->
        # receive with timeout
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"
    end
  end

  # -- Exception Handling ----------------------------------------------------

  defp to_string({:exception_handling, _meta, children}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    case children do
      [try_body | rest] ->
        try_str = "try\n#{pad}#{render(try_body, depth + 1, indent)}"

        {catch_arms, rest} =
          Enum.split_while(rest, fn
            {:match_arm, _, _} -> true
            _ -> false
          end)

        catch_str =
          if catch_arms != [] do
            arms =
              catch_arms
              |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
              |> Enum.join("\n#{pad}")

            "\ncatch\n#{pad}#{arms}"
          else
            ""
          end

        finally_str =
          case rest do
            [finally_body] ->
              "\nfinally\n#{pad}#{render(finally_body, depth + 1, indent)}"

            _ ->
              ""
          end

        "#{try_str}#{catch_str}#{finally_str}"

      _ ->
        "try"
    end
  end

  # -- Decorator / Property --------------------------------------------------

  defp to_string({:decorator, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name)
    "@#{name}(#{args_to_string(args, depth, indent)})"
  end

  defp to_string({:property, meta, _value}, _depth, _indent) do
    name = Keyword.get(meta, :name)
    "@#{name}"
  end

  # -- Line comment ----------------------------------------------------------

  defp to_string({:comment, _meta, text}, _depth, _indent) when is_binary(text) do
    # v0.20.0: free-standing `#` comment nodes round-trip as `# <text>`.
    "# " <> text
  end

  # -- Binary segment --------------------------------------------------------
  #
  # Round-trips the v0.20.0 segment AST back into surface syntax.
  # A segment with no specifiers renders as the plain value; otherwise
  # the specifier chain is emitted as `::type-signedness-endianness-size-unit`.

  defp to_string({:bin_segment, meta, [value]}, depth, indent) do
    value_str = render(value, depth, indent)
    spec_str = bin_segment_specifier_string(meta, depth, indent)

    if spec_str == "" do
      value_str
    else
      "#{value_str}::#{spec_str}"
    end
  end

  # -- Pin pattern (v0.18.0) -------------------------------------------------
  #
  # `^name` references a previously-bound variable in a pattern rather than
  # rebinding it.

  defp to_string({:pin, _meta, [inner]}, depth, indent) do
    "^" <> render(inner, depth, indent)
  end

  # -- As-pattern (`name @ inner`) -------------------------------------------
  #
  # Binds the whole matched value to `name` in addition to destructuring it.
  # The name is a bare string; the inner is the destructuring pattern.

  defp to_string({:as_pattern, _meta, [name, inner]}, depth, indent) when is_binary(name) do
    name <> " @ " <> render(inner, depth, indent)
  end

  # -- Forced (dot) pattern (`.x` / `.(compound)`) ---------------------------
  #
  # A leading `.` marks a forced-equation pattern: the inner term is a value
  # the scrutinee must be convertible with, not a fresh binder. A bare
  # variable/literal prints as `.x`; anything compound prints as `.(...)`.

  defp to_string({:forced_pattern, _meta, inner}, depth, indent) do
    inner_str = render(inner, depth, indent)

    case inner do
      {:variable, _, _} -> "." <> inner_str
      {:literal, _, _} -> "." <> inner_str
      _ -> ".(" <> inner_str <> ")"
    end
  end

  # -- Named-implicit dot pattern (`{ name = inner }`) -----------------------
  #
  # Annotates a constructor's erased implicit index `name` with a forced
  # value in a pattern-argument position. This is a 4-tuple node, not the
  # standard `{tag, meta, children}` shape.

  defp to_string({:named_implicit_pat, _meta, name, inner}, depth, indent) do
    "{ " <> name <> " = " <> render(inner, depth, indent) <> " }"
  end

  # -- Hole (`?name` / `??`) -------------------------------------------------
  #
  # A deferred term that reports its goal type. The lexer stores the anonymous
  # hole `??` with name `"?"`; a named hole keeps its bare name.

  defp to_string({:hole, meta, _children}, _depth, _indent) do
    case Keyword.get(meta, :name) do
      "?" -> "??"
      name -> "?" <> name
    end
  end

  # -- assert_type (`assert_type expr : Type`) -------------------------------

  defp to_string({:assert_type, _meta, [expr, type_ast]}, depth, indent) do
    "assert_type " <> render(expr, depth, indent) <> " : " <> render(type_ast, depth, indent)
  end

  # -- Dependent function type (Π) -------------------------------------------
  #
  # `(x: A, B) -> C` — at least one named domain. `binders` carries one entry
  # per domain (nil for an anonymous domain); the children are the domains
  # followed by the codomain.

  defp to_string({:pi_type, meta, children}, depth, indent) do
    binders = Keyword.get(meta, :binders, [])
    {doms, [ret]} = Enum.split(children, length(children) - 1)

    dom_strs =
      binders
      |> Enum.zip(doms)
      |> Enum.map(fn
        {nil, d} -> render(d, depth, indent)
        {name, d} -> "#{name}: #{render(d, depth, indent)}"
      end)

    "(" <> Enum.join(dom_strs, ", ") <> ") -> " <> render(ret, depth, indent)
  end

  # -- Dependent pair type (Σ) -----------------------------------------------
  #
  # `Sigma(x: DomType, BodyType)`.

  defp to_string({:sigma_type, meta, [dom_type, body_type]}, depth, indent) do
    binder = Keyword.get(meta, :binder)

    "Sigma(" <>
      binder <>
      ": " <>
      render(dom_type, depth, indent) <>
      ", " <> render(body_type, depth, indent) <> ")"
  end

  # -- GADT constructor signature --------------------------------------------
  #
  # `Name : Dom -> ... -> Result`. The third slot is a single `{:arrow_chain,
  # [...]}` tuple (NOT a children list). A `:named_dom` element carries a
  # dependent binder `(name: Type)` where the 2nd position is a bare string;
  # both `:arrow_chain` and `:named_dom` are rendered here, never as their own
  # dispatch targets.

  defp to_string({:gadt_ctor, meta, {:arrow_chain, elems}}, depth, indent) do
    name = Keyword.get(meta, :name)

    chain =
      Enum.map_join(elems, " -> ", fn
        {:named_dom, dname, inner} -> "(#{dname}: #{render(inner, depth, indent)})"
        other -> render(other, depth, indent)
      end)

    "#{name} : #{chain}"
  end

  # -- Indexed (GADT) type family --------------------------------------------
  #
  # `type Name[(params)] indices (indices)` followed by an indented block of
  # GADT constructor signatures. A `@builtin(:key)`-style decorator threaded
  # into `meta[:decorator]` prints on the preceding line.

  defp to_string({:indexed_type, meta, ctors}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])
    indices = Keyword.get(meta, :indices, [])

    params_str =
      if params == [], do: "", else: "(#{typed_params_to_string(params, depth, indent)})"

    header = "type #{name}#{params_str} indices (#{typed_params_to_string(indices, depth, indent)})"
    body_pad = String.duplicate(indent, depth + 1)

    ctors_str =
      ctors
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{body_pad}")

    type_block = "#{header}\n#{body_pad}#{ctors_str}"

    case Keyword.get(meta, :decorator) do
      nil ->
        type_block

      {dec_name, args} ->
        self_pad = String.duplicate(indent, depth)
        "@#{dec_name}(#{args_to_string(args, depth, indent)})\n#{self_pad}#{type_block}"
    end
  end

  # -- Interface (typeclass declaration) -------------------------------------
  #
  # `interface Name[(params)]` followed by an indented block of method
  # signatures / defaults.

  defp to_string({:interface, meta, body}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])

    params_str = if params == [], do: "", else: "(#{Enum.join(params, ", ")})"
    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "interface #{name}#{params_str}\n#{pad}#{body_str}"
  end

  # -- Implementation (typeclass instance) -----------------------------------
  #
  # `implementation Iface for Type [as Name] [where constraints]` followed by
  # an indented block of method definitions.

  defp to_string({:implementation, meta, body}, depth, indent) do
    iface = Keyword.get(meta, :interface)
    for_type = Keyword.get(meta, :for_type)
    as_name = Keyword.get(meta, :as)
    constraints = Keyword.get(meta, :constraints, [])

    as_str = if as_name, do: " as #{as_name}", else: ""

    where_str =
      if constraints != [] do
        " where " <> Enum.map_join(constraints, ", ", &render(&1, depth, indent))
      else
        ""
      end

    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    head =
      "implementation #{iface} for #{render(for_type, depth, indent)}#{as_str}#{where_str}"

    "#{head}\n#{pad}#{body_str}"
  end

  # -- With-abstraction (capability A) ---------------------------------------
  #
  # `with <scrut> [proof <name>]` with match arms, refining the goal by the
  # scrutinee's value. Rendered like `match` but with the `with` keyword.

  defp to_string({:with_abs, meta, [scrutinee | arms]}, depth, indent) do
    proof = Keyword.get(meta, :proof)
    proof_str = if proof, do: " proof #{proof}", else: ""

    case arms do
      [] -> "with " <> render(scrutinee, depth, indent) <> proof_str
      _ -> render_scrutinee_block("with ", scrutinee, proof_str, arms, depth, indent)
    end
  end

  # -- Supervisor child spec -------------------------------------------------
  #
  # `[sup ]Module as id [(restart: :x, shutdown: N)]`. All data lives in meta;
  # `meta[:kind]` is `:supervisor` (prefix `sup `) or `:worker` (no prefix).

  defp to_string({:child_spec, meta, _children}, depth, indent) do
    module = Keyword.get(meta, :module)
    id = Keyword.get(meta, :id)
    kind = Keyword.get(meta, :kind)
    prefix = if kind == :supervisor, do: "sup ", else: ""

    opts = Keyword.drop(meta, [:module, :id, :kind, :line, :col])

    opts_str =
      if opts == [] do
        ""
      else
        inner =
          Enum.map_join(opts, ", ", fn {k, v} -> "#{k}: #{render(v, depth, indent)}" end)

        " (#{inner})"
      end

    "#{prefix}#{module} as #{id}#{opts_str}"
  end

  # -- Binary generator (`<<pat <- source>>`) --------------------------------
  #
  # A comprehension qualifier that iterates a bitstring. The pattern is a
  # bytes literal whose segments are rendered inline between `<<` and `<-`.

  defp to_string({:binary_generator, _meta, [pattern, source]}, depth, indent) do
    pat_inner =
      case pattern do
        {:literal, _, segs} when is_list(segs) ->
          Enum.map_join(segs, ", ", &render(&1, depth, indent))

        _ ->
          render(pattern, depth, indent)
      end

    "<<" <> pat_inner <> " <- " <> render(source, depth, indent) <> ">>"
  end

  # -- Propositional-equality rewrite (`rewrite proof in body`) --------------

  defp to_string({:rewrite_expr, _meta, [proof, body]}, depth, indent) do
    "rewrite " <> render(proof, depth, indent) <> " in " <> render(body, depth, indent)
  end

  # -- Fallback --------------------------------------------------------------

  defp to_string(other, _depth, _indent) when is_binary(other), do: other

  defp to_string(other, _depth, _indent) do
    raise Cure.Compiler.Printer.UnprintableNodeError, node: other
  end

  # ── Helpers ──────────────────────────────────────────────────────────────

  # v0.22.0: multi-statement bodies carry a `block_shape` in meta. Round-trip
  # the author's chosen shape -- brace (`{...}`) or end-terminated
  # (`stmt1; stmt2; end`). Indented bodies without an explicit shape fall
  # through to the generic `to_string/3` path.
  defp lambda_body_to_string({:block, meta, exprs} = block, depth, indent) do
    case Keyword.get(meta, :block_shape) do
      :brace ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth, indent))
        "{ #{body} }"

      :end ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth, indent))
        "#{body}; end"

      _ ->
        render(block, depth, indent)
    end
  end

  defp lambda_body_to_string(other, depth, indent) do
    render(other, depth, indent)
  end

  defp operator_to_string(:+), do: "+"
  defp operator_to_string(:-), do: "-"
  defp operator_to_string(:*), do: "*"
  defp operator_to_string(:/), do: "/"
  defp operator_to_string(:rem), do: "%"
  defp operator_to_string(:==), do: "=="
  defp operator_to_string(:!=), do: "!="
  defp operator_to_string(:<), do: "<"
  defp operator_to_string(:>), do: ">"
  defp operator_to_string(:<=), do: "<="
  defp operator_to_string(:>=), do: ">="
  defp operator_to_string(:and), do: "and"
  defp operator_to_string(:or), do: "or"
  defp operator_to_string(:<>), do: "<>"
  defp operator_to_string(:..), do: ".."
  defp operator_to_string(:"..="), do: "..="
  defp operator_to_string(:|>), do: "|>"
  defp operator_to_string(:.), do: "."
  defp operator_to_string(:=), do: "="
  defp operator_to_string(other), do: Atom.to_string(other)

  # -- Precedence-aware parenthesisation -------------------------------------
  #
  # The parser is a Pratt parser (Cure.Compiler.Parser.Precedence). Reprinting
  # must re-insert exactly the parentheses needed to recover the SAME parse — no
  # more (over-parenthesising is ugly and breaks the print-fixpoint), no fewer
  # (under-parenthesising silently changes meaning). The table below mirrors
  # Precedence but is keyed by the operator ATOM the printer sees (`:+`) rather
  # than the token type Precedence uses (`:plus`); the two MUST stay in
  # agreement — any precedence change in the parser must be mirrored here.

  # Render `child` as an operand of a parent operator of precedence `parent`
  # (`{level, assoc}` or `:unknown`) on the given `side`, wrapping in parens only
  # when the parse would otherwise change.
  defp operand_str(child, depth, indent, parent, side) do
    s = render(child, depth, indent)
    if needs_parens?(child_prec(child), parent, side), do: "(#{s})", else: s
  end

  # An atomic/primary operand (variable, literal, call, access, …) never needs
  # parens; a control-flow operand (`if`/`match`/lambda/assignment) always does.
  defp needs_parens?(:atom, _parent, _side), do: false
  defp needs_parens?(:lowest, _parent, _side), do: true
  # Unknown parent operator: be conservative and parenthesise any compound child.
  defp needs_parens?(_child, :unknown, _side), do: true

  defp needs_parens?({clevel, _cassoc}, {plevel, passoc}, side) do
    cond do
      clevel < plevel -> true
      clevel > plevel -> false
      # Equal precedence: parens needed unless the child sits on the parent's
      # associative side (`a - b - c` = `(a - b) - c`, so a left child of a
      # left-assoc op needs none; its right child does).
      true -> not associates?(passoc, side)
    end
  end

  defp associates?(:left, :left), do: true
  defp associates?(:right, :right), do: true
  defp associates?(_assoc, _side), do: false

  # Precedence of a child node, as it matters for operand parenthesisation.
  defp child_prec({:binary_op, meta, _}) do
    case op_prec(Keyword.get(meta, :operator)) do
      :unknown -> :lowest
      prec -> prec
    end
  end

  defp child_prec({:unary_op, _meta, _}), do: {90, :right}
  # Infix operators the parser lowers to their own node types (not :binary_op).
  defp child_prec({:range, _meta, _}), do: {50, :none}
  defp child_prec({:send, _meta, _}), do: {8, :none}
  defp child_prec({:attribute_access, _meta, _}), do: {100, :left}
  # `|>` lowers to a pipe-tagged :function_call, binding loosest (level 10); an
  # ordinary call is a primary (atom) and never needs parens.
  defp child_prec({:function_call, meta, _}) do
    if Keyword.get(meta, :pipe) == true, do: {10, :left}, else: :atom
  end

  # Right-extending prefix keywords (`throw`/`yield`/`return`/`spawn`) grab
  # everything to their right, so as a left operand they must be parenthesised.
  defp child_prec({:throw, _meta, _}), do: :lowest
  defp child_prec({:yield, _meta, _}), do: :lowest
  defp child_prec({:early_return, _meta, _}), do: :lowest
  defp child_prec({:async_operation, _meta, _}), do: :lowest
  defp child_prec({:conditional, _meta, _}), do: :lowest
  defp child_prec({:pattern_match, _meta, _}), do: :lowest
  defp child_prec({:pickup, _meta, _}), do: :lowest
  defp child_prec({:lambda, _meta, _}), do: :lowest
  defp child_prec({:assignment, _meta, _}), do: :lowest
  defp child_prec({:augmented_assignment, _meta, _}), do: :lowest
  defp child_prec(_other), do: :atom

  # {level, assoc} per operator atom, mirroring Cure.Compiler.Parser.Precedence.
  defp op_prec(:|>), do: {10, :left}
  defp op_prec(:or), do: {20, :left}
  defp op_prec(:and), do: {30, :left}
  defp op_prec(op) when op in [:==, :!=, :<, :>, :<=, :>=], do: {40, :none}
  defp op_prec(op) when op in [:.., :"..="], do: {50, :none}
  defp op_prec(:<>), do: {60, :right}
  defp op_prec(op) when op in [:+, :-, :bor, :bxor, :bsl, :bsr], do: {70, :left}
  defp op_prec(op) when op in [:*, :/, :rem, :%, :band], do: {80, :left}
  defp op_prec(:.), do: {100, :left}
  defp op_prec(op) when op in [:=, :"+=", :"-=", :"*=", :"/="], do: {5, :right}
  defp op_prec(:melquiades), do: {8, :none}
  defp op_prec(_other), do: :unknown

  defp args_to_string(args, depth, indent) do
    render_span(args, ",", depth, indent)
  end

  defp pairs_to_string(pairs, depth, indent) do
    render_span(pairs, ",", depth, indent)
  end

  defp pair_to_string(key, value, depth, indent) do
    case key do
      {:literal, [subtype: :symbol], atom_val} when is_atom(atom_val) ->
        "#{atom_val}: #{render(value, depth, indent)}"

      _ ->
        "#{render(key, depth, indent)} => #{render(value, depth, indent)}"
    end
  end

  defp match_arm_to_string({:match_arm, meta, [body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)
    pat_str = render(pattern, depth, indent)
    body_str = arm_body_to_string(meta, body, depth, indent)

    if guard do
      "#{pat_str} when #{render(guard, depth, indent)} -> #{body_str}"
    else
      "#{pat_str} -> #{body_str}"
    end
  end

  defp gen_or_filter_to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    "#{render(pattern, depth, indent)} <- #{render(collection, depth, indent)}"
  end

  defp gen_or_filter_to_string({:filter, _meta, [expr]}, depth, indent) do
    render(expr, depth, indent)
  end

  defp gen_or_filter_to_string({:binary_generator, _meta, _} = node, depth, indent) do
    render(node, depth, indent)
  end

  defp conditional_to_elif({:conditional, _meta, [cond_ast, then_br, else_br]}, depth, indent) do
    cond_str = render(cond_ast, depth, indent)
    then_str = render(then_br, depth, indent)

    case else_br do
      {:literal, [subtype: :null], nil} ->
        "elif #{cond_str} then #{then_str}"

      {:conditional, _, _} ->
        "elif #{cond_str} then #{then_str} #{conditional_to_elif(else_br, depth, indent)}"

      _ ->
        "elif #{cond_str} then #{then_str} else #{render(else_br, depth, indent)}"
    end
  end

  defp rhs_to_string({:block, _meta, exprs}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)
    "\n#{pad}" <> render_stmt_list(exprs, depth + 1, indent)
  end

  defp rhs_to_string(ast, depth, indent), do: render(ast, depth, indent)

  # -- Function Definition ---------------------------------------------------

  defp fn_def_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    visibility = Keyword.get(meta, :visibility, :public)
    params = Keyword.get(meta, :params, [])
    return_type = Keyword.get(meta, :return_type)
    guard = Keyword.get(meta, :guards)
    constraints = Keyword.get(meta, :constraints, [])
    clauses = Keyword.get(meta, :clauses)
    extern = Keyword.get(meta, :extern)
    decorator = Keyword.get(meta, :decorator)

    prefix = if visibility == :private, do: "local fn", else: "fn"
    params_str = typed_params_to_string(params, depth, indent)
    ret_str = if return_type, do: " -> #{render(return_type, depth, indent)}", else: ""

    guard_str =
      if guard, do: " when #{render(guard, depth, indent)}", else: ""

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &render(&1, depth, indent))
        " where #{cs}"
      else
        ""
      end

    sig = "#{prefix} #{quote_if_reserved(name)}(#{params_str})#{ret_str}#{guard_str}#{constraints_str}"

    result =
      cond do
        clauses != nil and clauses != [] ->
          pad = String.duplicate(indent, depth + 1)

          clauses_str =
            clauses
            |> Enum.map(&fn_clause_to_string(&1, depth + 1, indent))
            |> Enum.join("\n#{pad}")

          "#{sig}\n#{pad}#{clauses_str}"

        body == [] ->
          # Signature only (protocol)
          sig

        true ->
          [body_ast] = body
          "#{sig} = #{rhs_to_string(body_ast, depth, indent)}"
      end

    result = maybe_prepend_decorator(result, extern, decorator, depth, indent)
    result
  end

  defp maybe_prepend_decorator(result, nil, nil, _depth, _indent), do: result

  defp maybe_prepend_decorator(result, extern, _decorator, depth, indent) when extern != nil do
    {m, f, a} =
      case extern do
        {m, f, a} -> {m, f, a}
        _ -> {nil, nil, nil}
      end

    if m do
      # The decorator prints on its own line; the definition on the next.
      # Re-indent the continuation so a decorated definition nested inside a
      # module/interface body keeps its `result` line aligned (the parent's
      # join only pads the first line).
      "@extern(#{extern_ref_to_string(m)}, #{extern_ref_to_string(f)}, #{a})\n#{String.duplicate(indent, depth)}#{result}"
    else
      result
    end
  end

  defp maybe_prepend_decorator(result, _extern, {dec_name, args}, depth, indent) do
    args_str =
      case args do
        [{:literal, [subtype: :boolean], bval}] ->
          # Single boolean arg: emit as @name true / @name false (no parens)
          " #{bval}"

        [] ->
          ""

        _ ->
          "(#{args_to_string(args, depth, indent)})"
      end

    "@#{dec_name}#{args_str}\n#{String.duplicate(indent, depth)}#{result}"
  end

  defp maybe_prepend_decorator(result, _, _, _, _), do: result

  # An `@extern` module/function reference. A dotted or PascalCase module atom
  # (`:"Elixir.Cure.Actor.Builtins"`) came from the bare dotted surface form
  # `Elixir.Cure.Actor.Builtins` and must round-trip WITHOUT a leading colon
  # (rendering `:Elixir.Cure...` would reparse as attribute-access, not an
  # atom). A plain lowercase atom (`:erlang`) keeps its symbol colon.
  defp extern_ref_to_string(ref) when is_atom(ref) do
    s = Atom.to_string(ref)

    cond do
      String.contains?(s, ".") -> s
      String.match?(s, ~r/^[A-Z]/) -> s
      true -> ":#{s}"
    end
  end

  defp extern_ref_to_string(ref), do: "#{ref}"

  # Backtick-quote a name that would otherwise lex as a keyword/operator so it
  # round-trips as an ordinary identifier (e.g. the `Std.Bool` connectives
  # `` `not` ``/`` `and` ``/`` `or` ``).
  defp quote_if_reserved(name) when is_binary(name) do
    if name in @reserved_words, do: "`#{name}`", else: name
  end

  defp quote_if_reserved(name), do: name

  defp typed_params_to_string(params, depth, indent) do
    Enum.map_join(params, ", ", fn {:param, meta, name} ->
      kind = Keyword.get(meta, :kind)
      type_ast = Keyword.get(meta, :type)
      default = Keyword.get(meta, :default)

      prefix =
        case kind do
          :variadic -> "*"
          :keyword_variadic -> "**"
          _ -> ""
        end

      type_str = if type_ast, do: ": #{render(type_ast, depth, indent)}", else: ""
      default_str = if default, do: " = #{render(default, depth, indent)}", else: ""
      "#{prefix}#{name}#{type_str}#{default_str}"
    end)
  end

  defp fn_clause_to_string(%{params: params, guard: guard, body: [body_ast]}, depth, indent) do
    params_str = Enum.map_join(params, ", ", &render(&1, depth, indent))
    guard_str = if guard, do: " when #{render(guard, depth, indent)}", else: ""
    body_str = render(body_ast, depth, indent)
    "| #{params_str}#{guard_str} -> #{body_str}"
  end

  # -- Container -------------------------------------------------------------

  defp container_to_string(meta, body, depth, indent) do
    type = Keyword.get(meta, :container_type)

    result =
      case type do
        :module -> module_to_string(meta, body, depth, indent)
        :struct -> record_to_string(meta, body, depth, indent)
        :enum -> enum_to_string(meta, body, depth, indent)
        :protocol -> protocol_to_string(meta, body, depth, indent)
        :trait -> impl_to_string(meta, body, depth, indent)
        :fsm -> fsm_to_string(meta, body, depth, indent)
        :supervisor -> supervisor_to_string(meta, body, depth, indent)
        :actor -> actor_to_string(meta, body, depth, indent)
        :app -> app_to_string(meta, body, depth, indent)
        :proof -> proof_to_string(meta, body, depth, indent)
        :primitive -> primitive_to_string(meta, body, depth, indent)
        _ -> inspect({:container, meta, body})
      end

    # A module-level decorator (`@group(:g)`) attaches to the container itself and
    # prints on its own line directly above it — the canonical above-`mod` form.
    maybe_prepend_decorator(result, nil, Keyword.get(meta, :decorator), depth, indent)
  end

  # -- Primitive type home (`primitive Name`) --------------------------------
  #
  # An irreducible base type (`Int`, `Float`, `Binary`, `Atom`) given a documented
  # module home. The body is empty; a `@builtin(:tag)` decorator (in meta) prints
  # on the preceding line via `maybe_prepend_decorator/5` in `container_to_string`.
  defp primitive_to_string(meta, _body, _depth, _indent), do: "primitive #{Keyword.get(meta, :name)}"

  # -- Supervisor container (`sup Name`) -------------------------------------
  #
  # Settings (`strategy`/`intensity`/`period`) live in meta; the body is a flat
  # list of `child_spec` nodes that must be re-wrapped in a `children` block.
  defp supervisor_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)
    child_pad = String.duplicate(indent, depth + 2)

    settings =
      for key <- [:strategy, :intensity, :period],
          (val = Keyword.get(meta, key)) != nil do
        "#{key} = #{render(val, depth + 1, indent)}"
      end

    children_block =
      case body do
        [] ->
          []

        specs ->
          specs_str =
            specs
            |> Enum.map(&render(&1, depth + 2, indent))
            |> Enum.join("\n#{child_pad}")

          ["children\n#{child_pad}#{specs_str}"]
      end

    lines = settings ++ children_block

    case lines do
      [] -> "sup #{name}"
      _ -> "sup #{name}\n#{pad}" <> Enum.join(lines, "\n#{pad}")
    end
  end

  # -- Actor container (`actor Name [with Init]`) ----------------------------
  #
  # The optional initial payload is in `meta[:init]`; `on_message`/`on_start`/
  # `on_stop` callbacks are keyword lists of match-arm clauses in meta.
  defp actor_to_string(meta, _body, depth, indent) do
    name = Keyword.get(meta, :name)
    init = Keyword.get(meta, :init)
    pad = String.duplicate(indent, depth + 1)

    init_str = if init, do: " with #{render(init, depth, indent)}", else: ""

    callbacks =
      callback_blocks_to_string(meta, [:on_start, :on_message, :on_stop], depth, indent)

    "actor #{name}#{init_str}\n#{pad}#{callbacks}"
  end

  # -- Application container (`app Name`) ------------------------------------
  #
  # Settings and `on_start`/`on_stop`/`on_phase` callbacks all live in meta.
  defp app_to_string(meta, _body, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)

    settings =
      for key <- [:vsn, :description, :root, :applications, :included_applications, :env, :registered],
          (val = Keyword.get(meta, key)) != nil do
        "#{key} = #{render(val, depth + 1, indent)}"
      end

    callback_lines =
      [:on_start, :on_stop]
      |> Enum.flat_map(fn cb -> callback_block_lines(meta, cb, depth, indent) end)

    phase_lines =
      case Keyword.get(meta, :on_phase) do
        phases when is_list(phases) and phases != [] ->
          child_pad = String.duplicate(indent, depth + 2)

          Enum.map(phases, fn {phase, clauses} ->
            clauses_str =
              clauses
              |> Enum.map(&callback_clause_to_string(&1, depth + 2, indent))
              |> Enum.join("\n#{child_pad}")

            "on_phase :#{phase}\n#{child_pad}#{clauses_str}"
          end)

        _ ->
          []
      end

    lines = settings ++ callback_lines ++ phase_lines

    case lines do
      [] -> "app #{name}"
      _ -> "app #{name}\n#{pad}" <> Enum.join(lines, "\n#{pad}")
    end
  end

  # -- Proof container (`proof Name`) ----------------------------------------
  #
  # A proof container is a module-like block of function definitions.
  defp proof_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    case body do
      [] -> "proof #{name}"
      _ -> "proof #{name}\n#{pad}#{body_str}"
    end
  end

  # Render the named callback blocks (`on_message` etc.) that carry lists of
  # match-arm clauses in meta, joined at the container-body indent.
  defp callback_blocks_to_string(meta, cb_names, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    cb_names
    |> Enum.flat_map(fn cb -> callback_block_lines(meta, cb, depth, indent) end)
    |> Enum.join("\n#{pad}")
  end

  defp callback_block_lines(meta, cb, depth, indent) do
    case Keyword.get(meta, cb) do
      clauses when is_list(clauses) and clauses != [] ->
        child_pad = String.duplicate(indent, depth + 2)

        clauses_str =
          clauses
          |> Enum.map(&callback_clause_to_string(&1, depth + 2, indent))
          |> Enum.join("\n#{child_pad}")

        ["#{cb}\n#{child_pad}#{clauses_str}"]

      _ ->
        []
    end
  end

  # A callback clause `(p1, p2) [when g] -> body`. A multi-statement body is
  # rendered as an indented block so its later statements do not dedent onto
  # the callback-clause column (which would reparse as a fresh clause).
  defp callback_clause_to_string({:match_arm, meta, [body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    head =
      if guard do
        render(pattern, depth, indent) <> " when " <> render(guard, depth, indent)
      else
        render(pattern, depth, indent)
      end

    case body do
      {:block, _bmeta, exprs} when length(exprs) > 1 ->
        inner_pad = String.duplicate(indent, depth + 1)

        body_str =
          exprs
          |> Enum.map(&render(&1, depth + 1, indent))
          |> Enum.join("\n#{inner_pad}")

        head <> " ->\n#{inner_pad}#{body_str}"

      _ ->
        head <> " -> " <> render(body, depth, indent)
    end
  end

  defp module_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)

    # A bare `mod Name` header (empty body — its definitions are siblings in the
    # enclosing statement list, not nested) must not emit a dangling indented
    # blank line.
    case body do
      [] ->
        "mod #{name}"

      _ ->
        pad = String.duplicate(indent, depth + 1)

        body_str =
          body
          |> Enum.map(&render(&1, depth + 1, indent))
          |> Enum.join("\n#{pad}")

        "mod #{name}\n#{pad}#{body_str}"
    end
  end

  defp record_to_string(meta, fields, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    fields_str =
      fields
      |> Enum.map(fn {:param, field_meta, field_name} ->
        type_ast = Keyword.get(field_meta, :type)
        "#{field_name}: #{render(type_ast, depth + 1, indent)}"
      end)
      |> Enum.join("\n#{pad}")

    "rec #{name}#{tp_str}\n#{pad}#{fields_str}"
  end

  defp enum_to_string(meta, variants, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    variants_str =
      case variants do
        [] ->
          # The empty (uninhabited) type is written `type Empty = |`.
          "|"

        _ ->
          variants
          |> Enum.map(&variant_to_string(&1, depth, indent))
          |> Enum.join(" | ")
      end

    "type #{name}#{tp_str} = #{variants_str}"
  end

  defp variant_to_string({:function_def, meta, []}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])

    if params != [] do
      params_str = Enum.map_join(params, ", ", &render(&1, depth, indent))
      "#{name}(#{params_str})"
    else
      name
    end
  end

  defp variant_to_string({:variable, _meta, name}, _depth, _indent), do: name
  defp variant_to_string(other, depth, indent), do: render(other, depth, indent)

  defp protocol_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "proto #{name}#{tp_str}\n#{pad}#{body_str}"
  end

  defp impl_to_string(meta, body, depth, indent) do
    protocol = Keyword.get(meta, :protocol)
    for_type = Keyword.get(meta, :for)
    constraints = Keyword.get(meta, :constraints, [])
    pad = String.duplicate(indent, depth + 1)

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &render(&1, depth, indent))
        " where #{cs}"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "impl #{protocol} for #{for_type}#{constraints_str}\n#{pad}#{body_str}"
  end

  defp fsm_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    payload = Keyword.get(meta, :payload)
    timer = Keyword.get(meta, :timer)
    pad = String.duplicate(indent, depth + 1)

    payload_str =
      if payload do
        " with #{render(payload, depth, indent)}"
      else
        ""
      end

    transitions_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    # Annotations
    annotations =
      if timer, do: ["\n#{pad}@timer #{timer}"], else: []

    # Callback blocks
    callback_blocks =
      ~w(on_transition on_enter on_exit on_failure on_timer)a
      |> Enum.flat_map(fn cb_name ->
        case Keyword.get(meta, cb_name) do
          clauses when is_list(clauses) and clauses != [] ->
            clauses_str =
              clauses
              |> Enum.map(&render(&1, depth + 2, indent))
              |> Enum.join("\n#{String.duplicate(indent, depth + 2)}")

            ["\n#{pad}#{cb_name}\n#{String.duplicate(indent, depth + 2)}#{clauses_str}"]

          _ ->
            []
        end
      end)

    "fsm #{name}#{payload_str}\n#{pad}#{transitions_str}#{annotations}#{callback_blocks}"
  end

  defp fsm_transition_to_string(meta, _depth, _indent) do
    from = Keyword.get(meta, :from)
    event = Keyword.get(meta, :event)
    to = Keyword.get(meta, :to)
    event_kind = Keyword.get(meta, :event_kind, :normal)

    suffix =
      case event_kind do
        :hard -> "!"
        :soft -> "?"
        _ -> ""
      end

    "#{from} --#{event}#{suffix}--> #{to}"
  end

  # -- Type Annotation -------------------------------------------------------

  defp type_annotation_to_string(meta, children, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    case children do
      [type_expr] ->
        "type #{name}#{tp_str} = #{render(type_expr, depth, indent)}"

      _ ->
        "type #{name}#{tp_str} = #{args_to_string(children, depth, indent)}"
    end
  end

  # -- Literal helpers -------------------------------------------------------

  defp escape_string(s) when is_binary(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\t", "\\t")
  end

  defp float_to_string(f) when is_float(f) do
    # Use shortest representation that round-trips correctly
    short = :erlang.float_to_binary(f, [:short])

    # Ensure it contains a dot so it parses as a float
    if String.contains?(short, ".") or String.contains?(short, "e") do
      short
    else
      short <> ".0"
    end
  end

  defp regex_to_string({body, flags}), do: "~r/#{body}/#{flags}"
  defp regex_to_string(other), do: inspect(other)

  defp char_to_string(c) when is_integer(c) do
    case c do
      ?\n -> "'\\n'"
      ?\t -> "'\\t'"
      ?\\ -> "'\\\\'"
      ?' -> "'\\''"
      0 -> "'\\0'"
      _ -> "'#{<<c::utf8>>}'"
    end
  end

  defp bytes_to_string(_meta, []), do: "<<>>"

  defp bytes_to_string(_meta, [{:bin_segment, _, _} | _] = segments) do
    # v0.20.0: bytes literal carries a list of `{:bin_segment, ...}` children.
    inner = Enum.map_join(segments, ", ", &render(&1, 0, @default_indent))
    "<<#{inner}>>"
  end

  defp bytes_to_string(_meta, elements) when is_list(elements) do
    inner = Enum.map_join(elements, ", ", &render(&1, 0, @default_indent))
    "<<#{inner}>>"
  end

  defp bytes_to_string(_meta, _value), do: "<<>>"

  # Build the specifier chain for a bin_segment. Returns an empty
  # string if no specifiers are present; otherwise a hyphen-joined
  # list such as `utf8`, `binary-size(n)`, or `signed-big-32`.
  defp bin_segment_specifier_string(meta, depth, indent) do
    parts = []
    parts = maybe_append(parts, Keyword.get(meta, :type))
    parts = maybe_append(parts, Keyword.get(meta, :signedness))
    parts = maybe_append(parts, Keyword.get(meta, :endianness))

    parts =
      case Keyword.get(meta, :size) do
        nil -> parts
        {:literal, _, n} when is_integer(n) -> parts ++ [Integer.to_string(n)]
        ast -> parts ++ ["size(" <> render(ast, depth, indent) <> ")"]
      end

    parts =
      case Keyword.get(meta, :unit) do
        nil -> parts
        n when is_integer(n) -> parts ++ ["unit(" <> Integer.to_string(n) <> ")"]
        {:literal, _, n} when is_integer(n) -> parts ++ ["unit(" <> Integer.to_string(n) <> ")"]
        _ -> parts
      end

    Enum.join(parts, "-")
  end

  defp maybe_append(parts, nil), do: parts
  defp maybe_append(parts, atom) when is_atom(atom), do: parts ++ [Atom.to_string(atom)]
  defp maybe_append(parts, _), do: parts

  # ── Match Block Rendering (MATCH §9) ────────────────────────────────────
  #
  # The strategy is the one prescribed by the spec:
  #
  #   1. Render every clause's head text (`pattern` or `pattern when guard`)
  #      and every clause's right-hand side text using the inline
  #      printer.
  #   2. If any branch is multi-line (its rendered RHS contains a
  #      newline) or any aligned line would exceed `max_line_width`,
  #      switch the entire block to the wrapped form.
  #   3. Otherwise, align all `->` arrows by padding heads to the
  #      width of the widest head, unless that width exceeds
  #      `alignment_limit`, in which case fall back to the unaligned
  #      form.

  defp render_match_block(scrutinee, arms, depth, indent) do
    render_scrutinee_block("match ", scrutinee, "", arms, depth, indent)
  end

  # Shared renderer for `match`/`with` scrutinee blocks: a keyword, the
  # scrutinee, an optional trailing suffix (e.g. ` proof p`), and aligned or
  # wrapped match arms.
  defp render_scrutinee_block(keyword, scrutinee, suffix, arms, depth, indent) do
    pad_kw = String.duplicate(indent, depth)
    pad = pad_kw <> indent
    scrut_str = render(scrutinee, depth, indent)

    heads = Enum.map(arms, &match_arm_head(&1, depth + 1, indent))
    rhs_inline = Enum.map(arms, &match_arm_rhs_inline(&1, depth + 1, indent))
    multiline_rhs? = Enum.any?(rhs_inline, &multiline?/1)

    max_head = max_grapheme_width(heads)
    align? = max_head <= @alignment_limit

    aligned_lines =
      if align? do
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} ->
          pad_str = String.duplicate(" ", max_head - grapheme_width(h))
          pad <> h <> pad_str <> " -> " <> r
        end)
      else
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} -> pad <> h <> " -> " <> r end)
      end

    too_long? = Enum.any?(aligned_lines, fn line -> grapheme_width(line) > @max_line_width end)

    clauses_str =
      cond do
        multiline_rhs? or too_long? ->
          arms
          |> Enum.zip(heads)
          |> Enum.map(fn {arm, head} -> render_match_arm_wrapped(arm, head, depth + 1, indent) end)
          |> Enum.join("\n" <> pad)

        true ->
          aligned_lines
          |> Enum.map(&String.trim_leading(&1, pad_kw <> indent))
          |> Enum.join("\n" <> pad)
      end

    keyword <> scrut_str <> suffix <> "\n" <> pad <> clauses_str
  end

  defp match_arm_head({:match_arm, meta, [_body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)
    pat_str = render(pattern, depth, indent)

    if guard do
      pat_str <> " when " <> render(guard, depth, indent)
    else
      pat_str
    end
  end

  defp match_arm_rhs_inline({:match_arm, meta, [body]}, depth, indent) do
    arm_body_to_string(meta, body, depth, indent)
  end

  defp render_match_arm_wrapped({:match_arm, meta, [body]}, head, depth, indent) do
    if Keyword.get(meta, :impossible) do
      head <> " -> impossible"
    else
      inner_pad = String.duplicate(indent, depth + 1)
      body_str = wrapped_body_to_string(body, depth, indent)
      head <> " ->\n" <> inner_pad <> body_str
    end
  end

  # An arm whose body is the soft-keyword `impossible` (an absurd/unreachable
  # case, spec §4) carries `meta[:impossible]` with a nil body; render the
  # keyword back.
  defp arm_body_to_string(meta, body, depth, indent) do
    if Keyword.get(meta, :impossible) do
      "impossible"
    else
      render(body, depth, indent)
    end
  end

  # ── Pickup Block Rendering (PICKUP §8) ───────────────────────────────────

  defp render_pickup_block(clauses, depth, indent) do
    pad_kw = String.duplicate(indent, depth)
    pad = pad_kw <> indent

    heads = Enum.map(clauses, &pickup_clause_head(&1, depth + 1, indent))
    rhs_inline = Enum.map(clauses, &pickup_clause_rhs_inline(&1, depth + 1, indent))
    multiline_rhs? = Enum.any?(rhs_inline, &multiline?/1)

    max_head = max_grapheme_width(heads)
    align? = max_head <= @alignment_limit

    aligned_lines =
      if align? do
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} ->
          pad_str = String.duplicate(" ", max_head - grapheme_width(h))
          pad <> h <> pad_str <> " -> " <> r
        end)
      else
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} -> pad <> h <> " -> " <> r end)
      end

    too_long? = Enum.any?(aligned_lines, fn line -> grapheme_width(line) > @max_line_width end)

    clauses_str =
      cond do
        multiline_rhs? or too_long? ->
          clauses
          |> Enum.zip(heads)
          |> Enum.map(fn {clause, head} ->
            render_pickup_clause_wrapped(clause, head, depth + 1, indent)
          end)
          |> Enum.join("\n" <> pad)

        true ->
          aligned_lines
          |> Enum.map(&String.trim_leading(&1, pad_kw <> indent))
          |> Enum.join("\n" <> pad)
      end

    "pickup\n" <> pad <> clauses_str
  end

  defp pickup_clause_head({:pickup_else, _meta, [_body]}, _depth, _indent), do: "else"

  defp pickup_clause_head({:pickup_clause, _meta, [guard, _body]}, depth, indent) do
    render(guard, depth, indent)
  end

  defp pickup_clause_rhs_inline({:pickup_else, _meta, [body]}, depth, indent) do
    render(body, depth, indent)
  end

  defp pickup_clause_rhs_inline({:pickup_clause, _meta, [_guard, body]}, depth, indent) do
    render(body, depth, indent)
  end

  defp render_pickup_clause_wrapped({:pickup_else, _meta, [body]}, _head, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    body_str = wrapped_body_to_string(body, depth, indent)
    "else ->\n" <> inner_pad <> body_str
  end

  defp render_pickup_clause_wrapped({:pickup_clause, _meta, [_guard, body]}, head, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    body_str = wrapped_body_to_string(body, depth, indent)
    head <> " ->\n" <> inner_pad <> body_str
  end

  # PICKUP §8.3: a trailing `true ->` clause is normalised to `else ->`.
  # Non-terminal `true ->` clauses are left alone (the type checker
  # will raise W-PICKUP-UNREACHABLE for the clauses that follow).
  defp normalize_pickup_terminator([]), do: []

  defp normalize_pickup_terminator(clauses) do
    {init, [last]} = Enum.split(clauses, length(clauses) - 1)

    normalised_last =
      case last do
        {:pickup_clause, meta, [{:literal, _, true}, body]} ->
          {:pickup_else, meta, [body]}

        _ ->
          last
      end

    init ++ [normalised_last]
  end

  # When the right-hand side is a multi-line block, we render it as a
  # block expression with the appropriate indentation. Otherwise we
  # render it inline (using the standard printer), which is fine for
  # any expression that fits on a single line.
  defp wrapped_body_to_string({:block, meta, exprs} = block, depth, indent) do
    case Keyword.get(meta, :block_shape) do
      :brace ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth + 1, indent))
        "{ " <> body <> " }"

      :end ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth + 1, indent))
        body <> "; end"

      _ ->
        # Render each statement on its own line, indented one step
        # deeper than the clause head.
        inner_pad = String.duplicate(indent, depth + 1)

        exprs
        |> Enum.map(&render(&1, depth + 1, indent))
        |> Enum.join("\n" <> inner_pad)
        |> case do
          "" -> render(block, depth + 1, indent)
          rendered -> rendered
        end
    end
  end

  defp wrapped_body_to_string(other, depth, indent) do
    render(other, depth + 1, indent)
  end

  defp multiline?(str) when is_binary(str), do: String.contains?(str, "\n")

  defp grapheme_width(str) when is_binary(str), do: String.length(str)

  defp max_grapheme_width([]), do: 0

  defp max_grapheme_width(list) do
    list
    |> Enum.map(&grapheme_width/1)
    |> Enum.max()
  end
end
