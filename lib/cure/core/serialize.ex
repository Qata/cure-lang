defmodule Cure.Core.Serialize do
  @moduledoc """
  Serialize `Cure.Core` terms to a stable, host-independent S-expression form and
  back (design spec §9, commitment C2).

  The point of C2 is *independent re-validation*: a kernel written in another
  language can parse this format, rebuild the Core term, and re-run
  `check`/`infer` on it. The grammar is therefore deliberately small and explicit
  — every term is `(tag …)`, de Bruijn indices and universe levels are integers,
  names are symbols, hole labels are quoted strings, and `case` branches are
  `(branch <ctor> <arity> <body>)`.

      encode({:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
      #=> "(prim add (int 3) (int 5))"
  """

  @doc "Encode a Core term as a canonical S-expression string."
  @spec encode(Cure.Core.Term.t()) :: binary()
  def encode(term), do: term |> enc() |> IO.iodata_to_binary()

  defp enc({:type, n}), do: ["(type ", Integer.to_string(n), ")"]
  defp enc({:var, k}), do: ["(var ", Integer.to_string(k), ")"]
  defp enc({:global, name}), do: ["(global ", sym(name), ")"]
  defp enc({:pi, d, c}), do: node("pi", [d, c])
  defp enc({:lam, d, b}), do: node("lam", [d, b])
  defp enc({:app, f, a}), do: node("app", [f, a])
  defp enc({:sigma, a, b}), do: node("sigma", [a, b])
  defp enc({:pair, a, b}), do: node("pair", [a, b])
  defp enc({:fst, p}), do: node("fst", [p])
  defp enc({:snd, p}), do: node("snd", [p])
  defp enc({:hole, name}), do: ["(hole ", str(name), ")"]
  defp enc({:absurd}), do: "(absurd)"
  defp enc({:int_type}), do: "(int-type)"
  defp enc({:float_type}), do: "(float-type)"
  defp enc({:int_lit, n}), do: ["(int ", Integer.to_string(n), ")"]
  defp enc({:float_lit, f}), do: ["(float ", Float.to_string(f), ")"]
  defp enc({:prim, op, args}), do: ["(prim ", sym(op), args_iodata(args), ")"]
  defp enc({:ctor, name, args}), do: ["(ctor ", sym(name), args_iodata(args), ")"]

  defp enc({:data, name, params, indices}),
    do: ["(data ", sym(name), " ", seq(params), " ", seq(indices), ")"]

  defp enc({:case, scrut, motive, branches}) do
    ["(case ", enc(scrut), " ", enc(motive), branches_iodata(branches), ")"]
  end

  defp node(tag, children),
    do: ["(", tag, Enum.map(children, fn c -> [" ", enc(c)] end), ")"]

  defp args_iodata(args), do: Enum.map(args, fn a -> [" ", enc(a)] end)
  defp seq(terms), do: ["(", Enum.map_intersperse(terms, " ", &enc/1), ")"]

  defp branches_iodata(branches) do
    Enum.map(branches, fn {ctor, arity, body} ->
      [" (branch ", sym(ctor), " ", Integer.to_string(arity), " ", enc(body), ")"]
    end)
  end

  defp sym(atom), do: Atom.to_string(atom)
  defp str(s), do: [?", String.replace(s, "\"", "\\\""), ?"]

  # -- decoding ---------------------------------------------------------------

  @doc "Decode a canonical S-expression string back into a Core term."
  @spec decode(binary()) :: {:ok, Cure.Core.Term.t()} | {:error, term()}
  def decode(string) when is_binary(string) do
    with {:ok, tokens} <- tokenize(string, []),
         {:ok, sexp, []} <- parse(tokens),
         {:ok, term} <- build(sexp) do
      {:ok, term}
    else
      {:ok, _sexp, _rest} -> {:error, :trailing_tokens}
      {:error, _} = err -> err
    end
  end

  # tokenizer → [:lparen | :rparen | {:atom, s} | {:int, n} | {:float, f} | {:str, s}]
  defp tokenize(<<>>, acc), do: {:ok, Enum.reverse(acc)}
  defp tokenize(<<c, rest::binary>>, acc) when c in [?\s, ?\t, ?\n, ?\r], do: tokenize(rest, acc)
  defp tokenize(<<?(, rest::binary>>, acc), do: tokenize(rest, [:lparen | acc])
  defp tokenize(<<?), rest::binary>>, acc), do: tokenize(rest, [:rparen | acc])

  defp tokenize(<<?", rest::binary>>, acc) do
    case take_string(rest, []) do
      {:ok, s, rest2} -> tokenize(rest2, [{:str, s} | acc])
      :error -> {:error, :unterminated_string}
    end
  end

  defp tokenize(bin, acc) do
    {word, rest} = take_atom(bin, [])
    tokenize(rest, [classify(word) | acc])
  end

  defp take_string(<<?\\, ?", rest::binary>>, acc), do: take_string(rest, [?" | acc])
  defp take_string(<<?", rest::binary>>, acc), do: {:ok, acc |> Enum.reverse() |> to_string(), rest}
  defp take_string(<<>>, _acc), do: :error
  defp take_string(<<c, rest::binary>>, acc), do: take_string(rest, [c | acc])

  defp take_atom(<<c, _::binary>> = bin, acc) when c in [?\s, ?\t, ?\n, ?\r, ?(, ?)],
    do: {acc |> Enum.reverse() |> to_string(), bin}

  defp take_atom(<<>>, acc), do: {acc |> Enum.reverse() |> to_string(), <<>>}
  defp take_atom(<<c, rest::binary>>, acc), do: take_atom(rest, [c | acc])

  defp classify(word) do
    case Integer.parse(word) do
      {n, ""} -> {:int, n}
      _ -> case Float.parse(word) do
             {f, ""} -> {:float, f}
             _ -> {:atom, word}
           end
    end
  end

  # parser: token list → nested s-expr ({:sexp, [..]} | {:atom,_} | {:int,_} | ...)
  defp parse([:lparen | rest]), do: parse_list(rest, [])
  defp parse([{_, _} = leaf | rest]), do: {:ok, leaf, rest}
  defp parse([]), do: {:error, :unexpected_eof}
  defp parse([:rparen | _]), do: {:error, :unexpected_rparen}

  defp parse_list([:rparen | rest], acc), do: {:ok, {:sexp, Enum.reverse(acc)}, rest}
  defp parse_list([], _acc), do: {:error, :unterminated_list}

  defp parse_list(tokens, acc) do
    with {:ok, item, rest} <- parse(tokens), do: parse_list(rest, [item | acc])
  end

  # build: s-expr → Core term
  defp build({:int, n}), do: {:ok, n}
  defp build({:float, f}), do: {:ok, f}
  defp build({:atom, s}), do: {:ok, s}
  defp build({:str, s}), do: {:ok, s}

  defp build({:sexp, [{:atom, head} | args]}), do: build_node(head, args)
  defp build(_), do: {:error, :malformed}

  defp build_node("type", [{:int, n}]), do: {:ok, {:type, n}}
  defp build_node("var", [{:int, k}]), do: {:ok, {:var, k}}
  defp build_node("global", [{:atom, n}]) do
    with {:ok, a} <- sym_atom(n), do: {:ok, {:global, a}}
  end
  defp build_node("int-type", []), do: {:ok, {:int_type}}
  defp build_node("float-type", []), do: {:ok, {:float_type}}
  defp build_node("int", [{:int, n}]), do: {:ok, {:int_lit, n}}
  defp build_node("float", [{:float, f}]), do: {:ok, {:float_lit, f}}
  defp build_node("hole", [{:str, s}]), do: {:ok, {:hole, s}}
  defp build_node("absurd", []), do: {:ok, {:absurd}}

  defp build_node("pi", [d, c]), do: binary(:pi, d, c)
  defp build_node("lam", [d, b]), do: binary(:lam, d, b)
  defp build_node("app", [f, a]), do: binary(:app, f, a)
  defp build_node("sigma", [a, b]), do: binary(:sigma, a, b)
  defp build_node("pair", [a, b]), do: binary(:pair, a, b)
  defp build_node("fst", [p]), do: unary(:fst, p)
  defp build_node("snd", [p]), do: unary(:snd, p)

  defp build_node("prim", [{:atom, op} | args]) do
    with {:ok, o} <- sym_atom(op), {:ok, cargs} <- build_all(args),
         do: {:ok, {:prim, o, cargs}}
  end

  defp build_node("ctor", [{:atom, name} | args]) do
    with {:ok, a} <- sym_atom(name), {:ok, cargs} <- build_all(args),
         do: {:ok, {:ctor, a, cargs}}
  end

  defp build_node("data", [{:atom, name}, {:sexp, ps}, {:sexp, is}]) do
    with {:ok, a} <- sym_atom(name), {:ok, cps} <- build_all(ps), {:ok, cis} <- build_all(is),
         do: {:ok, {:data, a, cps, cis}}
  end

  defp build_node("case", [scrut, motive | branches]) do
    with {:ok, cs} <- build(scrut),
         {:ok, cm} <- build(motive),
         {:ok, cbs} <- build_branches(branches) do
      {:ok, {:case, cs, cm, cbs}}
    end
  end

  defp build_node(_tag, _args), do: {:error, :unknown_node}

  defp unary(tag, x), do: with({:ok, t} <- build(x), do: {:ok, {tag, t}})

  defp binary(tag, a, b) do
    with {:ok, ta} <- build(a), {:ok, tb} <- build(b), do: {:ok, {tag, ta, tb}}
  end

  defp build_all(items) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case build(item) do
        {:ok, t} -> {:cont, {:ok, acc ++ [t]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp build_branches(branches) do
    Enum.reduce_while(branches, {:ok, []}, fn
      {:sexp, [{:atom, "branch"}, {:atom, ctor}, {:int, arity}, body]}, {:ok, acc} ->
        with {:ok, a} <- sym_atom(ctor), {:ok, b} <- build(body) do
          {:cont, {:ok, acc ++ [{a, arity, b}]}}
        else
          {:error, _} = err -> {:halt, err}
        end

      _other, _acc ->
        {:halt, {:error, :malformed_branch}}
    end)
  end

  # Bounded symbol interning (K12 / spec §D): decode names into EXISTING atoms
  # only. Untrusted C2 input cannot then exhaust the atom table — an unknown
  # symbol fails the decode cleanly (`:unknown_symbol`) instead of minting a new
  # permanent atom. Every symbol in a real program is already interned by the
  # compiler, so valid terms still round-trip.
  defp sym_atom(s) do
    {:ok, String.to_existing_atom(s)}
  rescue
    ArgumentError -> {:error, {:unknown_symbol, s}}
  end
end
