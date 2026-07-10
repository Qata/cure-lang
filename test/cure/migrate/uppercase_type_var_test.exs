defmodule Cure.Migrate.UppercaseTypeVarTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(ast, file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "free uppercase type var is lowercased across the signature" do
    {out, warns} = migrate("mod M\nfn id(x: T) -> T = x\n", "a.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    refute out =~ "T"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an uppercase name that resolves to a declared type is left alone" do
    {out, _} = migrate("mod M\ntype Foo = Int\nfn f(x: Foo) -> Foo = x\n", "b.cure")
    assert out =~ "Foo"
  end

  test "a built-in primitive type is left alone even with no local type declaration" do
    # `Int` is parsed identically to a free type var (both are a bare
    # `{:variable, [scope: :local], name}` at parser.ex:3281-3305) and this
    # file declares/imports nothing locally -- this only stays untouched if
    # `build_ctx/1` seeds Cure's built-in primitive type names, not just
    # this file's own `type`/`import` declarations.
    {out, warns} = migrate("mod M\nfn f(x: Int) -> Int = x\n", "e.cure")
    assert out =~ "x: Int"
    assert out =~ "-> Int"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "T and t in the same signature freshen rather than merge" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t) -> T = x\n", "c.cure")
    # every occurrence of the freshened `T` binder becomes `t1` consistently...
    assert out =~ "x: t1"
    assert out =~ "-> t1"
    # ...and the pre-existing `t` binder is untouched, not merged onto
    assert out =~ "y: t)"
    refute out =~ "T"
  end

  test "freshening skips an already-used t1, landing on t2 (spec §7)" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t, z: t1) -> T = x\n", "d.cure")
    # both `t` and `t1` are taken, so the freshened `T` must become `t2`,
    # not collide with either
    assert out =~ "x: t2"
    assert out =~ "-> t2"
    assert out =~ "y: t,"
    assert out =~ "z: t1)"
    refute out =~ "T"
  end

  test "a renamed type var is also renamed where it recurs in the body (let annotation)" do
    # The binder `T` is bound by the signature and referenced again in a body
    # `let y: T = x` type annotation. Renaming only the signature leaves the
    # body annotation dangling on an unbound `T`; the rename must propagate.
    {out, _} = migrate("mod M\nfn id(x: T) -> T =\n  let y: T = x\n  y\n", "f.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    assert out =~ "let y: t ="
    refute out =~ "T"
  end

  test "an implicit type-parameter binder is renamed in sync with its references" do
    # `{T: Type}` introduces the type variable via the param NAME `T`. Renaming
    # only the references (`x: T`, `-> T`) while leaving the binder spelled `T`
    # leaves those references bound to nothing — a working file turned broken
    # that the reparse-only verify still accepts. Binder and references must
    # move together.
    {out, _} = migrate("mod M\nfn id({T: Type}, x: T) -> T = x\n", "impl.cure")

    # Reparse and pull the implicit binder name and the reference names back out.
    {:ok, toks} = Lexer.tokenize(out, file: "impl.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "impl.cure", emit_events: false)
    fdef = find_fn(ast)
    params = Keyword.get(elem(fdef, 1), :params)
    return_type = Keyword.get(elem(fdef, 1), :return_type)

    [{:param, binder_meta, binder_name}, {:param, xmeta, _}] = params
    assert Keyword.get(binder_meta, :implicit), "the implicit param lost its :implicit flag"
    {:variable, _, xtype} = Keyword.get(xmeta, :type)
    {:variable, _, rtype} = return_type

    # All three must be the SAME (lowercased) name — no binder/reference desync.
    assert binder_name == xtype
    assert binder_name == rtype
    assert binder_name == String.downcase(binder_name)
  end

  test "a freshened signature binder avoids a distinct lowercase type var used only in the body" do
    # `T` in the signature lowercases to `t`, but the body already uses a
    # distinct free type var `t` in a `let` annotation. Freshening consulted
    # only signature names, so `T`→`t` silently MERGED onto the body's `t` —
    # violating the rule's own "T and t freshen rather than merge" guarantee.
    # The freshener must see the body's `t` and pick `t1`, leaving body `t`.
    {out, _} = migrate("mod M\nfn f(x: T) -> T =\n  let y: t = g(x)\n  y\n", "bodyfresh.cure")
    assert out =~ "x: t1"
    assert out =~ "-> t1"
    assert out =~ "let y: t ="
    refute out =~ "T"
  end

  defp find_fn(ast) do
    ast
    |> flatten_nodes()
    |> Enum.find(fn
      {:function_def, _, _} -> true
      _ -> false
    end)
  end

  defp flatten_nodes({_tag, _meta, kids} = node) when is_list(kids) do
    [node | Enum.flat_map(kids, &flatten_nodes/1)]
  end

  defp flatten_nodes(list) when is_list(list), do: Enum.flat_map(list, &flatten_nodes/1)
  defp flatten_nodes(other), do: [other]

  test "a renamed type var is also renamed in a body type application" do
    # `empty_of(T)` in the body passes the bound type var as a type argument;
    # it must track the signature rename to `t`, not stay `T`.
    {out, _} = migrate("mod M\nfn wrap(x: T) -> List(T) =\n  cons(x, empty_of(T))\n", "g.cure")
    assert out =~ "x: t"
    assert out =~ "List(t)"
    assert out =~ "empty_of(t)"
    refute out =~ "T"
  end
end
