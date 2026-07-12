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

  test "a declared nullary data constructor used as an index is left alone" do
    # `KA` is a nullary variant of the enum `K`, and appears as an *argument*
    # of a type application (`Pair(Int, KA)`) exactly as an optic kind index
    # like `Optic(s, a, LensKind)` does. It parses as a bare `{:variable}` node
    # indistinguishable from a free type var, so it only stays untouched if
    # `build_ctx/1` seeds this file's declared *constructor* names, not just
    # its declared *type* names.
    src = "mod M\ntype K = KA | KB\nfn f(x: Pair(Int, KA)) -> Int = 0\n"
    {out, warns} = migrate(src, "ctor.cure")
    assert out =~ "KA"
    refute out =~ "ka"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a declared opaque type is left alone" do
    # `opaque type Counter` has no body, so it is a `container_type: :opaque`
    # node. `build_ctx/1` must collect opaque type names alongside struct/enum
    # ones, or the opaque handle used in a signature is misread as a type var.
    src = "mod M\nopaque type Counter\nfn f(x: Counter) -> Counter = x\n"
    {out, warns} = migrate(src, "opaque.cure")
    assert out =~ "x: Counter"
    assert out =~ "-> Counter"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a built-in type the legacy classic Env omits (Pid) is left alone" do
    # `Pid`/`Ref`/`Binary`/`Bitstring`/`Map`/`Tuple`/`Nat` are real Cure types
    # that the legacy non-dependent `Cure.Types.Env` never registered, so — like
    # `Type` — they must be supplemented explicitly or every concurrency/container
    # signature that mentions them warns spuriously and `cure migrate --all` would
    # corrupt them (`Pid` -> `pid`).
    for ty <- ~w(Pid Ref Binary Bitstring Map Tuple Nat) do
      src = "mod M\nfn f(x: #{ty}) -> #{ty} = x\n"
      {out, warns} = migrate(src, "builtin.cure")
      assert out =~ "x: #{ty}", "#{ty} should be left as-is"
      refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var)),
             "#{ty} should not warn"
    end
  end

  test "an imported type or constructor (from `use Std.X`) is left alone" do
    # `Z` is `Std.Nat`'s zero constructor (`type Nat = Z | S(Nat)`), used here as
    # an index. It is neither a builtin nor declared in THIS file — only the
    # imported module knows it — so `build_ctx/1` must resolve `use Std.Nat` and
    # read its exported type/constructor names, or `Z` is misread as a free type
    # variable and lowercased to `z`.
    src = "mod M\nuse Std.Nat\nfn f(v: Pair(Int, Z)) -> Int = 0\n"
    {out, warns} = migrate(src, "imported.cure")
    assert out =~ "Z"
    refute out =~ "Pair(Int, z)"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an auto-prelude constructor used with no `use` statement is left alone" do
    # `proof.cure` references `Nat`/`Z`/`S` with NO import node — it gets them
    # from the elaborator's implicit auto-prelude (`Std.Nat` et al. imported into
    # every module). `build_ctx/1` must seed the auto-prelude's exported names
    # unconditionally, or `Z` in a file that never wrote `use Std.Nat` is misread
    # as a free type var and lowercased to `z`.
    src = "mod M\nfn f(v: Pair(Int, Z)) -> Int = 0\n"
    {out, warns} = migrate(src, "auto_prelude.cure")
    assert out =~ "Z"
    refute out =~ "Pair(Int, z)"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end
end
