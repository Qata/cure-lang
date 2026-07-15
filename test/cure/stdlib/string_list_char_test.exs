defmodule Cure.Stdlib.StringListCharTest do
  @moduledoc """
  #29 — Std.String is the value-surface `List(Char)`, not the old Erlang binary.
  Pins that string.cure elaborates on the dependent pipeline, that `String`
  resolves to `List(Char)`, and that its list-native functions run end-to-end
  (length as code-point count, concat as list append).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "string.cure elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/string.cure"))
  end

  test "a char/string literal elaborates with no explicit use Std.Bounded" do
    # Std.Bounded is auto-prelude, so `:bounded` (Char = Bounded(0x110000))
    # resolves everywhere — string literals are core surface sugar.
    assert {:ok, _} = Program.elaborate("mod M\n  fn c() -> List(Char) = ['a']\nend\n")
    assert {:ok, _} = Program.elaborate("mod M\n  fn s() -> List(Char) = \"hi\"\nend\n")
  end

  test "String resolves to List(Char)" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.String\n  fn f(s: String) -> String = s\nend\n")
    assert match?(
             {:data, :"Std.List#List", [global: :"Std.Char#Char"], []},
             Cure.Core.Env.get_def(env, :String).body
           )
  end

  test "length runs as code-point count" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.String\n  fn n() -> Int = length(\"hello\")\nend\n")
    fns = Program.reachable_def_names(env, [:n])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrLen", functions: fns)
    assert apply(m, :n, []) == 5
  end

  test "concat runs as list append (code points)" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.String\n  fn c() -> String = concat(\"ab\", \"cd\")\nend\n")
    fns = Program.reachable_def_names(env, [:c])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrCat", functions: fns)
    assert apply(m, :c, []) == ~c"abcd"
  end
end
