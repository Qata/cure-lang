defmodule Cure.Stdlib.UnitTypeTest do
  @moduledoc """
  `Std.Unit` — the unit type written the Swift way: `type Unit = ()`, with `()`
  as its sole value. This gives the compiler-seeded unit type a visible, surface
  definition (like `Std.Bool`/`Std.Nat`). `= ()` is reserved to `Unit`: any other
  type declared as `()` is a compile error, and `()` is not usable as a general
  ADT constructor spelling.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive

  defp elab(src) do
    try do
      Cure.Elab.Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  test "lib/std/unit.cure elaborates and declares Unit with the nullary `unit` ctor" do
    src = File.read!("lib/std/unit.cure")
    assert {:ok, env} = elab(src)
    ctors = Inductive.ctors_of(env, :Unit)
    assert [%{name: :"Std.Unit#unit", args: []}] = ctors
  end

  test "`type Unit = ()` produces the same family the compiler seeds" do
    {:ok, env} = elab("@group(:core)\nmod Std.Unit\n  type Unit = ()\n")
    assert [%{name: :"Std.Unit#unit", args: []}] = Inductive.ctors_of(env, :Unit)
  end

  test "`()` is a value of type Unit" do
    assert {:ok, _env} = elab("mod U\n  fn u() -> Unit = ()\n")
  end

  test "`type Foo = ()` for a non-Unit name is a reserved-syntax compile error" do
    assert {:error, errors} = elab("mod U\n  type Foo = ()\n")
    flat = List.wrap(errors)

    assert Enum.any?(flat, fn e -> match?({:unit_type_reserved, _}, e) end),
           "expected a :unit_type_reserved error, got: #{inspect(flat)}"
  end
end
