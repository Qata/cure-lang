defmodule Cure.Elab.ErasesDecoratorTest do
  @moduledoc """
  `@erases(<class>)` — an opaque FFI carrier declares the Erlang guard that recognises
  its erasure. An `opaque type` has no constructors, so its runtime shape cannot be
  inferred; it is asserted by the author of the sealed `unsafe` module. Spec §3.1.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  test "an @erases class is recorded on the opaque family" do
    src = """
    mod M
      @erases(:pid)
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: :pid} = Inductive.get_family(env, :Handle)
  end

  test "an opaque type without @erases has no declared erasure" do
    src = """
    mod M
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: nil} = Inductive.get_family(env, :Handle)
  end

  test "an unrecognised erasure class is a compile error" do
    src = """
    mod M
      @erases(:banana)
      opaque type Handle
    end
    """

    assert {:error, {:unknown_erasure_class, :Handle, :banana}} = Program.elaborate(src)
  end

  test "the unrecognised-class error names the admissible set (spec §4 item 2)" do
    error = {:unknown_erasure_class, :Handle, :banana}
    message = Cure.Compiler.Errors.format_error(error, "test.cure")

    for class <- [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list] do
      assert message =~ Atom.to_string(class),
             "the rendered message must name every admissible class; missing #{class}:\n#{message}"
    end
  end

  test "@erases on a type WITH constructors is a compile error" do
    src = """
    mod M
      @erases(:pid)
      type Colour = Red | Green
    end
    """

    assert {:error, {:erases_on_non_opaque, :Colour}} = Program.elaborate(src)
  end
end
