defmodule Cure.Elab.InstanceWhnfKeyTest do
  @moduledoc """
  Phase 1: the coherence key of an instance head is computed by whnf-ing the
  elaborated Core head, so a transparent type synonym files under the same key
  as the type it unfolds to (via the kernel's δ-reduction, not surface spelling).

  Note: the instance-method bodies use `a == b` rather than the primitive
  `Std.Builtin.int_eq`/`struct_eq` spelling — surface-callable builtins land in a
  later task. `==` already lowers correctly (Int → int_eq, Color → struct_eq), so
  these programs compile today and exercise exactly the coherence KEY this task
  changes.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "an instance for a transparent synonym collides with the underlying type" do
    src = """
    mod M
      use Std.Equatable
      typealias MyInt = Int
      implementation Equatable for MyInt
        fn eq(a: MyInt, b: MyInt) -> Bool = a == b
    end
    """

    # Std.Equatable already provides `Equatable for Int`. Registering a second
    # anonymous instance for `MyInt` (which whnf's to Int) must collide.
    assert {:error, {:overlapping_instance, :Equatable, :Int}} = Program.elaborate(src)
  end

  test "an instance for a genuine data type registers under its family name" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn eq(a: Color, b: Color) -> Bool = a == b
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
