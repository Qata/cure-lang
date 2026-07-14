defmodule Cure.Compiler.MacroStagedResolutionTest do
  use ExUnit.Case, async: false

  test "a staged callback uses a local helper over an imported helper" do
    source = """
    mod StagedResolution
      use Std.Syntax
      use Std.List

      macro Probe
        syntax probe <value: Code> computed by derive_probe

      fn map(values: List(t), f: t -> u) -> List(u) = []

      fn derive_probe(input: ProbeSyntax) -> Syntax =
        match map([1, 2], fn(x) -> x)
          [] -> integer(0)
          _ -> integer(1)

      fn answer() -> Int = probe 0
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :answer, []) == 0
  after
    purge(:StagedResolution)
  end

  test "a staged callback resolves a transitive import without a bare global" do
    source = """
    mod StagedTransitiveResolution
      use Std.Syntax

      macro Probe
        syntax probe computed by derive_probe

      fn derive_probe(input: ProbeSyntax) -> Syntax =
        Std.Syntax.leaf(:literal, [attr_value(:subtype, syntax_atom(:string))], syntax_string("7"))

      fn answer() -> String = probe
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :answer, []) == ~c"7"
  after
    purge(:StagedTransitiveResolution)
  end

  test "ambiguous imported names remain an error in staged compilation" do
    source = """
    mod StagedAmbiguousResolution
      use Std.{List, String}
      fn answer() -> Int = length("hello")
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  after
    purge(:StagedAmbiguousResolution)
  end

  defp purge(name) do
    module = Module.concat(Cure, name)
    :code.purge(module)
    :code.delete(module)
  end
end
