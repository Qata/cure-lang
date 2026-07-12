defmodule Cure.Compiler.MacroParseTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroParse

  test "builds a pure grammar declaration" do
    productions = [%{name: :word, body: ["word", :Text]}, %{name: :number, body: ["number", :Number]}]
    assert {:ok, %{kind: :quoted_parse_grammar, productions: ^productions}} = MacroParse.build(:Command, productions)
  end

  test "rejects duplicate and left-recursive productions" do
    duplicate = [%{name: :word, body: ["word"]}, %{name: :word, body: ["other"]}]
    assert {:error, :duplicate_parse_production} = MacroParse.build(:Command, duplicate)

    recursive = [%{name: :expr, body: [:expr, "+", :Number]}]
    assert {:error, {:left_recursive_parse_production, [:expr]}} = MacroParse.build(:Command, recursive)
  end
end
