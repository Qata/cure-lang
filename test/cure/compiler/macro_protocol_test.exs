defmodule Cure.Compiler.MacroProtocolTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroProtocol

  @steps [
    %{sender: :phone, receiver: :device, message: %{name: :hello, fields: [:name]}},
    %{sender: :device, receiver: :phone, message: %{name: :info, fields: [:model]}}
  ]

  test "builds deterministic protocol endpoints and message inventory" do
    assert {:ok, protocol} = MacroProtocol.build(:Provisioning, [:phone, :device], @steps, timeout: 10)
    assert protocol.kind == :quoted_protocol
    assert Enum.map(protocol.messages, & &1.name) == [:hello, :info]
    assert is_integer(protocol.declaration_hash)
    assert [_declaration] = protocol.declarations
  end

  test "rejects malformed roles and steps" do
    assert {:error, {:protocol_role_count, 3}} = MacroProtocol.build(:P, [:a, :b, :c], @steps)

    bad = [%{sender: :phone, receiver: :phone, message: %{name: :loop}}]
    assert {:error, {:self_protocol_step, :phone}} = MacroProtocol.build(:P, [:phone, :device], bad)
  end

  test "choice branches must begin with a message from the decider" do
    choices = [
      %{decider: :phone, branches: [[%{sender: :phone, receiver: :device, message: %{name: :join}}]]}
    ]

    assert {:ok, _} = MacroProtocol.build(:P, [:phone, :device], @steps, choices: choices)

    bad_choices = [%{decider: :phone, branches: [[%{sender: :device, receiver: :phone, message: %{name: :wrong}}]]}]
    assert {:error, {:unprojectable_choice, :phone}} =
             MacroProtocol.build(:P, [:phone, :device], @steps, choices: bad_choices)
  end
end
