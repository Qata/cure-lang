defmodule Cure.Stdlib.MacroOnlyOtpArchitectureTest do
  use ExUnit.Case, async: true

  @surfaces %{
    "lib/std/actor.cure" => ["macro actor", "Std.Otp.start_link"],
    "lib/std/fsm.cure" => ["macro fsm", "Std.Otp.start_statem"],
    "lib/std/supervisor.cure" => ["macro sup", "Std.Otp.start_supervisor"],
    "lib/std/app.cure" => ["macro app", "Std.Otp.start_supervisor"]
  }

  test "OTP object surfaces are source macros over the ordinary typed OTP algebra" do
    Enum.each(@surfaces, fn {file, required} ->
      source = File.read!(file)

      Enum.each(required, fn fragment ->
        assert source =~ fragment, "#{file} lost macro architecture fragment #{fragment}"
      end)

      refute source =~ "@extern(Elixir.Cure.", "#{file} restored an Elixir Builtins bridge"
      refute source =~ ".Builtins", "#{file} restored a Builtins-backed convenience API"
    end)
  end

  test "no active standard-library OTP object module references the retired bridges" do
    forbidden = [
      "Cure.Actor.Builtins",
      "Cure.FSM.Builtins",
      "Cure.Sup.Builtins",
      "Cure.App.Builtins"
    ]

    source =
      @surfaces
      |> Map.keys()
      |> Enum.map_join("\n", &File.read!/1)

    Enum.each(forbidden, fn bridge ->
      refute source =~ bridge
    end)
  end
end
