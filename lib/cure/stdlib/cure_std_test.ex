defmodule :cure_std_test do
  @moduledoc """
  Runtime helpers for `Std.Test.forall_shrunk/3`.

  When a property fails, walk the shrink candidates in aggressive-first order
  and pick the smallest value that still makes the property return `false`.

  Returns a `Std.Result`: `{:ok, :ok}` when every sample satisfied the property,
  `{:error, minimal}` carrying the minimised counterexample when one did not.

  It used to return the bare atom `:ok` and raise
  `{:property_failed_with_shrunk, minimal}`, under an `@extern` postulating
  `∀t. (Atom -> t) -> (t -> Bool) -> Int -> t`. Neither branch inhabited `t`,
  and the raise made the postulated totality false. The type is now
  `Result(Atom, t)` and both branches produce a value.

  The tags are LOWERCASE. The classic pipeline — which is what compiles
  `lib/std/test.cure` — erases `Ok(v)` to `{:ok, v}`, while the dependent
  pipeline erases it to `{:Ok, v}`. Every sibling shim (`cure_std_time`,
  `cure_std_regex`, `cure_std_json`) uses the lowercase form, and classic Cure
  cannot destructure the uppercase one. When `test.cure` eventually
  dependent-elaborates (#23), this tag has to change with it.
  """

  def forall_shrunk(gen, property, runs) when is_function(gen) and is_function(property) do
    case find_counterexample(gen, property, runs) do
      :all_pass ->
        {:ok, :ok}

      {:failed, value} ->
        {:error, shrink_loop(value, property)}
    end
  end

  defp find_counterexample(_gen, _property, 0), do: :all_pass

  defp find_counterexample(gen, property, n) when n > 0 do
    value = gen.(:draw)

    case property.(value) do
      true -> find_counterexample(gen, property, n - 1)
      false -> {:failed, value}
      _ -> {:failed, value}
    end
  end

  defp shrink_loop(value, property) do
    candidates =
      try do
        :cure_std_gen.shrink(value)
      rescue
        _ -> []
      end

    failing =
      Enum.find(candidates, fn cand ->
        case safe_invoke(property, cand) do
          false -> true
          _ -> false
        end
      end)

    case failing do
      nil -> value
      better -> shrink_loop(better, property)
    end
  end

  defp safe_invoke(f, v) do
    try do
      f.(v)
    rescue
      _ -> false
    catch
      _, _ -> false
    end
  end
end
