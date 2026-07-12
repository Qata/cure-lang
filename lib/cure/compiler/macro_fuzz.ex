defmodule Cure.Compiler.MacroFuzz do
  @moduledoc """
  Antigen-backed typed filler generation for macro proof inputs.

  This first slice deliberately uses Antigen's certified v1 signature menu. A
  grammar category outside that menu is a reported coverage gap, not a guessed
  inhabitant of a different type.
  """

  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{SigMenu, Term}
  alias Cure.Core.{Context, Eval, Kernel}

  @type generator_info :: %{
          category: String.t(),
          env: Cure.Core.Env.t(),
          ctx: Context.t(),
          goal: Cure.Core.Term.t(),
          generator: Antigen.Gen.t()
        }

  @category_goals %{
    "Nat" => {:data, :Nat, [], []},
    "Bd" => {:data, :Bd, [], []},
    "Vec" => {:data, :Vec, [], [{:ctor, :Z, []}]}
  }

  @spec hole_generator(String.t()) ::
          {:ok, generator_info()} | {:error, {:unsupported_hole_type, String.t()}}
  def hole_generator(category) when is_binary(category) do
    case Map.fetch(@category_goals, category) do
      {:ok, goal} ->
        env = SigMenu.env_of(:v1)
        ctx = Context.empty(env)
        {:ok, %{category: category, env: env, ctx: ctx, goal: goal, generator: Term.gen_term(ctx, goal)}}

      :error ->
        {:error, {:unsupported_hole_type, category}}
    end
  end

  @spec sample_holes(String.t(), non_neg_integer(), integer()) ::
          {:ok, generator_info(), [Cure.Core.Term.t()]}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:generated_hole_not_well_typed, term()}}
  def sample_holes(category, count, seed)
      when is_binary(category) and is_integer(count) and count >= 0 and is_integer(seed) do
    with {:ok, info} <- hole_generator(category),
         terms = Backend.sample_seeded(info.generator, count, seed),
         :ok <- check_samples(info, terms) do
      {:ok, info, terms}
    end
  end

  defp check_samples(%{ctx: ctx, goal: goal}, terms) do
    goal_value = Eval.eval(goal, Context.env(ctx))

    case Enum.find(terms, &(Kernel.check(ctx, &1, goal_value) != :ok)) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end
end
