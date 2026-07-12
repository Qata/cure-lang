defmodule Cure.Compiler.MacroFuzz do
  @moduledoc """
  Antigen-backed typed filler generation for macro proof inputs.

  This first slice deliberately uses Antigen's certified v1 signature menu. A
  grammar category outside that menu is a reported coverage gap, not a guessed
  inhabitant of a different type.
  """

  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{SigMenu, Term}
  alias Cure.Compiler.{Lexer, Parser, Token}
  alias Cure.Core.{Context, Eval, Kernel, Normalise}
  alias Cure.Elab.Elaborator

  @default_draws 32

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

  @doc "Proof-check supported syntax rules against generated use-sites."
  @spec check_expansion_proof(tuple(), Cure.Core.Env.t(), keyword()) ::
          :ok
          | {:error, {:expansion_ill_typed, map()}}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:unsupported_hole_arity, non_neg_integer()}}
          | {:error, term()}
  def check_expansion_proof({:macro_def, _meta, rules}, env, opts \\ []) do
    draws = Keyword.get(opts, :draws, @default_draws)
    seed = Keyword.get(opts, :seed, 1)

    rules
    |> Enum.filter(&(&1[:kind] == :syntax))
    |> Enum.reduce_while(:ok, fn rule, :ok ->
      case prove_rule(rule, rules, env, draws, seed) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp prove_rule(rule, rules, env, draws, seed) do
    holes = for {:hole, %{name: name, kind: kind}} <- rule.segments, do: {name, kind}

    case holes do
      [] ->
        with {:ok, input} <- assemble_use_site(rule, %{}),
             expansion = Parser.expand_example(rules, input) do
          check_expansion(rule.keyword, input, expansion, env)
        end

      [{name, kind}] ->
        with {:ok, _info, terms} <- sample_holes(kind, draws, seed) do
          Enum.reduce_while(terms, :ok, fn term, :ok ->
            with {:ok, input} <- assemble_use_site(rule, %{name => term}),
                 expansion = Parser.expand_example(rules, input),
                 :ok <- check_expansion(rule.keyword, input, expansion, env) do
              {:cont, :ok}
            else
              {:error, _} = error -> {:halt, error}
            end
          end)
        end

      many ->
        {:error, {:unsupported_hole_arity, length(many)}}
    end
  end

  defp check_expansion(keyword, input, expansion, env) do
    case Elaborator.elaborate_expr_typed(expansion, [], Context.empty(env), env) do
      {:ok, _term, _type} ->
        :ok

      {:error, reason} ->
        {:error, {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
    end
  end

  @doc "Assemble a rule's keyword, literals, and named hole fillers into tokens."
  @spec assemble_use_site(map(), %{String.t() => Cure.Core.Term.t()}) ::
          {:ok, [Token.t()]} | {:error, {:unsupported_surface_filler, term()}} | {:error, term()}
  def assemble_use_site(%{keyword: keyword, segments: segments}, bindings)
      when is_binary(keyword) and is_map(bindings) do
    with {:ok, words} <- assemble_words(segments, bindings),
         {:ok, tokens} <- Lexer.tokenize(Enum.join([keyword | words], " "), emit_events: false) do
      {:ok, Enum.reject(tokens, &(&1.type == :eof))}
    end
  end

  defp assemble_words(segments, bindings) do
    Enum.reduce_while(segments, {:ok, []}, fn
      {:lit, word}, {:ok, acc} ->
        {:cont, {:ok, acc ++ [word]}}

      {:hole, %{name: name}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, term} ->
            case surface_filler(term) do
              {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}
        end

      other, {:ok, _acc} ->
        {:halt, {:error, {:invalid_macro_segment, other}}}
    end)
  end

  defp surface_filler(term) do
    case surface_filler_normal(term) do
      {:error, _} = error ->
        normalized = Normalise.nf(Context.empty(SigMenu.env_of(:v1)), term)

        if normalized == term or normalized == :fuel_exhausted do
          error
        else
          surface_filler_normal(normalized)
        end

      result ->
        result
    end
  end

  defp surface_filler_normal({:ctor, :Z, []}), do: {:ok, "0"}

  defp surface_filler_normal({:ctor, :S, [inner]}) do
    with {:ok, n} <- surface_nat(inner), do: {:ok, Integer.to_string(n + 1)}
  end

  defp surface_filler_normal({:ctor, :T, []}), do: {:ok, "true"}
  defp surface_filler_normal({:ctor, :F, []}), do: {:ok, "false"}
  defp surface_filler_normal({:int_lit, n}) when is_integer(n), do: {:ok, Integer.to_string(n)}
  defp surface_filler_normal({:float_lit, n}) when is_float(n), do: {:ok, Float.to_string(n)}

  defp surface_filler_normal({:ctor, name, []}) when is_atom(name), do: {:ok, Atom.to_string(name)}
  defp surface_filler_normal(other), do: {:error, {:unsupported_surface_filler, other}}

  defp surface_nat({:ctor, :Z, []}), do: {:ok, 0}

  defp surface_nat({:ctor, :S, [inner]}) do
    with {:ok, n} <- surface_nat(inner), do: {:ok, n + 1}
  end

  defp surface_nat(_other), do: {:error, :not_a_nat}

  defp check_samples(%{ctx: ctx, goal: goal}, terms) do
    goal_value = Eval.eval(goal, Context.env(ctx))

    case Enum.find(terms, &(Kernel.check(ctx, &1, goal_value) != :ok)) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end
end
