defmodule Cure.Compiler.MacroFuzz do
  @moduledoc """
  Antigen-backed typed filler generation for macro proof inputs.

  This first slice deliberately uses Antigen's certified v1 signature menu. A
  grammar category outside that menu is a reported coverage gap, not a guessed
  inhabitant of a different type.
  """

  alias Antigen.{Challenge, Gen, Shrink}
  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{SigMenu, Term}
  alias Cure.Compiler.{Lexer, Parser, Token}
  alias Cure.Core.{Context, Eval, Inductive, Kernel, Normalise}
  alias Cure.Elab.{Elaborator, MacroExpand}

  @default_draws 32
  @cache_key :cure_macro_fuzz_cache_state

  @type generator_info :: %{
          category: String.t(),
          env: Cure.Core.Env.t(),
          ctx: Context.t(),
          goal: Cure.Core.Term.t() | nil,
          domain: atom(),
          generator: Antigen.Gen.t()
        }

  @category_goals %{
    "Nat" => {:data, :Nat, [], []},
    "Bd" => {:data, :Bd, [], []},
    "Vec" => {:data, :Vec, [], [{:ctor, :Z, []}]}
  }

  @spec hole_generator(String.t()) ::
          {:ok, generator_info()} | {:error, {:unsupported_hole_type, String.t()}}
  def hole_generator(category) when is_binary(category), do: hole_generator(category, SigMenu.env_of(:v1))

  @doc "Resolve a grammar category against a real module environment."
  @spec hole_generator(String.t(), Cure.Core.Env.t()) ::
          {:ok, generator_info()} | {:error, {:unsupported_hole_type, String.t()}}
  def hole_generator(category, env) when is_binary(category) do
    case Map.fetch(@category_goals, category) do
      {:ok, goal} ->
        generation_env = SigMenu.env_of(:v1)
        ctx = Context.empty(generation_env)
        {:ok, %{category: category, domain: :core, env: env, ctx: ctx, goal: goal, generator: Term.gen_term(ctx, goal)}}

      :error ->
        case native_hole_generator(category, env) do
          {:error, _} -> module_hole_generator(category, env)
          result -> result
        end
    end
  end

  defp native_hole_generator(category, _env) do
    generation_env = SigMenu.env_of(:v1)
    ctx = Context.empty(generation_env)

    case category do
      "Number" ->
        {:ok,
         %{
           category: category,
           domain: :number,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:int_lit, 0}, {:int_lit, 42}, {:float_lit, 0.5}])
         }}

      "Duration" ->
        {:ok,
         %{
           category: category,
           domain: :duration,
           env: generation_env,
           ctx: ctx,
           goal: {:int_type},
           generator: Gen.member_of([{:int_lit, 1}, {:int_lit, 500}, {:int_lit, 1_000_000}])
         }}

      "Code" ->
        {:ok,
         %{
           category: category,
           domain: :code,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator:
             Gen.frequency([
               {2, Gen.member_of([{:int_lit, 0}, {:int_lit, 9}])},
               {2, Term.gen_term(ctx, SigMenu.nat())}
             ])
         }}

      "Identifier" ->
        {:ok,
         %{
           category: category,
           domain: :identifier,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:ctor, :Example, []}, {:ctor, :Worker, []}])
         }}

      "Kind" ->
        {:ok,
         %{
           category: category,
           domain: :core,
           env: generation_env,
           ctx: ctx,
           goal: {:type, 0},
           generator: Term.gen_term(ctx, {:type, 0})
         }}

      "raw until " <> _delimiter ->
        {:ok,
         %{
           category: category,
           domain: :raw,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:raw_text, "0"}, {:raw_text, "item"}, {:raw_text, "item 1"}])
         }}

      _ ->
        {:error, {:unsupported_hole_type, category}}
    end
  end

  defp module_hole_generator(category, env) do
    family_name = String.to_atom(category)

    with true <- Inductive.family?(env, family_name),
         family = Inductive.get_family(env, family_name),
         true <- family.params == [] and family.indices == [],
         ctors = Inductive.ctors_of(env, family_name),
         nullary = Enum.filter(ctors, &(Map.get(&1, :args, []) == [])),
         true <- nullary != [] do
      ctx = Context.empty(env)
      goal = {:data, family_name, [], []}
      terms = Enum.map(nullary, &{:ctor, &1.name, []})

      {:ok,
       %{
         category: category,
         domain: :core,
         env: env,
         ctx: ctx,
         goal: goal,
         generator: Gen.member_of(terms)
       }}
    else
      _ -> {:error, {:unsupported_hole_type, category}}
    end
  end

  @spec sample_holes(String.t(), non_neg_integer(), integer()) ::
          {:ok, generator_info(), [Cure.Core.Term.t()]}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:generated_hole_not_well_typed, term()}}
  def sample_holes(category, count, seed)
      when is_binary(category) and is_integer(count) and count >= 0 and is_integer(seed) do
    sample_holes(category, count, seed, SigMenu.env_of(:v1))
  end

  @spec sample_holes(String.t(), non_neg_integer(), integer(), Cure.Core.Env.t()) ::
          {:ok, generator_info(), [Cure.Core.Term.t()]}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:generated_hole_not_well_typed, term()}}
  def sample_holes(category, count, seed, env)
      when is_binary(category) and is_integer(count) and count >= 0 and is_integer(seed) do
    with {:ok, info} <- hole_generator(category, env),
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
  def check_expansion_proof(macro_def, env, opts \\ []) do
    {result, _manifest, _cached?} = cached_proof(macro_def, env, opts)
    result
  end

  @doc "Return the proof manifest and whether this lookup reused cached work."
  @spec proof_manifest(tuple(), Cure.Core.Env.t(), keyword()) ::
          {:ok, %{cached?: boolean(), rules: [map()]}}
          | {:error, term(), %{cached?: boolean(), rules: [map()]}}
  def proof_manifest(macro_def, env, opts \\ []) do
    {result, manifest, cached?} = cached_proof(macro_def, env, opts)
    report = %{cached?: cached?, rules: manifest}

    case result do
      :ok -> {:ok, report}
      {:error, _} = error -> {:error, error, report}
    end
  end

  @doc "Report every typed hole domain and open category used by a macro."
  @spec category_coverage(tuple(), Cure.Core.Env.t()) :: {:ok, map()}
  def category_coverage({:macro_def, _meta, rules}, env) do
    open_categories =
      rules
      |> Enum.filter(&(&1[:kind] == :open_category))
      |> Enum.map(& &1.name)
      |> Enum.uniq()

    categories =
      rules
      |> Enum.filter(&(&1[:kind] in [:syntax, :computed]))
      |> Enum.flat_map(fn rule ->
        Enum.map(segment_holes(rule.segments), &{&1.kind, rule.keyword})
      end)
      |> Enum.uniq()
      |> Enum.map(fn {category, keyword} ->
        status =
          case hole_generator(category, env) do
            {:ok, info} -> %{status: :supported, domain: info.domain}
            {:error, {:unsupported_hole_type, ^category}} -> %{status: :unsupported, domain: nil}
          end

        Map.merge(%{category: category, keyword: keyword, open: category in open_categories}, status)
      end)

    unsupported = Enum.filter(categories, &(&1.status == :unsupported))

    {:ok,
     %{
       categories: categories,
       open_categories: open_categories,
       unsupported: unsupported,
       complete?: unsupported == []
     }}
  end

  defp cached_proof({:macro_def, _meta, rules} = macro_def, env, opts) do
    key = :erlang.phash2({macro_def, env, Keyword.get(opts, :draws, @default_draws), Keyword.get(opts, :seed, 1)})
    cache = :persistent_term.get(@cache_key, %{})

    case Map.fetch(cache, key) do
      {:ok, {result, manifest}} ->
        {result, manifest, true}

      :error ->
        result = run_expansion_proof(rules, env, opts)
        status = if result == :ok, do: :passed, else: :failed

        manifest =
          for rule <- Enum.filter(rules, &(&1[:kind] in [:syntax, :computed])) do
            %{
              keyword: rule.keyword,
              hole_kinds: rule.segments |> segment_holes() |> Enum.map(& &1.kind),
              draws: Keyword.get(opts, :draws, @default_draws),
              status: status
            }
          end

        :persistent_term.put(@cache_key, Map.put(cache, key, {result, manifest}))
        {result, manifest, false}
    end
  end

  defp run_expansion_proof(rules, env, opts) do
    draws = Keyword.get(opts, :draws, @default_draws)
    seed = Keyword.get(opts, :seed, 1)

    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :computed]))
    |> Enum.reduce_while(:ok, fn rule, :ok ->
      case prove_rule(rule, rules, env, draws, seed) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp prove_rule(rule, rules, env, draws, seed) do
    holes = segment_holes(rule.segments)

    case holes do
      [] ->
        with {:ok, input} <- assemble_use_site(rule, %{}),
             {:ok, expansion} <- expand_generated(rule, rules, input, env) do
          check_expansion(rule.keyword, input, expansion, env)
        end

      _ ->
        with {:ok, bindings} <- sample_bindings(holes, draws, seed, env) do
          Enum.reduce_while(bindings, :ok, fn binding, :ok ->
            case assemble_use_site(rule, binding) do
              {:ok, input} ->
                case expand_generated(rule, rules, input, env) do
                  {:ok, expansion} ->
                    case check_expansion(rule.keyword, input, expansion, env) do
                      :ok ->
                        {:cont, :ok}

                      {:error, {:expansion_ill_typed, details}} ->
                        shrunk = shrink_counterexample(rule, rules, env, binding, details)
                        {:halt, {:error, {:expansion_ill_typed, shrunk}}}
                    end

                  {:error, reason} ->
                    {:halt,
                     {:error, {:expansion_ill_typed, %{keyword: rule.keyword, input: input, kernel_error: reason}}}}
                end

              {:error, _} = error ->
                {:halt, error}
            end
          end)
        end
    end
  end

  defp sample_bindings(holes, draws, seed, env) do
    initial = List.duplicate(%{}, draws)

    Enum.reduce_while(holes, {:ok, initial}, fn %{name: name, kind: kind, repeat: repeat}, {:ok, bindings} ->
      case sample_holes(kind, draws, seed, env) do
        {:ok, _info, terms} ->
          next =
            bindings
            |> Enum.with_index()
            |> Enum.map(fn {binding, index} ->
              value = if repeat, do: [Enum.at(terms, index)], else: Enum.at(terms, index)
              Map.put(binding, name, value)
            end)

          {:cont, {:ok, next}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  defp expand_generated(%{kind: :syntax}, rules, input, _env),
    do: {:ok, Parser.expand_example(rules, input)}

  defp expand_generated(%{kind: :computed}, rules, input, env) do
    rules
    |> Parser.expand_example(input)
    |> MacroExpand.expand(env)
  end

  defp check_expansion(keyword, input, expansion, env) do
    case expansion do
      {:container, _meta, _body} ->
        case Cure.Compiler.ContainerMacro.descriptor(expansion) do
          {:ok, _descriptor} ->
            :ok

          {:error, reason} ->
            {:error,
             {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
        end

      _ ->
        check_expression_expansion(keyword, input, expansion, env)
    end
  end

  defp check_expression_expansion(keyword, input, expansion, env) do
    case Elaborator.elaborate_expr_typed(expansion, [], Context.empty(env), env) do
      {:ok, _term, _type} ->
        :ok

      {:error, reason} ->
        {:error, {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
    end
  end

  defp shrink_counterexample(rule, rules, env, bindings, details) do
    {name, term, info} = first_shrinkable_binding(bindings, env)

    if is_nil(info) do
      Map.put(details, :generated_bindings, bindings)
    else
      shrink_counterexample(rule, rules, env, bindings, details, name, term, info)
    end
  end

  defp shrink_counterexample(rule, rules, env, bindings, details, name, term, info) do
    challenge =
      Challenge.new(
        kind: :typed_term,
        assay: "macro/expansion",
        label: :well_typed,
        seed: 0,
        payload: %{sig: :v1, ctx: [], type: info.goal, term: term}
      )

    pred = fn candidate ->
      candidate_term = candidate.payload.term

      with {:ok, input} <- assemble_use_site(rule, Map.put(bindings, name, candidate_term)),
           {:ok, expansion} <- expand_generated(rule, rules, input, env),
           {:error, {:expansion_ill_typed, _}} <- check_expansion(rule.keyword, input, expansion, env) do
        true
      else
        _ -> false
      end
    end

    shrunk = Shrink.minimize(challenge, pred, 128)

    result =
      Map.merge(details, %{
        generated_bindings: bindings,
        generated_term: term,
        shrunk_term: shrunk.payload.term
      })

    if map_size(bindings) == 1, do: result, else: Map.put(result, :shrunk_hole, name)
  end

  defp first_shrinkable_binding(bindings, env) do
    Enum.find_value(bindings, fn {name, term} ->
      case term do
        {:ctor, _, _} ->
          {:ok, info} = hole_generator_for_term(term, env)

          case info do
            %{goal: goal} when not is_nil(goal) -> {name, term, info}
            _ -> nil
          end

        _ ->
          nil
      end
    end) || {nil, nil, nil}
  end

  defp hole_generator_for_term({:ctor, :Z, []}, env), do: hole_generator("Nat", env)
  defp hole_generator_for_term({:ctor, :S, _}, env), do: hole_generator("Nat", env)
  defp hole_generator_for_term({:ctor, name, []}, env) when name in [:T, :F], do: hole_generator("Bd", env)
  defp hole_generator_for_term(_term, _env), do: {:ok, %{goal: nil}}

  @doc "Assemble a rule's keyword, literals, and named hole fillers into tokens."
  @spec assemble_use_site(map(), %{String.t() => Cure.Core.Term.t()}) ::
          {:ok, [Token.t()]} | {:error, {:unsupported_surface_filler, term()}} | {:error, term()}
  def assemble_use_site(%{keyword: keyword, segments: segments}, bindings)
      when is_binary(keyword) and is_map(bindings) do
    with {:ok, words} <- assemble_words(segments, bindings),
         {:ok, tokens} <- Lexer.tokenize(Enum.join([keyword | words], " "), emit_events: false) do
      tokens = Enum.reject(tokens, &(&1.type == :eof))
      {:ok, append_raw_delimiters(tokens, segments)}
    end
  end

  defp append_raw_delimiters(tokens, segments) do
    if Enum.any?(segments, &match?({:raw_hole, %{delimiter: "dedent"}}, &1)),
      do: tokens ++ [Token.new(:dedent, nil, 1, 1)],
      else: tokens
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

      {:raw_hole, %{name: name}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, term} ->
            case surface_filler(term) do
              {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}
        end

      {:repeat, {:hole, %{name: name}}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, values} when is_list(values) ->
            case Enum.reduce_while(values, {:ok, []}, fn value, {:ok, words} ->
                   case surface_filler(value) do
                     {:ok, text} -> {:cont, {:ok, words ++ [text]}}
                     {:error, _} = error -> {:halt, error}
                   end
                 end) do
              {:ok, words} -> {:cont, {:ok, acc ++ words}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}
        end

      {:optional, group}, {:ok, acc} ->
        case assemble_words(group, bindings) do
          {:ok, words} -> {:cont, {:ok, acc ++ words}}
          {:error, _} = error -> {:halt, error}
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
  defp surface_filler_normal({:data, :Nat, [], []}), do: {:ok, "Nat"}
  defp surface_filler_normal({:data, :Bd, [], []}), do: {:ok, "Bd"}
  defp surface_filler_normal({:raw_text, text}) when is_binary(text), do: {:ok, text}
  defp surface_filler_normal({:int_lit, n}) when is_integer(n), do: {:ok, Integer.to_string(n)}
  defp surface_filler_normal({:float_lit, n}) when is_float(n), do: {:ok, Float.to_string(n)}

  defp surface_filler_normal({:ctor, name, []}) when is_atom(name), do: {:ok, Atom.to_string(name)}
  defp surface_filler_normal(other), do: {:error, {:unsupported_surface_filler, other}}

  defp surface_nat({:ctor, :Z, []}), do: {:ok, 0}

  defp surface_nat({:ctor, :S, [inner]}) do
    with {:ok, n} <- surface_nat(inner), do: {:ok, n + 1}
  end

  defp surface_nat(_other), do: {:error, :not_a_nat}

  defp check_samples(%{ctx: ctx, goal: goal, domain: :core}, terms) do
    goal_value = Eval.eval(goal, Context.env(ctx))

    case Enum.find(terms, &(Kernel.check(ctx, &1, goal_value) != :ok)) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: domain}, terms) when domain in [:number, :duration] do
    case Enum.find(terms, fn
           {:int_lit, _} -> false
           {:float_lit, _} -> domain != :number
           _ -> true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{ctx: ctx, domain: :code}, terms) do
    case Enum.find(terms, fn term ->
           not (match?({:ok, _}, Kernel.infer(ctx, term)) and match?({:ok, _}, surface_filler(term)))
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :raw}, terms) do
    case Enum.find(terms, &(not match?({:raw_text, text} when is_binary(text), &1))) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :identifier}, terms) do
    case Enum.find(terms, &(not match?({:ctor, name, []} when is_atom(name), &1))) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp segment_holes(segments) when is_list(segments), do: Enum.flat_map(segments, &segment_holes/1)

  defp segment_holes({:hole, %{name: name, kind: kind}}),
    do: [%{name: name, kind: kind, repeat: false}]

  defp segment_holes({:raw_hole, %{name: name, delimiter: delimiter}}),
    do: [%{name: name, kind: "raw until " <> delimiter, repeat: false}]

  defp segment_holes({:repeat, {:hole, %{name: name, kind: kind}}}),
    do: [%{name: name, kind: kind, repeat: true}]

  defp segment_holes({:optional, segments}), do: segment_holes(segments)
  defp segment_holes(_segment), do: []
end
