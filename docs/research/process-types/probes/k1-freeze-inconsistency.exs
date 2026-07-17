alias Cure.Core.{Builtins, Context, Env, Normalise, Conv, Eval}
u = Cure.Core.Grade.unrestricted()
nat = {:data, :Nat, [], []}
z = {:ctor, :Z, []}
s = fn x -> {:ctor, :S, [x]} end
m = {:data, :M, [], []}
mkm = fn a -> {:ctor, :MkM, [a]} end
unit = {:data, :Unit, [], []}
mku = {:ctor, :MkU, []}

# plus a b = case a { Z -> b | S k -> S (plus k b) }
plus_body =
  {:lam, u, nat,
   {:lam, u, nat,
    {:case, {:var, 1}, {:lam, u, nat, nat},
     [{:Z, 0, {:var, 0}}, {:S, 1, s.({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}]}}}
plus_type = {:pi, u, nat, {:pi, u, nat, nat}}
plus = fn a, b -> {:app, {:app, {:global, :plus}, a}, b} end

# g u = case u { MkU -> MkM Z }   (mirrors recvs(LEnd))
g_body = {:lam, u, unit, {:case, {:var, 0}, {:lam, u, unit, m}, [{:MkU, 0, mkm.(z)}]}}
g_type = {:pi, u, unit, m}

# combine m n = case m { MkM a -> case n { MkM b -> MkM (plus a b) } }   (mirrors msum)
combine_body =
  {:lam, u, m,
   {:lam, u, m,
    {:case, {:var, 1}, {:lam, u, m, m},
     [{:MkM, 1,
       {:case, {:var, 1}, {:lam, u, m, m}, [{:MkM, 1, mkm.(plus.({:var, 1}, {:var, 0}))}]}}]}}}
combine_type = {:pi, u, m, {:pi, u, m, m}}

env =
  Builtins.seed(Env.empty())
  |> Env.add_def(:plus, plus_type, plus_body)
  |> Env.certify(:plus)
  |> Env.add_def(:g, g_type, g_body)
  |> Env.certify(:g)
  |> Env.add_def(:combine, combine_type, combine_body)
  |> Env.certify(:combine)

ctx = Context.extend(Context.empty(env), m)   # one free var of type M => {:var, 0}

comb = fn x, y -> {:app, {:app, {:global, :combine}, x}, y} end
a_term = comb.(mkm.(z), {:var, 0})   # combine (MkM Z) x
b_term = comb.({:app, {:global, :g}, mku}, {:var, 0})   # combine (g MkU) x

IO.puts("=== g(MkU) alone whnf ===")
IO.inspect(Normalise.whnf(ctx, {:app, {:global, :g}, mku}), label: "whnf g(MkU)")
IO.puts("=== A = combine(MkM Z, x) nf ===")
nfa = Normalise.nf(ctx, a_term)
IO.inspect(nfa, label: "nf A")
IO.puts("=== B = combine(g MkU, x) nf ===")
nfb = Normalise.nf(ctx, b_term)
IO.inspect(nfb, label: "nf B")
IO.puts("=== equal? ===")
IO.inspect(nfa == nfb, label: "nf A == nf B")
IO.inspect(Conv.conv?(a_term, b_term, Context.env(ctx), Context.length(ctx), Context.signature(ctx)),
  label: "conv?(A,B)")
