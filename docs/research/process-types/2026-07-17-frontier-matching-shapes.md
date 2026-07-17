# The G9 frontier — refined shape and matching fills across cloned PL formalizations

*2026-07-17. Cloning the mailbox-type checker `mbcheck` (Fowler–Gay–Padovani) and reading its
algorithm SHARPENED the frontier far past my initial set-lattice sketch, and — with mathlib,
Lean core, Actris, and PLFA all cloned to `~/Develop` — every structural part now has a
concrete matching shape to port. Only ONE piece has no external match.*

## The refined frontier shape (from `~/Develop/mbcheck`)

My `Std.Otp.Inference` used accepted-SETS (`TagList`, `Handles`/`AllHandled`). That is the
QUALITATIVE fragment. The real mailbox type is QUANTITATIVE:

- A mailbox type is a **commutative regular expression** ("pattern"): `1` (empty), `t` (one
  message of tag t), `E + F` (choice), `E · F` (both, IN ANY ORDER — commutative), `*E`
  (many). `mbcheck/lib/common/type.ml` `Pattern`. It denotes the MULTISET pattern of messages,
  order-insensitive. Receive computes the **Brzozowski derivative** of the pattern wrt the
  received tag (`type.ml` "pattern derivative wrt. a message tag").
- Inference is **bidirectional constraint generation** — `mbcheck/lib/typecheck/gen_constraints.ml`
  `synthesise_comp : … -> Type.t * Ty_env.t * Constraint_set.t` / `check_comp` — a fold over the
  IR producing a constraint set over pattern/type variables.
- Solving is **Presburger arithmetic over semilinear sets** — commutative-regex inclusion /
  emptiness is a Parikh/semilinear-set problem, discharged by an external **Z3** backend
  (`solve_constraints.ml`, `z3_solver.ml`, `presburger.ml`).

So the "least fixpoint over a finite set lattice" I sketched is the shadow; the real inference
is constraint-generation → Presburger solving over commutative-regex patterns, with recursion
closed by a fixpoint.

## Matching-shape map (all references cloned to `~/Develop`)

| Frontier part | Shape | Matching fill (repo · module) |
|---|---|---|
| Mailbox type = commutative regex + derivatives | pattern algebra, Brzozowski deriv | **mathlib** `Computability/RegularExpressions.lean` (`deriv`, `matches'`, `star`/`plus`/`comp`) — the commutative twist is Parikh (below) |
| Constraint SOLVING (pattern inclusion/emptiness) | Presburger / Parikh / semilinear sets | **mathlib** `ModelTheory/Arithmetic/Presburger/Semilinear/{Basic,Defs}.lean` + `Presburger/{Basic,Definability}.lean` — *Presburger + semilinear sets are formalized*; decision procedure = **Lean core** `Init/Omega/*` + `Lean/Elab/Tactic/Omega` (the QF-Presburger fragment Z3 solves) |
| Constraint GENERATION (the fold) | bidirectional synth/check → constraints | **mbcheck** `lib/typecheck/gen_constraints.ml` (the reference algorithm); **PLFA** bidirectional typing (`~/Develop/plfa`, proof pattern) |
| Recursion (`rec X.b` → transfer fixpoint) | lfp of a continuous map / ωCPO | **mathlib** `Order/FixedPoints.lean` + `Order/OmegaCompletePartialOrder.lean` (`ωSup_iterate_mem_fixedPoint`); **Lean core** `Init/Internal/Order/Basic.lean` (CCPO) + `PartialFixpoint/` |
| Transfer MONOTONICITY (semantic adequacy of the fold) | compositional per-former monotone | **Lean core** `Lean/Elab/Tactic/Monotonicity.lean` (`monotoneExt`, `[partial_fixpoint_monotone]`) + `Init/Internal/Order/Basic` |
| Session-typing meta / message-passing logic | behavioural typing + adequacy | **Actris** `~/Develop/actris` (Coq/Iris) — dependent session protocols over message passing |

## What has NO external match — the one genuinely novel theorem

**Operational adequacy against the OTP reduction.** mbcheck proves soundness for *Pat's* calculus.
The novel piece for THIS project is tying `infer(behaviour)` to the metatheory already built:
that the inferred pattern is exactly the mailbox type under which `Std.Otp.Preservation` /
`Std.Otp.Safety` / `Std.Otp.HetRouting` hold — i.e. inference computes a type at which the OTP
reduction never delivers an unhandled message. Everything MECHANICAL (patterns, derivatives,
constraint gen, Presburger solving, the fixpoint, monotonicity) ports from the six references
above; the ADEQUACY connecting inference to the operational safety theorems is the contribution
a full G9 push would make, and it has no shape to clone — it must be proved against the
`Std.Otp.*` reduction relations in this repo.

## Cloned references (`~/Develop`)

- `mathlib4` — `Order/FixedPoints`, `Order/OmegaCompletePartialOrder`, `Computability/RegularExpressions`,
  `ModelTheory/Arithmetic/Presburger/Semilinear`, `CategoryTheory/Endofunctor/Algebra`.
- `lean4` (already present) — `Init/Omega/*`, `Lean/Elab/Tactic/{Omega,Monotonicity}`,
  `Init/Internal/Order/Basic`, `Lean/Elab/PreDefinition/PartialFixpoint/`.
- `mbcheck` — the reference mailbox-type inference ALGORITHM (constraint gen + Z3/Presburger).
- `plfa` — bidirectional type inference + operational semantics + adequacy (proof pattern).
- `actris` — Coq/Iris dependent session types (message-passing meta).
- `pat-exercise-solutions` — Pat mailbox-typing worked examples.

No Coq/Agda/opam toolchains are installed; these are cloned for READING/porting shapes (as
mathlib was), not building.
