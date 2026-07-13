# Cure Glossary — for Newcomers

This glossary explains the vocabulary you'll meet reading Cure's docs, compiler,
and error messages: the dependent-type-theory core, the everyday standard-library
value surface, the BEAM/concurrency words, and the toolchain/metatheory terms.
Every term here actually occurs somewhere in this repo, and every entry carries a
short worked example in Cure.

**It is telescope-sorted.** Entries are ordered so that *every definition uses
only terms already defined above it* — read top to bottom and you should never hit
a word you haven't seen. (The name is the type-theory *telescope*: a chain where
each thing may depend only on the earlier ones.) The ordering is enforced by
`docs/check_glossary_telescope.py` — run it after editing; it flags any entry that
references a term defined further down.

**Layer 0 is notation, not concepts:** it teaches just enough Cure syntax to read
the examples, so the examples themselves never get ahead of you. A few genuinely
circular ideas (type/value, scope/binder, proposition/proof) are introduced as
pairs, since neither can honestly come first.

**Contents**

- Layer 0 — Reading the examples (Cure syntax)
- Layer 1 — Types and universes
- Layer 2 — Data and pattern matching
- Layer 3 — Dependent types
- Layer 4 — Variables, binding, and resources
- Layer 5 — Computation and equality
- Layer 6 — How the compiler reads your code
- Layer 7 — Guarantees the compiler enforces
- Layer 8 — Propositions and proofs
- Layer 9 — Typeclasses and the value surface
- Layer 10 — The trust boundary and the FFI
- Layer 11 — The BEAM: processes and concurrency
- Layer 12 — Toolchain and metatheory

**The field in one sentence:** in a *dependent* type system, types may mention
*values*, so a type can state a specific, checkable fact about a thing — "a list of
exactly 3 numbers," not merely "a list" — and the compiler checks that fact the way
an ordinary compiler checks you didn't add a string to an integer.

---

## Layer 0 — Reading the examples (Cure syntax)

Not concepts — just the notation the code blocks below use. Skim it once and the
examples read themselves.

- `mod Std.Foo` … — a **module**; `use Std.Foo` imports one.
- `fn name(x: T, y: U) -> R = body` — a function: parameters with types, a return
  type after `->`, body after `=`.
- `{a: Type}`, `{n: Nat}` — **implicit** parameters in braces; the compiler fills
  them in, you don't pass them.
- `type Name = A | B(T)` — a data type with constructors `A` and `B`.
- `match x` then indented `Pattern -> result` lines — inspect `x` by constructor.
- `pickup` then indented `condition -> result` lines with a final `else ->` —
  guard/branch on boolean conditions.
- `let v = expr` — bind a local name.
- `expr |> f` — pipe: `f(expr)`, left to right.
- `[1, 2, 3]`, `[head | tail]`, `[]` — list literal, cons, empty.
- `%[a, b]` — a tuple literal.
- `Point{x: 1, y: 2}`, `p.x`, `Point{p | x: 3}` — build / read / copy-update a record.
- `:ok`, `:"Cure.Turnstile"` — **atoms** (interned symbolic constants).
- `## text` is a doc comment; `# text` is an inline comment (used for `# => result`).
- `@extern(...)`, `@group(:g)`, `@builtin(:nat)`, `@derive(JSON)` — **attributes**
  attached to the declaration below them.
- `-> R ! Io` — a return type with an **effect** annotation (`! Io`).

---

## Layer 1 — Types and universes

**Type** — A description of what a value is and what you may do with it. In Cure a
type is itself just another term the compiler can compute with — which is why
(later) types will be allowed to contain values.

```cure
fn double(x: Int) -> Int = x * 2      # Int is the type of x and of the result
```

**Universe** *(also **sort**, **kind**)* — The "type of types." If `Int` is a type,
the type *of* `Int` is a universe, written `Type`. Universes are stacked in levels
so no universe contains itself (that would be paradoxical).

```cure
type Option(t) = Some(t) | None()     # t ranges over Type: Option takes a *type*
```

**Cumulativity** — The convenience rule that anything in a lower universe also
counts as living in a higher one, so you rarely think about universe levels.

```cure
# A value usable where Type is expected is also usable where a higher Type is —
# you never write a level annotation for ordinary code.
```

---

## Layer 2 — Data and pattern matching

**Inductive type** — A type defined by listing the ways to build its values, where
those ways may refer back to the type itself. `Nat`, lists, and trees are all
inductive.

```cure
type Nat = Z | S(Nat)                 # a Nat is zero, or the successor of a Nat
```

**Constructor** *(often **ctor**)* — One of the named ways to build a value of an
inductive type. Every value is a constructor applied to arguments.

```cure
S(S(Z))                               # the constructor S applied twice to Z  (= 2)
```

**Nat / Peano / successor / zero** — `Nat` is the counting numbers 0, 1, 2, … The
**Peano** encoding builds them from **zero** (`Z`) and **successor** (`S`). Cure
stores literals compactly so large numbers don't blow up.

```cure
fn plus(m: Nat, n: Nat) -> Nat =
  match m
    Z()  -> n
    S(k) -> S(plus(k, n))
```

**List** — The everyday inductive sequence: empty (`Nil`, written `[]`) or an
element in front of a list (`Cons`, written `[h | t]`).

```cure
type List(a) = Nil | Cons(a, List(a))
[1, 2, 3]                             # sugar for Cons(1, Cons(2, Cons(3, Nil)))
```

**Pattern / match / scrutinee** — A **match** inspects a value (the **scrutinee**)
by which constructor built it and branches; each branch's left side is a
**pattern**. Like `switch`, but here matching can *teach the compiler new facts* in
each branch (you'll see how once dependent types arrive).

```cure
fn is_empty(xs: List(t)) -> Bool =
  match xs                            # xs is the scrutinee
    []      -> true                   # pattern for Nil
    [_ | _] -> false                  # pattern for Cons
```

**Coverage / exhaustiveness** — The check that a match handles *every* constructor,
with no case forgotten.

```cure
match xs
  [] -> 0
  # omitting the [_|_] case is a coverage error: not exhaustive
```

---

## Layer 3 — Dependent types

**Dependent type** — A type that *depends on* (mentions) a value. Ordinary types are
`List` or `Int`; a dependent type can say `Vector(Int, 3)` — a list whose *length is
part of its type*. Because the type carries a real fact, the compiler can reject
`head(empty)` before the program runs. This is what Cure is built around.

```cure
fn head({a: Type}, {n: Nat}, xs: Vector(a, S(n))) -> a    # only accepts non-empty
```

**Family / indexed family** — A whole *collection* of related types from one
definition, told apart by an **index**. `Vector(T, n)` is a family: each length `n`
gives a different type. The index is the value the type depends on.

```cure
Vector(Int, 0)   # one type in the family …
Vector(Int, 1)   # … a different type in the same family
```

**Vector** — A list whose length is part of its type, `Vector(a, n)`; the running
example of a dependent type. Its constructors *refine the length index*.

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

**Fin / Bounded** — `Fin(n)` (Cure's underlying type is **Bounded**) is the type of
numbers *strictly less than `n`* — a provably in-range index. With a `Vector(a, n)`
and a `Bounded(n)`, indexing can never go out of bounds, and the compiler knows it.

```cure
fn lookup({a: Type}, {n: Nat}, xs: Vector(a, n), index: Bounded(n)) -> a
# no default, no Option, no bounds check: Bounded(n) *is* the proof it's in range
```

**Pi type** (Π) — A *dependent function type*: the **return type** depends on the
*value* passed in. Ordinary `Int -> Int` is the special case where it doesn't.

```cure
fn replicate({a: Type}, n: Nat, x: a) -> Vector(a, n)     # result type mentions n
```

**Sigma type** (Σ) — A *dependent pair* `(a, b)` where the type of `b` may depend on
the *value* of `a`. "A length `n`, together with a `Vector(T, n)`."

```cure
# (n: Nat, Vector(Int, n)) — the second component's type is decided by the first.
# Cure packages these with Std.Sigma.
```

**Telescope** — A chain of parameters where each may mention the earlier ones. The
name is the picture — and this glossary is ordered the same way.

```cure
# (n: Nat, xs: Vector(Int, n), i: Bounded(n)) — each segment sees the ones before it
```

**GADT** (Generalized Algebraic Data Type) — An inductive type whose constructors
each produce a *different, more specific* member of the family. If a plain inductive
type is an ordinary enum, a GADT lets each case refine the index — exactly what
`Vector`'s `empty : Vector(a, Z)` and `prepend : … -> Vector(a, S(n))` do.

```cure
empty   : Vector(a, Z)        # this constructor forces the index to Z
prepend : a -> Vector(a, n) -> Vector(a, S(n))   # this one forces it to S(n)
```

**Motive** — A match's *return-type recipe*: what type each branch produces, *as a
function of the scrutinee*. Dependent matches need it because branches can have
differently-typed results.

```cure
# Matching Z vs S(k) can land in different types; the motive says which per branch.
match n
  Z()  -> empty()               # : Vector(a, Z)
  S(k) -> prepend(x, rest)      # : Vector(a, S(k))
```

**Eliminator** — The primitive, fully general "consume a value of an inductive type"
(a fold/recursor). Surface `match` is elaborated down to eliminators, and the motive
is one of an eliminator's inputs.

```cure
# You write `match`; the compiler lowers it to Nat's eliminator with your motive.
```

---

## Layer 4 — Variables, binding, and resources

**Scope** — The region of code where a name is meaningful. Delicate here because
types *in* scope may mention values *in* scope.

```cure
fn f(x: Int) -> Int = x + 1     # x is in scope only inside f's body
```

**Binder** — Anything that introduces a variable with a scope: a function parameter,
a `let`, a pattern variable.

```cure
let y = 3                       # `let` binds y; the pattern S(k) below binds k
match n
  S(k) -> k                     # S(k) binds k inside this branch
```

**Lambda / abstraction / application** — A **lambda** (or **abstraction**) is an
anonymous function; **application** is calling one.

```cure
map([1, 2, 3], fn(x) -> x * x)   # fn(x) -> … is a lambda; map applies it
```

**Substitution** — Replacing a variable with a term everywhere it occurs — what
happens when a function meets its argument.

```cure
# applying fn(x) -> x + 1 to 4 substitutes x := 4, giving 4 + 1
```

**de Bruijn index** — Representing a variable by *how many binders out* it lives
(0 = nearest) instead of by name, so substitution is immune to name clashes. You see
it in the kernel, never in source.

```cure
# Source `fn(x) -> fn(y) -> x` stores x as "1" (skip y) internally — no names.
```

**Erasure / erased** — Deleting the parts that existed only for type-checking before
generating run-time code. `Vector(a, n)`'s length `n` proves things at compile time
but isn't needed at run time, so it's **erased** — dependent code stays fast.

```cure
# At run time a Vector is just its spine: :empty / {:prepend, head, tail}.
# The length index n is gone — it did its job in the type checker.
```

**QTT (Quantitative Type Theory) / grades** — Cure records *how many times* each
variable is used, as a **grade** on every binder:

| Grade | Meaning | Used |
|-------|---------|------|
| `erased` | `0` | never at run time — compile-time only, then erased |
| `linear` | `1` | exactly once |
| `affine` | `≤1` | at most once (may be dropped) |
| `unrestricted` | `ω` | freely — the default |

This makes erasure *checked*: an `erased` variable is guaranteed unused at run time.
Grades live in the kernel today (no surface syntax yet).

```cure
# The n in Vector(a, n) carries grade `erased`: present for typing, gone at run time.
```

**Context** — The compiler's running record of "what's in scope, at what type, and at
what **grade**" at a point. Type-checking always happens relative to a context.

```cure
# Inside head(xs) the context holds: a : Type, n : Nat, xs : Vector(a, S(n)).
```

---

## Layer 5 — Computation and equality

**Reduction / redex** — A single computation step is a **reduction**; a **redex**
("reducible expression") is a spot where one can happen. The five named rules that
follow — one entry each — are the kinds of reduction Cure performs.

```cure
(fn(x) -> x + 1)(4)      # this application is a redex; it reduces to 4 + 1
```

**beta** — Apply a lambda to its argument (substitute) — the core "run one step."

```cure
(fn(x) -> x + 1)(4)      # beta →  4 + 1
```

**eta** — Treat `f` and `fn(x) -> f(x)` as equal: a function *is* its behavior.

```cure
fn(x) -> plus(m, x)      # eta-equal to  plus(m)  (partial application)
```

**delta** — Unfold a top-level definition to its body.

```cure
plus(Z, n)               # delta-unfolds `plus` to its match expression
```

**iota** — Reduce a pattern match once the scrutinee's constructor is known.

```cure
match Z()                # iota →  the Z branch's result
  Z()  -> n
  S(k) -> S(plus(k, n))
```

**zeta** — Substitute a `let`-bound value.

```cure
let y = 3
y * y                    # zeta substitutes y := 3, giving  3 * 3
```

**Neutral term** — An expression stuck because it's blocked on an unknown; it can't
reduce until the unknown is known, so the compiler keeps it symbolically.

```cure
plus(k, n)               # with k a variable, this is neutral — no rule applies yet
```

**Spine** — A function together with its stack of applied arguments, as one unit.

```cure
lookup(xs, i)            # head `lookup` with spine [xs, i]
```

**Normalization / normalise** — Reduce a term to its simplest, fully-computed form
by applying reductions until no redex remains.

```cure
plus(S(Z), S(Z))         # normalises to  S(S(Z))
```

**WHNF** (Weak Head Normal Form) — A *partial* normal form: compute just enough to
reveal the outermost constructor, leaving the insides untouched. Often that's all a
decision needs, and it's cheaper. Ubiquitous in the kernel.

```cure
plus(S(Z), n)            # WHNF is  S(plus(Z, n))  — head S(…) exposed, inside left alone
```

**Reify** — Turn an internal/computed representation back into an ordinary term to
print or inspect (the opposite of evaluating).

```cure
# The kernel evaluates a type to a value, then reifies it back to text for an error.
```

**Definitional equality** *(also **judgmental** equality)* — Two terms are
definitionally equal when they *compute* to the same normal form. Settled silently,
by evaluation.

```cure
Vector(Int, 2 + 2)       # accepts a 4-vector: 2 + 2 is definitionally 4
```

**Conversion** — The compiler's check that two types (or terms) are interchangeable,
i.e. definitionally equal. Passing a value succeeds when its type *converts* with the
expected type.

```cure
# A Vector(Int, 4) is accepted where Vector(Int, 2+2) is expected — they convert.
```

**Congruence** — Equality survives being built upon: if `a = b`, then `f(a) = f(b)`.
A basic ingredient the conversion check relies on.

```cure
# From m = n, the checker gets S(m) = S(n) for free.
```

---

## Layer 6 — How the compiler reads your code

**Type inference / infer** — The compiler working out a type you didn't write.

```cure
let n = 3                # inferred: n : Int
```

**Bidirectional checking (check vs. synthesize)** — Sometimes the compiler knows the
type it *expects* and only **checks** against it; sometimes it must **synthesize**
the type from the expression alone. "Check mode" errors mean *"you didn't meet my
expectation"*; "synthesize mode" means *"I couldn't discover the type."*

```cure
fn f() -> Int = some_call()     # check: some_call() is checked against Int
some_call()                     # synthesize: type discovered from some_call
```

**Elaboration / elaborator / elaborate** — Turning the friendly source you wrote into
the fully-explicit, fully-checked internal form: filling in omitted types, resolving
what was left implicit, and verifying every dependent claim. The **elaborator** is
the part of Cure that does this — the heart of the compiler, and the word you'll see
most in errors.

```cure
singleton(5)             # elaborated to singleton({Int}, 5): the implicit {a} filled in
```

**Implicit argument** — An argument the compiler fills in rather than one you type.

```cure
singleton(5)             # the {a: Type} is implicit — you never write Int here
```

**Ascription** — Writing an explicit type on an expression to guide or document it.

```cure
(3 : Nat)                # ascribe: read the 3 at type Nat, not the default Int
```

**Coercion** — A safe conversion the compiler inserts automatically so two things
line up. You usually don't see them.

```cure
'a'                      # a Char coerces to its code point (Int) where needed
```

**Metavariable / metavar** — A placeholder "unknown" the compiler invents for
something not yet solved (often an implicit or omitted type), written like `?m`.

```cure
singleton(5)             # element type starts as ?a, to be solved
```

**Unification / unify / unifier** — Making two terms equal by *solving* for their
metavariables — "what must `?m` be for these to match?" Most inference is unification.

```cure
singleton(5)             # unifies ?a with Int (from the argument 5)
```

**Hole** — A deliberate gap you leave where you don't yet have the term; the compiler
replies with the expected type and what's in scope.

```cure
fn f(n: Nat) -> Nat = ?goal     # compiler reports:  ?goal : Nat,  with n : Nat in scope
```

---

## Layer 7 — Guarantees the compiler enforces

**Termination / size-change** — The check that a recursive function actually *stops*.
Cure uses **size-change termination**: something must get strictly smaller on every
recursive call.

```cure
fn plus(m: Nat, n: Nat) -> Nat =
  match m
    S(k) -> S(plus(k, n))       # recurses on k, strictly smaller than S(k): terminates
```

**Totality / total** — A function is **total** if it's defined for *all* inputs and
always finishes: no crashes, no missing cases, no infinite loops. Totality =
**coverage** + **termination**. Cure cares because a non-terminating "proof" could
prove anything.

```cure
# plus is total: every Nat is matched (coverage) and recursion shrinks (termination).
```

**Positivity** — A restriction on how an inductive type may refer to itself (roughly:
not "to the left of an arrow" in a way that smuggles in a loop). It keeps inductive
definitions sound.

```cure
type Bad = Mk(Bad -> Bad)       # rejected: self-reference left of -> fails positivity
```

**Canonicity** — Every closed, fully-computed value of a data type really *is* one of
its constructors — the guarantee that the types don't lie at run time.

```cure
# Any closed Nat normalises to Z or S(...) — never gets stuck as something else.
```

---

## Layer 8 — Propositions and proofs

**Proposition** — A statement that could be true, expressed *as a type*. The slogan
"propositions as types" means a proposition is a type and a **proof** of it is a
value of that type.

```cure
# `Equivalent(Nat, plus(n, Z), n)` is the proposition "n + 0 equals n."
```

**Proof / witness** — A value inhabiting a proposition-type — evidence it holds.
"**Witness**" stresses it's a concrete example making the claim true.

```cure
reflexive(Z)             # a proof (witness) that Z equals Z
```

**Propositional equality / identity type** — The type of *proofs that two values are
equal* (in Cure, `Equivalent(T, a, b)`). Unlike definitional equality (settled by
computation), this is a fact you hold as a *value* and pass around.

```cure
fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n)     # a provable equality
```

**refl / reflexive** — Reflexivity: the built-in proof that any value equals itself.
The seed all equality proofs grow from.

```cure
reflexive(S(k))          # proof that S(k) = S(k)
```

**transport** — Move a value from one type to an equal type using an equality proof:
given `a = b` and a `P(a)`, get the corresponding `P(b)`.

```cure
# Given a proof n = m, transport turns a Vector(a, n) into a Vector(a, m).
```

**rewrite** — Use an equality proof to *replace* one side with the other inside a
goal. In Cure it's `rewrite proof in expr`; it's sugar over transport.

```cure
S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))   # swap plus(k,Z) for k, then close
```

**UIP / axiom K** — Uniqueness of Identity Proofs: any two proofs of `a = b` are
themselves equal — "equality has at most one proof." Cure adopts it; it keeps
equality reasoning simple.

```cure
# Any two witnesses of Equivalent(Nat, x, y) are interchangeable.
```

**Decidable** — A property is *decidable* if a **total** procedure always answers
yes-or-no *with a proof either way*.

```cure
# Nat equality is decidable: you can always compute equal/not-equal with evidence.
```

**Absurd / impossible** — A case that *cannot happen* because it would contradict the
types. Cure lets you discharge such a branch as impossible, and *checks* that it
truly is.

```cure
fn head({a: Type}, {n: Nat}, xs: Vector(a, S(n))) -> a =
  match xs
    prepend(x, _) -> x    # no `empty` case: it's impossible at type Vector(a, S(n))
```

---

## Layer 9 — Typeclasses and the value surface

**Typeclass / interface / instance / implementation** — A **typeclass** (Cure spells
it `interface`) is a set of operations a type can support; an **instance**
(`implementation`) provides them for a specific type. The compiler picks the right
instance for you.

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = int_to_string(x)
```

**Coherence** — The guarantee that a type has *one* agreed-upon instance, so meaning
doesn't depend on which implementation was found. Cure enforces it globally.

```cure
# There is exactly one `Show for Int`; every `show(n: Int)` in the program agrees.
```

**Ordering** — The three-way comparison result, `LessThan | EqualTo | GreaterThan`.

```cure
type Ordering = LessThan | EqualTo | GreaterThan
```

**String** — Text, defined as `List(Char)` (a `Char` is `Bounded(0x110000)`, a
provably-valid code point). Because a string *is* a list, list operations and
concatenation work on it directly.

```cure
length("hello")          # => 5   (code points, not bytes)
```

**Comparable / compare** — The total-ordering interface: one method `compare`
returning an `Ordering`. The operators `<`, `>`, `<=`, `>=` route through it.

```cure
compare(1, 2)            # => LessThan
"ada" < "grace"          # => true   (desugars to compare(...) == LessThan)
```

**Equatable** — The equality interface: `eq` (and `ne`), surfaced as `==`.

```cure
eq(1, 1)                 # => true
:ok == :ok               # => true
```

**Semigroup / combine** — Types with an associative `combine`. `x <> y` desugars to
`combine(x, y)`; a non-numeric `x + y` does too. The `List` instance is append, and
since `String = List(Char)`, string concat rides the same instance.

```cure
combine([1, 2], [3, 4])  # => [1, 2, 3, 4]
"ab" <> "cd"             # => "abcd"
```

**Show** — The interface for rendering a value as a `String`.

```cure
show(42)                 # => "42"
show(:ok)                # => ":ok"
```

**Option / Some / None** — An optional value: present (`Some(v)`) or absent
(`None()`). The standard "value that might be absent" type.

```cure
type Option(t) = Some(t) | None()
unwrap(none(), 0)        # => 0
```

**Result / Ok / Error** — A computation that either succeeded (`Ok(v)`) or failed
(`Error(e)`). The standard "this can fail" type.

```cure
type Result(t, e) = Ok(t) | Error(e)
ok(42) |> map(fn(x) -> x * 2) |> unwrap(0)   # => 84
```

**Map** — A key/value dictionary built through functions (no literal syntax).

```cure
let m = put(:age, 42, put(:name, "Ada", new()))
get(:name, m)            # => "Ada"
```

**Set** — A collection of distinct elements (built over `Map` with `true` values).

```cure
let s = add(:x, add(:y, new()))
member(:x, s)            # => true
```

**Iter / iterator** — A *lazy* sequence: elements are produced on demand rather than
materialised up front (the lazy counterpart to `List`).

```cure
from_list([1, 2, 3, 4, 5]) |> map(fn(x) -> x * x)   # squares, computed lazily
```

**record** — A product type with named fields; build, read, and copy-update with
brace syntax (see Layer 0).

```cure
let p = Point{x: 1, y: 2}
p.x                      # => 1
Point{p | y: 9}          # copy of p with y replaced
```

---

## Layer 10 — The trust boundary and the FFI

Where you tell the compiler "trust me." Cure ships `cure audit trust` to list every
such place.

**Axiom / postulate** — A fact asserted *without proof*: you declare its type and the
compiler believes it. Needed to reach the outside world, but each one is something
you're *trusting*, not something Cure verified.

```cure
@extern(:cure_std_nat, :of_int, 1)
fn of_int(i: Int) -> Nat        # signature believed, body lives outside Cure
```

**@extern / FFI** — The Foreign Function Interface: `@extern(module, function,
arity)` compiles a Cure function to a *direct Erlang/BEAM call*. It's how axioms
target real code — NIFs (`gpio`, `uart`), OTP, or Cure's own runtime helpers.

```cure
@extern(:erlang, :self, 0)
fn raw_self() -> Any
```

**believe_me** — An unchecked coercion that forces the compiler to accept a value at
a type it couldn't verify. The bluntest escape hatch, used sparingly (e.g. behind
Cure's opaque `Any`).

```cure
# Used inside the stdlib to cast an opaque Any to a known shape without a proof.
```

**Opaque** — A type deliberately hidden behind an interface so its innards can't be
inspected or relied on; you touch it only through the operations provided.

```cure
# `Any` is opaque: you can hold and pass it, but not pattern-match its structure.
```

**Primitive / delta-global** — A built-in the compiler knows directly rather than one
written in Cure. A **delta-global** is such a definition the kernel can unfold on
demand (the *delta* reduction from Layer 5).

```cure
2 + 2                    # + is a primitive op; a function like plus/2 is a delta-global
```

---

## Layer 11 — The BEAM: processes and concurrency

Cure runs on the BEAM (the Erlang VM), so its concurrency is BEAM concurrency, made
typed. The checked `Std.Otp` algebra is the source-level process boundary.

**Process** — An independent, isolated unit of execution with its own memory,
communicating only by messages. The BEAM runs many cheaply.

```cure
fn start() -> Effect(Tuple) = beam_ops start_link :worker []
```

**Pid** — A **process identifier**: a handle to a running process, used to message
or stop it.

```cure
fn me() -> Effect(Pid(Atom)) = beam_ops self
```

**Atom** — An interned symbolic constant, written `:name`. Cheap to compare; used for
tags, states, and module names.

```cure
:ok
:"Cure.Turnstile"                        # a module name as an atom
```

**Any** — The opaque "some BEAM value of unchecked shape" type, permitted only at an
explicit raw BEAM or FFI boundary.

```cure
fn raw_boundary(value: Any) -> Any
```

**Message / send** — Processes communicate by sending values to a typed `Pid(m)`;
the checker requires the message to have type `m`.

```cure
beam_ops tell pid :coin                  # checked before emission
```

**beam_ops** — An auto-preluded standard-library syntax macro that expands to
ordinary checked `Std.Otp` calls. It has no compiler-owned operation table.

```cure
fn start() -> Effect(Tuple) = beam_ops start_statem :"Cure.Turnstile" [0]
```

**Effect (`Effect(T)`)** — The inert type former for an effectful result. A BEAM
operation returns `Effect(T)` and an effectful `let` sequences it.

```cure
fn current() -> Effect(Pid(Atom)) = beam_ops self
```

**fsm (finite state machine)** — An auto-preluded standard-library macro that
expands to a generic lifted module with `gen_statem` callbacks. Transition rows
are checked Cure values, not a compiler parser.

```cure
fsm Cure.Turnstile state Int transitions [
  transition :locked :coin :unlocked,
  transition :unlocked :push :locked
]
```

**actor** — A standard-library macro that expands to a generic lifted module
with checked `gen_server` callbacks and a typed message surface.

```cure
actor Cure.Store state Atom messages Atom handle_info
  %[:noreply, state]
```

**supervisor** — A standard-library macro that expands to a generic lifted module
whose checked `init/1` returns ordinary BEAM child specifications.

```cure
sup Cure.Root children [child_spec Cure.Worker :worker]
```

---

## Layer 12 — Toolchain and metatheory

**TCB (Trusted Computing Base) / kernel** — The small set of files whose correctness
everything rests on: the dependent **kernel** (type checker + conversion). Everything
outside — the elaborator's conveniences, the stdlib, the SMT lint — is *untrusted*
and can only ever *ask* the kernel, never bypass it.

```cure
# A soundness bug is only dangerous if it's in the kernel; that's why it stays tiny.
```

**Classic vs. dependent pipeline** — Cure has two compile paths: the older **classic**
one (a non-dependent checker + codegen, being retired) and the **dependent** one
(elaborator + kernel). New work targets the dependent pipeline.

```cure
# The same .cure source can elaborate dependently; classic is the fallback being removed.
```

**Antigen** — Cure's property-based *metatheory* test engine: it generates kernel
terms and checks soundness laws (a well-typed term stays well-typed after
substitution, etc.), hunting for holes in the type theory itself.

```cure
# `mix antigen` runs the explorer; it found and pinned real mutual-recursion holes.
```

**escript** — The build product of the compiler: `mix escript.build` produces the
`cure` command-line binary that compiles `.cure` sources.

```cure
# cure build hello.cure        # the escript compiling a program
```

**packbeam / AtomVM** — The path to hardware: Cure compiles to `.beam`, which is
packed (**packbeam**) into an `.avm` bundle that **AtomVM** runs — including on an
ESP32.

```cure
# hello.cure -> hello.beam -> (packbeam) -> hello.avm -> run on AtomVM / ESP32
```

**Parametricity** — A truly generic function *can't inspect* the type it's generic
over, so it behaves uniformly — yielding "free theorems" from the type alone. Cure's
tests use it to catch functions that cheat by peeking at run-time representations.

```cure
fn id({a: Type}, x: a) -> a = x     # can only return its input: nothing else typechecks
```

**Intensional vs. extensional** — Two attitudes to equality. *Intensional* equality is
by construction/computation (Cure is intensional); *extensional* would call two
functions equal merely for agreeing on every input. The gap is why some equalities
need explicit **propositional** proofs.

```cure
# plus(n, Z) and n agree on every n, but proving them equal needs plus_zero_right —
# that extra proof step is the mark of an intensional system.
```

**Subtyping** — "An `A` may be used wherever a `B` is expected." Cure keeps subtyping
minimal; the main place it appears is **cumulativity** (Layer 1) between universe
levels.

```cure
# There's no int-to-float widening or subclass slack: types must match (or convert).
```
