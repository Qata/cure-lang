defmodule Cure.Diagnostic.Registry.Catalog do
  @moduledoc false

  @catalog %{
    "E001" => """
    E001: Type Mismatch

    A function's body type does not match its declared return type,
    or an argument type does not match the parameter type.

    Example:
      fn add(a: Int, b: Int) -> String = a + b
      # Error: declared return type String but body has type Int

    Fix: change the return type annotation or the function body.
    """,
    "E002" => """
    E002: Unbound Variable

    A variable is referenced that has not been defined in the current scope.

    Example:
      fn foo() -> Int = x + 1
      # Error: undefined variable 'x'

    Fix: define the variable with let, or check for typos.
    """,
    "E003" => """
    E003: Arity Mismatch

    A function is called with the wrong number of arguments.

    Example:
      fn add(a: Int, b: Int) -> Int = a + b
      fn main() -> Int = add(1)  # Error: expects 2 arguments, got 1

    Fix: provide the correct number of arguments.
    """,
    "E004" => """
    E004: Non-Exhaustive Match

    A match expression does not cover all possible values of the scrutinee type.

    Example:
      match x
        true -> "yes"
      # Warning: missing pattern for 'false'

    Fix: add the missing patterns or a wildcard (_ -> ...).
    """,
    "E005" => """
    E005: Constraint Violation

    A function with a guard constraint is called with arguments that
    may violate the constraint.

    Example:
      fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
      fn main() -> Int = safe_div(10, 0)  # Warning: b != 0 may be violated

    Fix: ensure the arguments satisfy the guard condition.
    """,
    "E006" => """
    E006: Effect Violation

    A function performs an effect that is not declared in its effect
    annotation. Either add the missing effect to the `!` annotation or
    remove the effectful operation.

    Example:
      fn pure_add(a: Int, b: Int) -> Int = println("adding"); a + b
      # Error: undeclared effect Io

    Fix: annotate as `fn pure_add(a: Int, b: Int) -> Int ! Io` or
    remove the println call.
    """,
    "E007" => """
    E007: Unused Variable

    A variable is defined but never referenced. Prefix unused variables
    with `_` to suppress this warning.

    Example:
      fn foo() -> Int =
        let x = 42
        0
      # Warning: unused variable 'x'

    Fix: use the variable or rename it to `_x`.
    """,
    "E008" => """
    E008: Undocumented Public Function

    A public function has no `##` doc comment. This warning is only
    emitted when `cure doc --strict` is used.

    Fix: add a `##` doc comment above the function definition.
    """,
    "E009" => """
    E009: Unreachable Clause

    A pattern matching clause is shadowed by a prior clause and can
    never be reached.

    Example:
      fn classify(x: Int) -> String
        | _ -> "other"
        | 0 -> "zero"   # Unreachable: wildcard above catches everything

    Fix: reorder the clauses so more specific patterns come first.
    """,
    "E010" => """
    E010: Missing Effect Annotation

    A public function performs side effects but has no `!` annotation.
    This warning is only emitted when `--strict-effects` is enabled.

    Fix: add an effect annotation, e.g. `fn greet() -> Atom ! Io`.
    """,
    "E011" => """
    E011: Missing Implicit Argument

    Implicit unification could not solve every implicit parameter at a
    call site. The unification trace shows which constraint failed.

    Fix: pass the implicit explicitly with `{T = ConcreteType}`, or
    constrain the explicit arguments so the implicit can be inferred.
    """,
    "E012" => """
    E012: Sigma Destructuring Failure

    A pattern attempted to destructure a sigma value into shapes that
    don't agree with its declared first or second component.

    Fix: ensure the pattern matches the sigma's structure, or relax
    the type to a plain tuple where dependency is not required.
    """,
    "E013" => """
    E013: Totality Failure

    A function annotated `@total true` is not provably total. Either
    coverage is incomplete or a recursive call doesn't shrink any
    structural argument.

    Fix: add the missing patterns, restructure the recursion to use
    a smaller sub-term, or remove `@total true` if partiality is OK.
    """,
    "E014" => """
    E014: Unfilled Hole

    The compiler reached a `?name` or `??` placeholder. This is
    informational by default; when running `cure check --strict`
    every hole becomes an error.

    Fix: replace the hole with a real expression of the reported
    goal type.
    """,
    "E015" => """
    E015: Refinement Counterexample (retired)

    Reserved. This code covered refinement-type counterexamples, a
    feature removed pending SMTCoq-style proof reconstruction; it no
    longer fires.

    Fix: no action required -- refinement types are not currently part
    of the language.
    """,
    "E016" => """
    E016: Dependent Type Mismatch

    A function's dependent return type, after substituting the
    call-site arguments and normalising, does not match the expected
    type at the use site.

    Fix: check that the actual arguments produce the expected
    relationship (e.g. `m + n` versus the literal length).
    """,
    "E017" => """
    E017: Equality Proof Mismatch

    `refl(x)` was used to inhabit `Eq(T, a, b)` where `a` and `b` are
    not definitionally equal to `x`.

    Fix: if the equality is true but not definitional, prove it using
    `Std.Equivalent.trans/2`, `Std.Equivalent.cong/2`, or a `rewrite` step.
    """,
    "E018" => """
    E018: Path-sensitive Refinement Conflict (retired)

    Reserved. This code covered path-sensitive refinement conflicts, a
    feature removed pending SMTCoq-style proof reconstruction; it no
    longer fires.

    Fix: no action required -- refinement types are not currently part
    of the language.
    """,
    "E019" => """
    E019: Implicit Argument Solved Inconsistently

    The same implicit argument was solved to two different types from
    different parts of the call site.

    Fix: pass the implicit explicitly, or ensure the call-site
    arguments agree on the inferred type.
    """,
    "E020" => """
    E020: Doctest Mismatch

    A `cure>` doctest produced a different value from its `=>`
    expected line.

    Fix: update either the doctest expectation or the function it
    documents.
    """,
    "E021" => """
    E021: Unknown Record Field in Pattern

    A record pattern references a field that is not declared in the
    record's schema.

    Example:
      rec Point
        x: Int
        y: Int

      fn f(p: Point) -> Int =
        match p
          Point{z: v} -> v   # Error: Point has no field 'z'

    Fix: use one of the declared fields, or remove the clause.
    """,
    "E022" => """
    E022: Record Pattern Field Type Mismatch

    A sub-pattern inside a record pattern is incompatible with the
    declared type of that field.

    Example:
      rec Person
        age: Int

      match p
        Person{age: "forty"} -> ...   # Error: age is Int, not String

    Fix: change the sub-pattern or the field type so they agree.
    """,
    "E023" => """
    E023: Non-Literal Map Pattern Key

    Map keys in pattern position must be literal values (atoms,
    integers, strings, etc.). Bound variables may be used as keys
    only when they are already in scope; in that case they are
    looked up, not bound.

    Example:
      match m
        %{key(): v} -> v   # Error: function calls not allowed as keys

    Fix: use a literal key, or pre-compute the key with `let`.
    """,
    "E024" => """
    E024: Unbound Pin Variable

    The pin operator `^x` was used on a name that is not in scope at
    the pattern's position. The pin operator only compares against
    previously bound values.

    Example:
      match tag
        ^status -> :hit   # Error: 'status' is not bound

    Fix: bind the variable with `let` before the match, or drop the
    `^` if you intended to introduce a fresh binding.
    """,
    "E025" => """
    E025: Non-Exhaustive Nested Match

    A `match` expression with nested patterns does not cover every
    inhabitant of the scrutinee type. The compiler prints a concrete
    witness for the missing case.

    Example:
      match %[r]
        %[Ok(_)] -> :ok
      # Warning: missing pattern `%[Error(_)]`

    Fix: add the missing clause or a wildcard.
    """,
    "E026" => """
    E026: Proof Shape Mismatch

    A binding inside a `proof` container does not elaborate to an
    `Eq(T, a, b)` proof. Proof containers are intended exclusively for
    propositional laws.

    Example:
      proof Arithmetic
        fn meaning() -> Int = 42   # Error: not a proof shape

    Fix: move ordinary code into a `mod` container; keep `proof`
    containers for functions returning `Eq(...)`.
    """,
    "E027" => """
    E027: assert_type Assertion Failed

    The `assert_type expr : T` builtin was used but the type
    inferred for `expr` is not compatible with `T`.

    Example:
      fn f() -> Int = assert_type 42 : String
      # Error: assert_type expected String, got Int

    Fix: either change the asserted type or the expression. The
    wrapper disappears at runtime, so nothing breaks at runtime when
    it succeeds.
    """,
    "E028" => """
    E028: Record Default Type Mismatch

    A record field declared with a default value has a default whose
    inferred type does not match the declared field type.

    Example:
      rec Person
        name: String = 0       # Error: name is String, default is Int

    Fix: change the default or the declared field type.
    """,
    "E029" => """
    E029: Mutual Recursion Not Structural

    Two or more functions annotated with `@total true` call each other
    in a cycle in which no argument shrinks structurally on every
    path through the cycle. The compiler cannot prove termination.

    Example:
      @total true
      fn a(x: Nat) -> Nat = b(x)

      @total true
      fn b(x: Nat) -> Nat = a(x)
      # Error: neither clause decreases

    Fix: restructure the cycle so some structural argument shrinks
    on every path, or drop `@total true` if partiality is acceptable.
    """,
    "E030" => """
    E030: Package Version Conflict

    The dependency resolver could not find a set of versions that
    satisfies every constraint in `Cure.toml` and the transitive
    dependency graph.

    Example:
      # Cure.toml declares http ~> 1.0
      # but dep Foo requires http ~> 2.0
      # Error: no version of http satisfies both ~> 1.0 and ~> 2.0

    Fix: relax one of the constraints, or pin to a compatible
    version.
    """,
    "E031" => """
    E031: Binary Pattern Not Exhaustive

    A sequence of binary patterns (in a `match`, function head, `let`,
    or comprehension generator) does not cover every byte-length
    inhabitant of the scrutinee's Bitstring type.

    Example:
      fn first_byte(buf: Bitstring) -> Int =
        match buf
          <<b, _rest::binary>> -> b
      # Warning: missing pattern `<<>>`

    Fix: add the missing shape (typically `<<>>` or a size-0 case) or
    provide a catch-all arm.
    """,
    "E032" => """
    E032: Match Clause Unreachable (W-MATCH-UNREACHABLE)

    A `match` arm is provably shadowed by an earlier arm, so its
    pattern can never match (its guard, if any, is therefore never
    evaluated). The compiler emits this as a warning under MATCH §6.4
    so unreachable clauses surface during compilation rather than at
    review time.

    Example:
      match x
        _ -> :a       # wildcard absorbs everything
        0 -> :b       # warning E032: unreachable

    Fix: reorder the arms so more specific patterns come first, drop
    the redundant arm, or tighten the earlier pattern (or its guard)
    so the later arm is reachable. Numeric code reserved by
    `docs/MATCH.md` §20 -- the descriptive alias is `W-MATCH-UNREACHABLE`.
    """,
    "E033" => """
    E033: Match Branches Have No Common Type (E-MATCH-BRANCH-MISMATCH)

    The right-hand sides of two or more `match` arms produce values
    whose types do not admit a least upper bound under the
    language's existing subtyping rules. The result type of the
    whole `match` is therefore undefined.

    Example:
      match x
        "yes" -> 1     # Int
        42    -> "two" # String
      # error E033: branches have no common upper bound

    Fix: change the bodies so all arms produce the same type, or
    explicitly widen via `assert_type` or a sum-type wrapper. Numeric
    code reserved by `docs/MATCH.md` §20 -- the descriptive alias is
    `E-MATCH-BRANCH-MISMATCH`.
    """,
    "E071" => """
    E071: Function Type Payload Invalid

    An ADT constructor payload carries a value whose type cannot be
    resolved. The most common trigger is a bare identifier that does
    not refer to a declared type. Function-type payloads
    (e.g. `On(Int -> Int)` and `On((Int, Int) -> Int)`) are allowed
    and compile to first-class functions at runtime.

    Example:
      type Callback = On(DoesNotExist) | Off   # Error: unknown type

    Fix: use a concrete type, a declared type alias, or a function
    arrow for callable payloads.

    History: this diagnostic was previously code `E032`. The number
    was reassigned to `W-MATCH-UNREACHABLE` per `docs/MATCH.md` §20.
    """,
    "E072" => """
    E072: Multi-line Type Layout Invalid

    A `type` ADT declaration spans multiple lines but the layout
    cannot be absorbed by `parse_type_def/1`. This usually means the
    continuation lines are not indented beyond the `type` keyword or
    a leading `|` is followed by a closing `:dedent` instead of a
    variant name.

    Example:
      type Shape =
      | Circle(Int)   # error: continuation lines must be indented

    Fix: indent every continuation line at the same column inside
    the parent block, for example:
      type Shape =
        | Circle(Int)
        | Square(Int)

    History: this diagnostic was previously code `E033`. The number
    was reassigned to `E-MATCH-BRANCH-MISMATCH` per `docs/MATCH.md`
    §20.
    """,
    "E073" => """
    E073: Empty Match Block (E-MATCH-EMPTY)

    A `match` expression has no clauses. Empty `match` blocks are
    rejected at the macro-invocation site per `docs/MATCH.md` §17,
    so a macro that constructs a `match` AST without any clauses is
    flagged here rather than at runtime.

    Fix: ensure every macro-generated `match` has at least one clause,
    or guard the macro so the empty case never reaches expansion.
    """,
    "E074" => """
    E074: Bare Nullary Constructor in Pattern (E-MATCH-NULLARY-NEEDS-PARENS)

    A pattern position carries a bare PascalCase identifier such as
    `None`. `docs/MATCH.md` §5.12 requires nullary constructors to be
    written with explicit empty parentheses so the parser can tell
    them apart from a regular variable binding (which is lowercase).

    Example:
      match opt
        Some(x) -> x
        None    -> default     # error: write `None()`

    Fix: rewrite the pattern as `None()`. The compiler ships a code
    action that performs the rewrite automatically.
    """,
    "E075" => """
    E075: Constructor Arity Mismatch in Pattern (E-MATCH-CONSTRUCTOR-ARITY)

    A constructor pattern is applied to a different number of
    arguments than the constructor was declared with. `docs/MATCH.md`
    §5.12 requires the pattern arity to match the declaration.

    Example:
      type Pair = P(Int, Int)

      match p
        P(x) -> x         # error: P/2 received 1 argument

    Fix: change the pattern to match the declared arity, or change
    the type so the constructor accepts the new shape.
    """,
    "E076" => """
    E076: pickup Without else (E-PICKUP-NO-ELSE)

    A `pickup` block does not end in a mandatory terminating clause.
    `docs/PICKUP.md` §5.2 requires every `pickup` to end in either
    `else -> ...` (canonical) or a trailing `true -> ...` (alternative
    form normalised by the formatter).

    Example:
      pickup
        x > 0 -> :positive
        x < 0 -> :negative
      # error E076: missing terminator

    Fix: add a final `else -> ...` arm. The language server provides
    an "Add missing else" code action.
    """,
    "E077" => """
    E077: pickup else Not Last (E-PICKUP-ELSE-NOT-LAST)

    A `pickup` block has a clause after the `else ->` terminator.
    `docs/PICKUP.md` §4.1 forbids any clause after the terminator,
    because subsequent clauses would be unreachable by construction.

    Fix: move the `else ->` arm to the end of the block, or delete
    the trailing clauses.
    """,
    "E078" => """
    E078: pickup Has Multiple else (E-PICKUP-MULTIPLE-ELSE)

    A `pickup` block contains more than one `else ->` arm. Per
    `docs/PICKUP.md` §4.1 the terminator is unique.

    Fix: keep one terminator and inline or relocate the other arms.
    """,
    "E079" => """
    E079: pickup Guard Not Bool (E-PICKUP-GUARD-TYPE)

    A `pickup` guard expression has a type other than `Bool`. `pickup`
    is strict about guard typing per `docs/PICKUP.md` §5.1; there is
    no truthy/falsy coercion.

    Example:
      pickup
        "yes" -> :positive    # error: guard is String
        else  -> :other

    Fix: rewrite the guard as a Boolean expression, e.g.
    `name == "yes"` or `is_positive?(n)`.
    """,
    "E080" => """
    E080: pickup Branch Type Mismatch (E-PICKUP-BRANCH-MISMATCH)

    The right-hand sides of two or more `pickup` clauses produce
    values whose types do not admit a least upper bound. `pickup`'s
    branch-join rule is identical to `match`'s; see `docs/PICKUP.md`
    §5.6.

    Fix: align the branch types, wrap one branch in a sum type, or
    use `assert_type` to widen explicitly.
    """,
    "W081" => """
    W081: pickup Guard Unreachable (W-PICKUP-UNREACHABLE)

    A `pickup` guard is provably shadowed by a constant-true earlier
    guard, so it (and any subsequent guards) can never be evaluated.
    `docs/PICKUP.md` §5.3 mandates a sound, possibly incomplete
    reachability check; the implementation reports the obvious
    constant-`true` short-circuit case here.

    Fix: reorder the clauses, drop the dead arm, or replace the
    constant-true guard with a real condition.
    """,
    "W082" => """
    W082: pickup Terminator Unreachable (W-PICKUP-DEAD-ELSE)

    A `pickup` terminator can be shown unreachable because some
    earlier guard is statically `true`. The terminator is preserved
    syntactically so the totality property of `pickup` still holds,
    but the dead branch is reported as a warning per
    `docs/PICKUP.md` §5.3.

    Fix: drop the unreachable terminator or, if it is the intended
    branch, demote the redundant constant-true guard above it.
    """,
    "H083" => """
    H083: pickup `true ->` Normalised to `else ->` (H-PICKUP-PREFER-ELSE)

    The formatter rewrote a trailing `true -> ...` arm into the
    canonical `else -> ...` form. Both forms compile identically, but
    `else ->` reads as the default arm and is the surface form
    `docs/PICKUP.md` §8.3 prescribes.
    """,
    "H084" => """
    H084: Degenerate `pickup` Reduced (H-PICKUP-DEGENERATE)

    A `pickup` block whose only clause is the terminator was reduced
    to its right-hand side by the formatter. Per `docs/PICKUP.md`
    §8.6 the wrapping `pickup` carries no behaviour beyond evaluating
    its single body, so removing it produces equivalent code.
    """,
    "E085" => """
    E085: `if` Removed -- Use `pickup` (E-IF-REMOVED)

    `docs/PICKUP.md` §17 retires the `if`/`elif`/`then` keywords in
    favour of `pickup`. The current release keeps the parser
    permissive so legacy sources still compile, but `cure check`
    surfaces this hint so authors can migrate. The `mix cure.rewrite`
    task produces the canonical replacement automatically.

    Fix: replace the `if` chain with a `pickup` block, or run
    `mix cure.rewrite if-to-pickup <path>` to convert the file in
    place.
    """,
    "E034" => """
    E034: Let Pattern Not Exhaustive

    A `let` binding destructures its RHS with a pattern that does
    not cover every inhabitant of the RHS type. The binding still
    compiles -- Erlang's `=` raises at runtime on a failed match --
    but the compiler surfaces the gap as a warning so you can decide
    whether to widen the pattern or mark the let partial.

    Example:
      fn first_ok(r: Result(Int, String)) -> Int =
        let Ok(x) = r       # warning: missing `Error(_)`
        x

    Fix: rewrite as a `match` with every branch covered, add a
    wildcard by widening to `let _ = r`, or annotate the let's
    AST metadata with `partial: true` (reserved for tooling that
    knows the pattern is acceptable by construction).
    """,
    "E035" => """
    E035: Lambda Block Unterminated

    A multi-statement lambda body (v0.22.0) opened a brace block or
    began an `end`-terminated block but never closed it. The parser
    reached the end of the enclosing expression without seeing `}`
    or `end`.

    Example:
      map(xs, fn (x) -> { x + 1; x * 2 ) # Error: missing '}'
      map(xs, fn (x) -> x + 1; x * 2)    # Error: missing 'end'

    Fix: close the block with a matching `}` for brace-delimited
    bodies or with `end` for end-terminated ones. If the body is a
    single expression, use the v0.19.0 single-expression or indented
    form without `{` and without `;`.
    """,
    "E036" => """
    E036: Binary Comprehension Source Not Bitstring

    A binary comprehension generator `for <<pattern <- source>>`
    requires `source` to be a `Bitstring` (or a subtype of it).
    An Int, List, or other shape cannot drive byte-level iteration.

    Example:
      [b for <<b <- 123>>]   # Error: 123 is Int, not Bitstring

    Fix: pass a `Bitstring` value, for example a string literal
    (`"abc"`) or a `<<...>>` construction.
    """,
    "E038" => """
    E038: Registry Fetch Failed

    A call to the Cure package registry returned a non-2xx status or
    hit a transport error. The failure is surfaced through
    `Cure.Pipeline.Events` on the `:registry` stage; rerun with
    `--verbose` for the HTTP status or transport reason.

    Fix: verify the registry URL (env `CURE_REGISTRY_URL`), check
    network connectivity, or retry after the upstream incident is
    resolved.
    """,
    "E039" => """
    E039: Registry Hash Mismatch

    A tarball downloaded from the registry does not match the sha256
    the index declared for that version. This is treated as an
    unconditional error: the bytes are discarded and the install
    aborts.

    Fix: run `cure deps update` to force a re-resolution against the
    current index. If the mismatch persists, the registry entry is
    corrupt and should be reported upstream.
    """,
    "E040" => """
    E040: Registry Package Not Found

    The registry index has no entry for the requested package name.

    Fix: check the spelling in `Cure.toml`, confirm the package is
    published, or search the index with `cure search <query>`.
    """,
    "E041" => """
    E041: Registry Signature Invalid

    A tarball's Ed25519 signature failed verification against the
    trusted public key for its publisher. The install is aborted.

    Fix: either trust the publisher's key explicitly
    (`cure keys generate / cure keys list`) or reject the package
    until the publisher rotates a compromised key.
    """,
    "E042" => """
    E042: Transparency Log Unreachable

    The registry's transparency log did not respond to the pre-install
    verification request. By default the install continues with an
    :unverified annotation; set `config :cure,
    strict_transparency: true` to make this a hard failure.

    Fix: check connectivity to the registry's `/log` endpoint, or
    accept the unverified install if you trust the transport.
    """,
    "E037" => """
    E037: Binary Segment Size Non-Linear

    The compiler tried to compute the exact byte length of a trailing
    `rest::binary` segment as `byte_size(scrutinee) -
    sum_of_preceding_sizes`, but one of the preceding segments carries
    a size expression that cannot be linearised (for example an
    arbitrary runtime expression, or a non-byte-aligned specifier).
    The segment is typed as plain `Bitstring` and the pipeline emits
    this warning so you can choose whether to tighten the pattern or
    accept the looser type.

    Example:
      fn f(buf: Bitstring, n: Int) -> Int =
        match buf
          <<head::size(n)-unit(3), rest::binary>> -> ...
                    # warning: non-byte-aligned head size (E037)

      Fix: use byte-aligned sizes (multiples of 8 bits) or explicit
      literal sizes so the arithmetic can be emitted; otherwise accept
      that `rest` binds to plain `Bitstring` and let runtime pattern
      matching enforce the remaining invariants.
    """,
    "E056" => """
    E056: @extern Declaration Missing a Typed Head

    A function annotated with `@extern(:mod, :fun, arity)` is a type-only
    foreign-function signature: the compiler does not see its implementation,
    so it must trust the declared types and lower the call to a direct Erlang
    remote call. That trust only holds if the head is fully typed -- every
    parameter annotated and a return type declared. An untyped head would
    silently default to `Any`, defeating the type checker at every call site.

    Rejected:
      @extern(:erlang, :abs, 1)
      fn abs(x)                  # parameter `x` has no type, no return type

    Fix: annotate the whole head.
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int

    A zero-parameter extern still needs its return type:
      @extern(:math, :pi, 0)
      fn pi() -> Float
    """,
    "E057" => """
    E057: @extern Declaration Has a Body

    A function annotated with `@extern` is a signature only. Codegen lowers it
    to a direct remote call to the external function, so any body you write is
    dead code -- it is never compiled or run. To stop that silent discard from
    misleading readers, a body on an `@extern` function is an error. This covers
    both a `= ...` body and a multi-clause `|` definition.

    Rejected:
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int = x  # the `= x` body is ignored by codegen

    Also rejected (the clauses are ignored just the same):
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int
        | 0 -> 0
        | n -> n

    Fix: drop the body; keep only the typed head.
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int

    If you actually need local logic, write a normal function and call the
    extern from inside it:
      @extern(:erlang, :abs, 1)
      fn raw_abs(x: Int) -> Int

      fn abs_or_zero(x: Int) -> Int =
        pickup
          x < -1000 -> 0
          else      -> raw_abs(x)
    """,
    "E063" => """
    E063: Parse Error (recovered)

    A statement contained a syntax error from which the parser
    recovered by skipping tokens until the next statement boundary
    (newline, dedent, or definition-opening keyword such as `fn`,
    `mod`, `rec`, etc.). Subsequent definitions in the same file are
    still reported.

    A file that contains this error will also contain one or more
    primary parse errors (e.g. `:unexpected_token`) that identify
    the root cause. Fix those first; E063 errors will disappear once
    the primary error is resolved.

    Example:
      mod M
        fn foo() -> ???bad     # primary parse error here
        fn bar() -> Int = 0    # still parsed; E063 recovery consumed
                               # the tokens between the two fns

    Fix: address the root syntax error. E063 diagnostics are
    informational and do not indicate a new, independent bug.
    """,
    "E064" => """
    E064: Monomorphisation Budget Exhausted

    The optimiser's monomorphisation pass synthesises one specialised
    clone of a polymorphic function per unique call-site type
    substitution. To keep BEAM bytecode size bounded, the pass caps
    the number of specialisations at `[compiler].monomorph_budget`
    (default 16) per source function.

    When a function has more than the configured number of distinct
    concrete call shapes in a single compilation unit, the pass keeps
    the first N specialisations, falls back to the original generic
    clone for the rest, and emits this warning. Calls that fell back
    are still correct -- they just dispatch through the generic
    function instead of a tighter clone.

    Example:
      fn id(x: T) -> T = x
      # 17 distinct concrete types call id/1 -> the 17th and beyond
      # use the generic implementation; the warning lists the count.

    Fix: either accept the generic fallback (it is fully correct), or
    raise the budget in `Cure.toml`:

      [compiler]
      monomorph_budget = 32
    """,
    "E065" => """
    E065: Proof File Missing

    `cure verify` found no `.cureproof` artifact in the package
    tarball or extracted directory, and `strict_proofs: true` is set
    in `config.exs`.

    The `.cureproof` file is generated during `cure publish` when
    `[publish] include_proofs = true` is set in the project's
    `Cure.toml` (the default). A missing artifact means the publisher
    either disabled proof inclusion explicitly or published with an
    older version of Cure that predates v0.32.0.

    Fix: if you control the upstream package, re-publish with proof
    collection enabled. Otherwise, remove `strict_proofs: true` from
    your `config.exs` to allow packages without proof artifacts.
    """,
    "E066" => """
    E066: Proof Verification Failed

    `cure verify` successfully loaded a `.cureproof` artifact but one
    or more certificates could not be replayed. The diagnostic
    includes the module name and the failing proposition.

    This may indicate:
      - The package tarball was modified after signing (integrity
        violation). Cross-check the tarball hash against the
        transparency log (`cure info <pkg>:<ver>`).
      - The proof depends on a Z3 lemma whose off-line replay requires
        a solver version newer than the one installed locally.
      - The proof was produced in a development build with weakened
        checker settings.

    Fix: if you suspect tampering, discard the package and fetch a
    fresh copy. Otherwise, check the solver version with
    `cure doctor` and update it if necessary.
    """,
    "E067" => """
    E067: Proof Schema Incompatible

    The `.cureproof` file's embedded version byte does not match the
    schema the running Cure release understands. This happens when a
    proof artifact generated by a future release of Cure is verified
    by an older toolchain, or vice versa.

    Fix: update Cure to at least the version that generated the proof
    artifact, or ask the publisher to re-publish with the current
    Cure release.
    """,
    "E068" => """
    E068: Export Type Unmappable

    `cure export-types` encountered a Cure type that has no direct
    equivalent in the target language. The offending field is replaced
    by a comment in the generated output so the remaining types are
    still exported.

    Types that commonly trigger E068:
      - Dependent types (`Nat`, `Vec n T`) have no standard proto3
        representation.
      - Higher-kinded types and type-level functions.
      - `proof` container types (they are erased at runtime).

    Fix: annotate the field in the source with a `@export_as`
    attribute to give `cure export-types` a concrete target type, or
    wrap the value in an outer `rec` and export only the record.
    """,
    "E069" => """
    E069: Snap Schema Incompatible

    The `.cure-snap` file was produced by a different version of the
    Cure REPL serializer. The `snap_vsn` field inside the file does
    not match the version this Cure release understands.

    Fix: discard the old snap file and create a new one with the
    current Cure version via `:snap save <path>`.
    """,
    "E070" => """
    E070: Snap Module Missing

    A `.cure-snap` file recorded one or more files that were loaded
    via `:load` during the original session, but one or more of those
    files no longer exist at the saved path. The rest of the session
    has been restored normally; only the bindings from the missing
    file are absent.

    Fix: locate the missing `.cure` file and run `:load <path>` to
    restore its bindings manually, or delete the entry from the snap
    file's `loaded_paths` list.
    """,
    "W086" => """
    W086: Import Cycle

    Two or more modules in one compile set reference each other through
    `use` declarations, forming a cycle. This is NOT an error: the cycle's
    members compile together as a single group in deterministic
    (alphabetical) order -- Cure's compile-set model matches Rust's
    crate-internal modules, where module cycles are legal -- and the cycle
    is reported as a closed walk (`A (a.cure:3) -> B (b.cure:2) -> A`).

    A cycle is harmless when the modules only depend on each other's
    types or qualified calls, which lower syntactically and impose no
    order. It becomes actionable when the modules CALL each other's
    imported functions UNQUALIFIED: resolution inside the group is
    order-dependent, so an unqualified call may fall back to a local
    reference and surface as W088.

    Fix: qualify the cross-module calls (`Other.fn(...)`), merge the
    mutually-recursive modules into one, or drop a redundant `use`.
    """,
    "E087" => """
    E087: Duplicate Module

    Two or more files in the same compile set declare a module with the
    same name. The build driver scans every `.cure` source before
    ordering and aborts here, because a duplicate name makes the
    dependency graph -- and the emitted beam -- ambiguous.

    Example:
      one.cure:  mod Dup
      two.cure:  mod Dup      # Error: 'Dup' declared twice

    Fix: rename one of the modules, or remove the redundant file if it
    was an accidental copy.
    """,
    "E089" => """
    E089: Ambiguous Name

    An unqualified reference names a global that two or more imported
    modules provide, and the local module does not redeclare it to claim
    the name. Approach B re-keys every colliding import to its qualified
    key (`Mod#name`), so the bare name has no single owner -- resolving it
    silently would pick whichever import merged last. This fires at BOTH
    reference sites: a call (`name(...)`) and a bare value (`f(name)`).

    Example:
      mod P
        use Std.CollA        # exports helper/1
        use Std.CollB        # also exports helper/1
        fn f() -> Nat = helper(Z())   # Error: 'helper' is ambiguous
      end

    Fix: qualify the reference (`Std.CollA.helper(...)`), or define a
    local `helper` to shadow both imports.
    """,
    "E090" => """
    E090: Unrecognized Pattern Shape (E-MATCH-UNRECOGNIZED-PATTERN)

    A pattern's head is not one the pattern compiler recognizes. Match
    arms are parsed with the general expression parser, so shapes that
    are legal expressions but not legal patterns reach pattern position
    and must be rejected here.

    Pattern compilation specializes over a closed set of head shapes; a
    shape outside that set used to compile to a wildcard, which matches
    every value and shadows every arm below it.

    Examples:
      match x
        1..10 -> 1        # error: range patterns are not supported
        some(v) -> v      # error: lowercase head is not a constructor
        -f(x) -> 0        # error: unary `-` is not a pattern

    Fix: use a `when` guard for a range test (`n when n >= 1 and n <= 10`),
    capitalize a constructor name, or bind a variable and test in the body.
    """,
    "E091" => """
    E091: Unknown Name

    A value, type, constructor, module, or module member is not available in
    the namespace where it was referenced. The diagnostic payload records the
    namespace, original spelling, visible candidates, owner when applicable,
    and the declaration currently being checked.

    Fix: correct the spelling, import or qualify the definition, or use a name
    from the required namespace. Suggestions are filtered by namespace and
    visibility before they are shown.
    """,
    "E092" => """
    E092: Macro Expansion Failed

    A public macro generated a declaration that the compiler rejected. The
    default diagnostic names the macro and its authored declaration rather
    than exposing generated implementation source. Its structured cause and
    complete expansion provenance remain available to compiler tooling.

    Fix the authored macro declaration or captured argument identified by the
    diagnostic. If generated syntax alone is invalid, report the macro or
    compiler defect; users must never be asked to edit generated code.
    """,
    "E093" => """
    E093: Type Mismatch

    An expression's inferred type is not definitionally equal to the type
    required at that position. Dependent indices and normalized type forms are
    retained in the structured payload, while the ordinary message uses Cure
    surface spelling instead of raw Core tuples.

    Fix the expression, its annotation, or the relevant dependent index so the
    actual type agrees with the expected type.
    """,
    "E094" => """
    E094: Syntax Error

    The parser encountered a token or construct that cannot appear at this
    point. The diagnostic records the expected and actual syntax categories and
    labels the offending authored source.

    Fix the indicated delimiter, keyword, expression, or declaration shape.
    """,
    "E095" => """
    E095: Could Not Read File

    Cure could not read a required source, manifest, journal, or artifact.
    The payload retains the path and host file-system reason.
    """,
    "E096" => """
    E096: Could Not Write File

    Cure could not write a generated source, artifact, journal, or report.
    The payload retains the path and host file-system reason.
    """,
    "E097" => """
    E097: Dependency Resolution Failed

    The project dependency graph could not be resolved consistently.
    """,
    "E098" => """
    E098: Command Failed

    An external or project operation returned a deliberate failure.
    """,
    "E099" => """
    E099: Invalid Command Usage

    A Cure command was invoked with missing or incompatible arguments.
    """,
    "E100" => """
    E100: Invalid Build Artifact

    A required build, proof, snapshot, or release artifact is absent,
    corrupt, incompatible, or has the wrong format.
    """,
    "E101" => """
    E101: Internal Compiler Error

    Cure caught an exception or received an impossible return shape inside the
    compiler. The diagnostic includes a stable fingerprint; stacktraces are
    retained only in debug payloads.

    Ordinary source errors must never use E101. Please report the fingerprint
    with a minimal reproducer.
    """,
    "E102" => """
    E102: Erasure Violation

    An opaque type declares an invalid runtime erasure, or an erasure
    declaration is applied to a type whose runtime shape is determined by
    constructors.

    Fix: use one of the supported erasure classes on a constructor-less
    opaque type, or remove the declaration from a constructed type.
    """,
    "E103" => """
    E103: Non-Strictly-Positive Type

    An inductive type refers to itself in a negative or otherwise
    non-strictly-positive position. Such a definition would make the
    normalising kernel unsound.

    Fix: move the recursive occurrence to a strictly positive constructor
    argument or introduce an appropriate external boundary.
    """,
    "E104" => """
    E104: Erased Value Used Relevantly

    A value marked erased is used in a runtime-relevant position. Erased
    values are unavailable after compilation and cannot influence returned
    values, present arguments, or other runtime computation.

    Fix: remove the runtime use or make the binding relevant.
    """,
    "E105" => """
    E105: Declaration Conflict

    A declaration conflicts with another declaration, constructor, field,
    parameter, or reserved name in the same visible namespace.

    Fix: rename the declaration or change its signature so each visible
    declaration has a unique identity.
    """,
    "W000" => """
    W000: Compiler Warning

    Compatibility code for a compiler warning awaiting a more specific public
    category. New producers must allocate a specific warning code.
    """,
    "W001" => """
    W001: Migration Warning

    Authored syntax is accepted for compatibility but has a modern form.
    """,
    "W002" => """
    W002: Invalid Configuration

    A configuration value was ignored because it is not valid in its setting.
    """,
    "W088" => """
    W088: Unresolved Import

    An unqualified call matched no export of any `use`-imported module,
    so codegen emitted a plain local call instead. This is the silent
    fallback that classic codegen took without saying so; W088 makes it
    visible.

    It most often fires inside an import cycle (W086), where the callee
    module has not been loaded yet when the caller is compiled, so its
    exports are invisible to the beam-probing resolver.

    Example:
      mod UserB
        use LibA
        fn start() -> Int = ping()   # warning: ping/0 not found in LibA

    Fix: make sure the imported module is compiled and loaded before
    this file (DepGraph ordering normally guarantees this outside a
    cycle), or qualify the call (`LibA.ping()`).
    """
  }

  @spec entries() :: [{String.t(), String.t(), String.t()}]
  def entries do
    @catalog
    |> Enum.map(fn {code, text} ->
      lines = text |> String.trim() |> String.split("\n") |> Enum.map(&String.trim/1)

      title =
        case lines do
          [first | _] ->
            case String.split(first, ":", parts: 2) do
              [_, name] -> String.trim(name)
              _ -> first
            end

          _ ->
            code
        end

      brief = Enum.drop(lines, 1) |> Enum.find("", &(&1 != ""))
      {code, title, brief}
    end)
    |> Enum.sort_by(fn {code, _, _} -> code end)
  end

  @spec explanation!(String.t()) :: String.t()
  def explanation!(code) do
    case Map.fetch(@catalog, String.upcase(code)) do
      {:ok, text} -> String.trim(text)
      :error -> raise ArgumentError, "unregistered diagnostic code: #{inspect(code)}"
    end
  end
end
