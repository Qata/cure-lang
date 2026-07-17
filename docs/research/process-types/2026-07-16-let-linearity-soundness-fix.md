# Soundness fix — a linear resource could be duplicated through a `let`

*2026-07-16. Found while pivoting to fix roadblock #2b (relevance's convoy
over-rejection). Probing the linear checker turned up the opposite kind of bug: a
genuine **unsound accept**. Fixed here; it directly strengthens obligation (1).*

## The hole

`Cure.Elab.Relevance` (the `{0,1,ω}` usage check that makes erasure sound) counted
a `let x = v in b` by `seq(uv, ub \ x)` — the value's usage once, and it DROPPED the
binder's own uses. So a linear resource **aliased** by the `let` and then used more
than once was laundered to a single use:

```cure
fn serve(r: Req, cap :linear ReplyCap(r)) -> Pair =
  let x = cap in MkPair(reply(x, handle(r)), reply(x, handle(r)))   -- was ACCEPTED
```

The linear reply capability `cap` is bound to `x` and consumed **twice**. This was
accepted, so obligation (1)'s "capability consumed exactly once" was not actually
enforced — the direct-duplication negative (`MkPair(reply(cap,…), reply(cap,…))`)
rejected, but the `let`-aliased form slipped through.

Verified against the Idris oracle (`~/Develop/Idris2`), which rejects it:

| program (c : linear) | Idris | Cure (before) | Cure (after) |
|----------------------|-------|---------------|--------------|
| `let x = c in (x, x)` (alias, ×2) | reject | **accept** 🐛 | reject |
| `let x = consume(c) in (x, x)` (×2) | reject | **accept** 🐛 | reject |
| `let x = c in use(x)` (×1) | accept | accept | accept |
| `let x = consume(c) in x` (×1) | accept | accept | accept |

Oracle cluster `test/oracle/let_linear/` pins all four (`rel=same`), and
`test/oracle/otp/ob1_neg_launder_cap` pins the capability version.

## The fix (relevance.ex, `:let` `:not_join`)

Keep Cure's single **call-by-value** evaluation — the value runs once, so `uv` is
counted once (this is why `let x = consume(c) in Done`, which consumes `c` once, and
`let x = consume(c) in consume2(c)`, which uses `c` twice, are both already handled
correctly by `seq`). Then ADD the aliasing duplication: if the body uses the binder
`x` ω-many times, the value's result — hence any linear/affine resource aliased into
it — is referenced ω times, so add `scale(uv, ω)`.

```elixir
dup = if Enum.any?(Map.get(ub, depth, no_uses()), &(&1 == Grade.unrestricted())),
        do: scale(uv, Grade.unrestricted()), else: %{}
{:ok, seq(seq(uv, dup), Map.delete(ub, depth))}
```

**Soundness:** the value's resources are still counted at least once (CBV
evaluation, via `uv`), and ω more when the binder is reused — the check never
under-counts a real use (verified on the `consume(c) … consume2(c)` counterexample,
which stays rejected). A value with no restricted resource is unaffected (ω
resources carry no obligation), so the common `let` is unchanged.

**One deliberate divergence from Idris (call-by-value vs call-by-name).**
`let x = consume(c) in Done` — `x` unused, `c` consumed once — is ACCEPTED by Cure
(sound: `c` is used exactly once at the BEAM's call-by-value runtime) but rejected
by Idris (which counts `let` by substitution, so an unused binder makes the value's
resources vanish). Cure's acceptance is CBV-sound; this case is therefore left out
of the `let_linear` oracle cluster rather than marked `same`.

## Verification

Antigen 563 pass / 318-318 coverage (soundness engine); full `test/cure/elab` 1043
pass; oracle replay 79; stdlib 49/0. New behavioral test
`test/cure/elab/let_linear_soundness_test.exs` (6 cases, red→green).
