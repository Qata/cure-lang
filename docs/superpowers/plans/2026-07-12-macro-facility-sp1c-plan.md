# SP1 T8 — Macro-Expansion Soundness Firewall — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Builds on milestone 2 (local macro use-site expansion, commits d66bf57/0bd320f/94c33a6/6e01715).

**Goal:** Lock the central safety claim of the whole macro facility — **a macro's expansion is type-checked exactly like hand-written code, with no bypass** — as a permanent regression firewall. Concretely: for a battery of macro programs, `Program.elaborate/1` returns the *identical* verdict (accept, or reject with the identical error term) as the hand-written program the macro expands to.

**Architecture:** Macro expansion happens at **parse time** (`Parser.parse` substitutes the template in place), so a macro use-site produces ordinary surface AST that flows through the *unchanged* elaborator+kernel — `Cure.Elab.Program.elaborate/1` (`lib/cure/elab/program.ex:16`) neither knows nor cares that a macro was involved. This task adds **no production code**: it is a soundness firewall test that proves — and forever guards — that this is true. If any future change let macro output reach codegen without full elaboration, this test breaks.

**Tech Stack:** Elixir; ExUnit; `Cure.Elab.Program.elaborate/1`.

## Global Constraints

- **TCB delta ZERO** — no `lib/cure/core/*`, no `lib/cure/elab/*`, no `lib/cure/compiler/*` changes. This task is a **test only**. If executing it seems to require a production change, STOP and record why — it means expansion is *not* in fact re-elaborated, which is a HALT-level finding, not a code tweak.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Run `mix test test/cure/elab/macro_expansion_soundness_test.exs` scoped; full `mix test` only at the milestone gate.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone `/Users/ch/Develop/esp32-beam/cure-lang` (which lacks the macro code and yields phantom failures).
- **Tests immutable once green.**

## TDD framing (read before executing — this is an honest exception)

This is a **firewall / characterization test over already-correct behavior**, not a red-green feature test — the same shape as milestone-2's Task-1 pin and the existing `test/cure/elab/emit_hole_firewall_test.exs`. The behavior it asserts (expanded AST is elaborated identically to hand-written) *already works*; the test's value is permanently *locking* it. So Step "run and expect FAIL" does **not** apply to the accept/reject assertions — they pass immediately. What IS genuinely falsifiable and MUST be demonstrated red-first is the **negative control** (Step 2 below): a deliberately-broken variant of the equality helper that would pass a bypassing implementation, shown to fail, proving the test has teeth. See Task 1 Step 2.

**Verified examples (probed live against the current tree with `Program.elaborate/1` — these exact verdicts are real, not assumed):**
- `zero`→`0` used as `Int` ⇒ `{:ok, _}` (accept). Hand-written `fn f() -> Int = 0` ⇒ `{:ok, _}`.
- `inc <x: Code>`→`x + 1`, `inc n` on an `Int` param ⇒ `{:ok, _}` (accept, hole substituted).
- `bad`→`nonexistent_thing` used as `Int` ⇒ `{:error, :unknown_global}`. Hand-written `fn f() -> Int = nonexistent_thing` ⇒ **the same** `{:error, :unknown_global}`.
- `tt`→`true` used as `Int` ⇒ `{:error, {:conversion_failure, {:data, :Bool, [], []}, {:int_type}}}`. Hand-written `fn f() -> Int = true` ⇒ **the same** term. (Error terms here are position-free, so `==` between macro and hand-written verdicts is exact.)

---

### Task 1: The macro-expansion soundness firewall

**Files:**
- Create: `test/cure/elab/macro_expansion_soundness_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.elaborate/1` — `{:ok, Env.t()} | {:error, term()}`.
- Produces: nothing importable — a test module. Its value is the locked property, exercised by SP3's generative fuzz later (SP3 calls `Program.elaborate` directly; this task does not build a wrapper — YAGNI).

- [ ] **Step 1: Write the firewall test file**

The core property is `verdict(macro_src) == verdict(handwritten_src)`, where `verdict/1` reduces an elaborate result to a position-free comparable shape. Because the accept case's `Env` is large and not value-comparable, `verdict/1` maps `{:ok, _} -> :accept` and passes `{:error, term}` through verbatim (the four chosen error terms are position-free — asserted by the negative control in Step 2).

```elixir
# test/cure/elab/macro_expansion_soundness_test.exs
defmodule Cure.Elab.MacroExpansionSoundnessTest do
  # SOUNDNESS FIREWALL. The entire macro facility rests on one claim: a macro's
  # expansion is type-checked exactly like hand-written code — expansion is a
  # parse-time surface-AST rewrite, so the *unchanged* elaborator+kernel judge
  # it, and nothing reaches codegen unelaborated (TCB delta zero). This test
  # proves it by verdict-equality: each macro program elaborates to the IDENTICAL
  # result as the hand-written program it expands to — accepting when well-typed,
  # and rejecting with the SAME error term when ill-typed (well-formed-but-
  # mistyped included). If a future change ever lets macro output bypass
  # elaboration, one of these equalities breaks.
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Reduce an elaborate result to a position-free comparable verdict. Accept
  # collapses to :accept (the Env is large and not meaningfully ==); reject
  # keeps its error term verbatim (the terms exercised here carry no line/col).
  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _env} -> :accept
      {:error, term} -> {:reject, term}
    end
  end

  # {label, macro_program, hand_written_equivalent}. Each macro_program's
  # expansion is textually the hand_written_equivalent's body.
  @cases [
    {"zero-hole accept: zero => 0",
     "mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept: inc <x> => x + 1",
     "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"reject (unknown global): bad => nonexistent_thing",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"reject (type mismatch): tt => true used as Int",
     "mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n",
     "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, hand_src} <- @cases do
    test "macro verdict equals hand-written verdict — #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(hand_src))
    end
  end

  # Pin the accept/reject SENSE too, so an implementation that made *both* sides
  # equally broken (e.g. every program rejects) can't pass by trivial equality.
  test "the two well-typed cases genuinely accept" do
    assert verdict("mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n") == :accept
    assert verdict("mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n") == :accept
  end

  test "the two ill-typed cases genuinely reject with a position-free error term" do
    assert {:reject, :unknown_global} =
             verdict("mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n")

    assert {:reject, {:conversion_failure, {:data, :Bool, [], []}, {:int_type}}} =
             verdict("mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n")
  end
end
```

- [ ] **Step 2: Prove the firewall has teeth (negative control, red-first)**

Before trusting the green suite, demonstrate the test would CATCH a bypass. Temporarily add this throwaway test to the file, run it, confirm it FAILS, then delete it (it is a scaffold, not part of the committed suite):

```elixir
  # THROWAWAY — delete after confirming it fails. Simulates a "bypass" where the
  # macro program were NOT elaborated (verdict forced to :accept regardless).
  # If verdict-equality had no teeth, this would pass; it must fail on the
  # ill-typed pair, proving the real tests detect an un-elaborated expansion.
  test "NEGATIVE CONTROL (delete me)" do
    bypass = fn _src -> :accept end
    hand = verdict("mod M\n  fn f() -> Int = true\n")   # {:reject, {:conversion_failure, ...}}
    assert bypass.("...") == hand                        # :accept == {:reject,...} -> FAILS
  end
```

Run: `mix test test/cure/elab/macro_expansion_soundness_test.exs`
Expected: the NEGATIVE CONTROL test FAILS (`:accept` ≠ `{:reject, {:conversion_failure, …}}`); all six real tests PASS. This is the red evidence that the equality assertions are non-trivial. **Then delete the NEGATIVE CONTROL test.**

- [ ] **Step 3: Run the committed test file — expect all green**

Run: `mix test test/cure/elab/macro_expansion_soundness_test.exs`
Expected: 6 passed (4 verdict-equality + accept-sense + reject-sense), 0 failures, negative control removed.

- [ ] **Step 4: Confirm zero production delta**

Run: `git -C . status --porcelain`
Expected: the ONLY change is the new untracked `test/cure/elab/macro_expansion_soundness_test.exs`. No `lib/**` file modified. (If any `lib/**` changed, the task was mis-executed — revert and reassess: this task is test-only by construction.)

- [ ] **Step 5: Full suite — no regression**

Run: `mix test` (once, alone). Expected: green at the milestone-2 baseline + the new tests (~4103 passed / 2 skipped, antigen coverage intact). Confirm `test/antigen/seeds.sexp` and `corpus.sexp` are untouched.

- [ ] **Step 6: Commit**

```bash
git add -- test/cure/elab/macro_expansion_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(macros): soundness firewall — macro expansion elaborated identically to hand-written (SP1 T8)"
```

---

## Task boundary + what remains in SP1

T8 locks the DONE-criterion clause **"expands to well-typed Core"** with a permanent guard: macro output is proven indistinguishable from hand-written code at the elaborator, so it cannot smuggle an ill-typed (or well-formed-but-mistyped) term past the kernel. SP3's generative expansion proof will *fuzz* this same `Program.elaborate` primitive across randomly-generated use-sites; T8 is the hand-picked, position-exact anchor that fuzzing generalizes.

**Remaining SP1 tasks** (subsequent Stage-2 rounds, in priority order):
- **T7 — hygiene:** `<fresh Name>` gensym in templates + capture-avoidance, so a template-introduced binder cannot capture a use-site name and vice-versa. Milestone-2 expansion is deliberately unhygienic; T7 makes name-binding templates safe. Needs its own grounding (a template-binder example, a capture repro) and its own plan `…-sp1d-plan.md`. This is a real red-green feature (capture repro → red → gensym fix → green).
- **T4 — `literal` rules + numeric-suffix lexer** (`500ms`): the one lexer change; also unblocks bounded hole+literal segment matching.
- **T9 — cross-module (imported) macros + import scoping + same-keyword conflict; two-pass name resolution.**

When T7/T4/T9 are executed + code-reviewed, run SP1's own Stage 6 (full `mix test`), update the state file, and start **SP2** (Tier 3 + the self-proving typed-error obligations). The end-to-end DONE proof ("its expansion runs") is a final integration step after SP3.
