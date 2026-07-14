# Autopilot completion report — OTP conformance fixes

**Branch:** `autopilot/otp-conformance-fixes` (11 commits on top of `811b3507`)
**Worktree:** `.claude/worktrees/otp-conformance-fixes`
**Final state:** `mix test` → **4137 passed, 1 skipped, 0 failures.** Antigen shape-coverage 318/318.
**Not merged.** The operator merges.

## What this fixed

The executed conformance audit (`docs/research/process-types/raw-algebra-conformance-checklist.md`)
found five defects where `Std.Otp` / `Std.Otp.Raw` claimed more than the BEAM delivers. All five
are closed; F-1 was out of scope from the start (see Deferred).

| # | Defect | Fix |
|---|---|---|
| F-2c | `whereis` asserted a pid; the BIF returns the atom `undefined` when unregistered | Returns `Effect(Option(BarePid))`. `BarePid` carries an uninhabited message type, so a registry-recovered handle is supervisable but **not sendable** — nothing associates a NAME with a message TYPE. |
| F-2 | `Pid(m)` ≡ `GenServer(q, r)`, so `call` on a plain process typechecked (and would hang 5s, then kill the caller) | An erased phantom tag (`Plain` / `Server`) as `RawPid`'s third argument. `call`/`cast`/`stop` are `Server`-only; signal ops stay tag-polymorphic. Zero runtime cost. |
| F-4 | Ten raw ops declared `Effect(Unit)` for BIFs returning real terms — and `emit.ex` does no result coercion, so the message / `true` / `ok` / an integer was *inhabiting `Unit`* | Every raw op now carries its audited return type. Typed wrappers discard where the answer is constant; `cancel_timer` surfaces `Option(Int)`, because "the timer already fired" is information a caller must be able to see. |
| F-3 | `exit`'s reason was fully polymorphic, erasing the very distinction the BEAM's three exit rules turn on | `type ExitReason = Normal \| Kill \| Because(Atom)`. The raw op stays permissive — the raw base carries the most permissive *honest* type. |
| F-5 | `MonitorRef` and `TimerRef` were two aliases of one `Ref`, so `cancel_timer(monitor_ref)` typechecked; `demonitor` never flushed | Distinct opaque carriers, both erasing to `:reference`. `demonitor` now goes through `erlang:demonitor/2` with `[flush]`, so a `DOWN` already in the mailbox cannot outlive the call. |

Enabling machinery (elaborator, outside the kernel):

- **`@erases(<class>)`** — the human gate. An `opaque type` has no constructors, so no erasure is
  inferable; the decorator *declares* the runtime guard that recognises it. This is what lets an
  opaque carrier appear in a union at all.
- **`:pid` / `:reference` runtime classes** (`is_pid` / `is_reference`) in the union machinery.
- **`@extern` may now return `Effect(<union>)`** — it was *rejected* before, not miscompiled, so
  this is an enablement rather than a bug fix.

## Stage-by-stage

| Stage | Outcome |
|---|---|
| 0 Brainstorm | Design approved; spec written + committed. One human gate: **decorator over hardcoding** `RawPid → :pid`. |
| 1 Spec review | Hardened, committed by the subagent. |
| 2 Plan | 9 tasks, `docs/superpowers/plans/2026-07-14-otp-conformance-fixes-plan.md`. |
| 3 Plan review | Hardened → `811b3507`. |
| 4 Execute | 9 tasks, strict red-green, one commit each (`c61d06b7` … `47427c21`). |
| 5 Code review | Converged; 2 confirmed findings fixed red-test-first (`815dc296`, `cf6b5f27`). |
| 6 Verify | Full suite green. |

The code review's substantive catch: `erasure_class/2` had a catch-all that treated a *malformed*
`@erases` (`@erases()`, `@erases(:pid, :reference)`, `@erases(pid)` — no colon) exactly like an
absent one, silently yielding `erasure: nil` with **zero diagnostic**. A typo in the decorator
would have quietly disabled the guard it was supposed to declare. Now rejected with a named error.

## Things the operator should know

1. **TCB delta:** `lib/cure/core/inductive.ex`, +16/−3 — the sanctioned `erasure` field on the
   opaque-family record, and nothing else. No other kernel file is touched.
2. **Three pre-existing tests were edited.** Two were sanctioned by the plan (`stop_it` retyped to
   `GenServer`; the `beam_ops` lifecycle test's refs retyped to `TimerRef`/`MonitorRef`). The third
   was **not** in the plan: `test/cure/stdlib/otp_raw_test.exs`'s `raw_self` Core-type pin now
   expects the 3-argument `RawPid`. It is a shape pin updated to a deliberately-changed shape, not
   a defect assertion weakened away — but it is a test edit and you should see it.
3. **A deliberate deviation from the plan.** Task 2 Step 4 called for explicit `:pid`/`:reference`
   overlap clauses in `union.ex`. They were skipped as dead code: `class_overlap?(c, c) → true` plus
   `refines?/2`'s false catch-all already give the right answer. The code reviewer independently
   verified this holds.
4. **A printer gap surfaced, and was fixed.** `Cure.Compiler.Printer` had no clause for `()` — the
   parser gives the unit value its own node kind, and no stdlib file had ever used one until the
   discard shape did. `cure fmt` / `cure migrate` raised on any file containing `()`. Fixed, with a
   round-trip pin in `printer_fidelity_test.exs`. Unrelated to OTP; found by the corpus tests.
5. **`otp_raw_pin_test.exs` is a claim about the BEAM, not a test to update.** It pins every raw op's
   declared return type — the concrete `no_widening_narrow` validator the parent spec's §12 asked
   for and never got. If it goes red, re-probe the BIF before repinning.
6. **AtomVM hazard, documented at the op.** `erlang:send_after/3` on AtomVM registers its timer under
   a *different* ref than the one it returns, so cancelling a `send_after` ref there always yields
   `None` **and the message still fires**. Cancellation is reliable on OTP; on AtomVM it is not.

## Deferred (unchanged, and deliberately so)

- **F-1 — the pid message index is founded on nothing.** Recovering a *typed* handle from a
  registered name needs a name-to-code association nothing builds yet. Rung 2; gated on the macro
  facility. `BarePid` is the honest interim answer: you may `link`/`monitor`/`exit`/`is_alive` it,
  you may not `tell` to it.
- **`gen_server:call` is partial.** A timeout or a dead server exits the caller. `Effect(r)` is
  *sound* — no value is ever returned at the wrong type — but not *total*. A `try_call` reifying the
  failure needs a try/catch shim.
- **The `start_link` family's `Effect(Tuple)`.** Honest on AtomVM; not on OTP, where an `init/1`
  returning `ignore` makes `start_link` return a bare atom. Typing it honestly means producing a
  typed handle from an untyped tuple — the same unfounded assertion as F-1, and deferred with it.
- **Typestate / §9.5.** Untouched, as the audit brief required.
