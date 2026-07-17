# Adequacy — the shape of tying `infer` to the metatheory, and its matches

*2026-07-17. The one piece of G9 I had called "no external match" — connecting `infer(behaviour)`
to the operational safety theorems — turns out to decompose into three parts, EACH with a
concrete matching shape in the cloned references. The composition is novel; the pieces are not.*

**A precise comparison (NOT "ahead").** Proof of Delivery (Rocq) and Cure's `Std.Otp.*`
mechanized COMPLEMENTARY halves, and neither dominates:
- PoD mechanized the mailbox-type ALGEBRA richly — patterns as COMMUTATIVE REGULAR EXPRESSIONS,
  derivatives, subtyping — and DEFERRED the operational semantics + preservation theorem.
- Cure has an operational reduction + a PRESERVATION theorem — but only for the TAG-SET fragment
  (an interface is a flat accepted-set), the DEGENERATE case of PoD's patterns.
So Cure already has the operational-preservation PIECE PoD deferred, but at a much LOWER type
expressiveness; on the type language itself (patterns, subtyping) PoD is well ahead. The two are
complementary, not ranked.

## The shape

**Adequacy = the fundamental theorem of type soundness, parameterized by inference:** the
statically-inferred interface is preserved by the operational reduction of the behaviour it was
inferred from — so a process typed by inference never delivers a message it cannot handle. It
decomposes:

1. **`config ⊨ interface` — the semantic relation.** A configuration satisfies an interface
   when every message in flight and in its mailbox is accepted by it. In the tag-set fragment
   this is `AllMember(ether, I) ∧ AllMember(mailbox, I)` (`WTat` in
   `scaffolds/inference_adequacy.cure`); in the full theory it is the commutative-regex-PATTERN
   relation, order-insensitive.

2. **Preservation at the inferred interface — the operational half.** `config ⊨ I` is preserved
   by every typed step (`preservation_at`, PROVED in the scaffold). This is `Std.Otp.Preservation`
   generalized from a fixed accepted-set to an arbitrary interface `I = infer(b)`.

3. **The bridge — inference ⇒ semantic typing.** That `b`'s operational steps are all typed at
   `infer(b)` — its sends land in `infer(b)`, its receives are handled — is the COVERAGE the
   constraint generator provides; composed with (2) over the run, it gives adequacy
   (`?adequacy`, the hole; provable for the first-order fold, needs the frontier `lfp` for
   recursion).

## The matches (all in cloned references)

| Adequacy piece | Matching shape |
|---|---|
| **1. `config ⊨ pattern` relation** (order-insensitive) | **Proof of Delivery** (Rocq, the PDF in this dir): "patterns as a RELATION between a configuration and a pattern, via list permutations, instead of infinite multisets" — the exact shape, mechanized. Also my `Std.Otp.WT`/`WTat` for the tag fragment. |
| **2. operational preservation** | **PLFA** `preserve` (Agda STLC subject reduction) — the canonical shape my `Std.Otp.Preservation`/`Safety` already mirror. **Proof of Delivery EXPLICITLY LEAVES THIS OPEN** for mailbox types ("a full account of Pat's operational semantics and preservation theorem … is left [for future work]"). So Cure already HAS what the SOTA mechanization deferred. |
| **3. fundamental-theorem bridge** (syntactic typing ⇒ semantic) | **Actris** `actris/logrel/term_typing_judgment.v` + `term_typing_rules.v` — the semantic typing judgment `⊨` (`ltyped`) and each syntactic rule proven semantically sound (`ltyped_var`, `ltyped_subsumption`, …). The logical-relations fundamental lemma. |

## The upshot

Nothing in adequacy is unmatched. The static relation ports from Proof of Delivery; the bridge
from Actris's logical relation; the operational preservation Cure already has (and is the piece
PoD deferred). The genuinely NEW work is the COMPOSITION — proving the three fit together over
*this* project's `Std.Otp.*` reduction — but every part has a shape to port, and the hardest
part (operational preservation for mailbox-typed configurations) is done.

**Concretely provable next step:** the first-order fold fragment (no `BRec`) makes `?adequacy`
dischargeable outright — induction on the run, `RStart ↦ MkWTat(AMNil, AMNil)`, `RStep ↦
preservation_at ∘ IH`, with send-coverage `BSend(t,k) ⟹ Member(t, infer(b))` immediate from the
fold. Proving THAT turns the scaffold's `?adequacy` into a theorem for the first-order case —
the mailbox-inference adequacy the literature has only stated, not mechanized against an
operational reduction — leaving only the recursive (`lfp`) fragment holed.

## References (cloned to `~/Develop`)

`mbcheck` (algorithm), `plfa` (preservation shape), `actris` (logical-relations fundamental
lemma), `mathlib4` (fixpoint / Presburger), `lean4` (omega / monotonicity). Proof of Delivery is
a Rocq artifact behind DOIs (not cloned); its shape is read from the PDF in this directory.
