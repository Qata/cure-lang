%default total

-- THE PREFIX-COUNT CORE of Fidge-Mattern COMPLETENESS. Soundness (fidge_mattern) shows a -> b implies
-- VC(a) < VC(b); completeness is the converse and is FALSE on raw vector clocks -- it needs the RETROSPECTIVE
-- characterisation VC(e)[i] = #{ process-i events causally <= e }. That count is the popcount of a boolean
-- bitmask: for coordinate i, mark position k with T iff the k-th event of process i causally precedes-or-equals
-- e. Program order makes that mask DOWNWARD CLOSED (if k is in the past, so is every earlier position), i.e.
-- a run of Ts followed by Fs -- captured by `Prefix`. The load-bearing combinatorial fact is then: position k
-- reads T EXACTLY WHEN k is below the popcount. `threshold` proves it. Everything Fidge-Mattern completeness
-- adds on top (diagonal, coordinate projection) reduces to this lemma at coordinate proc(a).

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

-- A process's causal-past bitmask: entry k = "does the k-th event of this process causally precede-or-equal b?"
data Flags = FNil | FCons Bool2 Flags

-- The vector-clock coordinate: how many events of this process are in the past (the popcount).
countTrue : Flags -> Natt
countTrue FNil = Z
countTrue (FCons T r) = S (countTrue r)
countTrue (FCons F r) = countTrue r

-- Read position k (out of range = F, i.e. not in the past).
nth : Flags -> Natt -> Bool2
nth FNil _ = F
nth (FCons x r) Z = x
nth (FCons x r) (S k) = nth r k

-- An all-F suffix: no further events are in the past.
data AllF : Flags -> Type where
  AFNil  : AllF FNil
  AFCons : (r : Flags) -> AllF r -> AllF (FCons F r)

allfNth : (fs : Flags) -> AllF fs -> (k : Natt) -> nth fs k = F
allfNth FNil AFNil k = Refl
allfNth (FCons F r) (AFCons r h2) Z = Refl
allfNth (FCons F r) (AFCons r h2) (S k2) = allfNth r h2 k2

allfCount : (fs : Flags) -> AllF fs -> countTrue fs = Z
allfCount FNil AFNil = Refl
allfCount (FCons F r) (AFCons r h2) = allfCount r h2

-- DOWNWARD CLOSED: a run of Ts (the causal past, a prefix by program order) followed by an all-F suffix.
data Prefix : Flags -> Type where
  PBase : (fs : Flags) -> AllF fs -> Prefix fs
  PT    : (fs : Flags) -> Prefix fs -> Prefix (FCons T fs)

-- THE THRESHOLD LEMMA: for a downward-closed mask, position k is in the past EXACTLY WHEN k is below the
-- popcount. This is the whole content of "comparing the VC coordinate decides causal precedence".
threshold : (fs : Flags) -> Prefix fs -> (k : Natt) -> nth fs k = leq (S k) (countTrue fs)
threshold fs (PBase _ af) k = rewrite allfCount fs af in rewrite allfNth fs af k in Refl
threshold (FCons T fs2) (PT _ p2) Z = Refl
threshold (FCons T fs2) (PT _ p2) (S k2) = threshold fs2 p2 k2
