%default total

-- FIDGE-MATTERN COMPLETENESS (the converse of the clock condition, the deferred hard direction).
-- Soundness (fidge_mattern) shows a -> b implies VC(a) < VC(b). Completeness is the converse: VC(a) <= VC(b)
-- implies a causally precedes-or-equals b. It is FALSE on raw vector clocks (unrelated stamps can compare),
-- so it needs event IDENTITY and the RETROSPECTIVE clock VC(e)[i] = #{ process-i events causally <= e }.
--
-- The proof pivots on the DIAGONAL coordinate p = proc(a). Two facts about a valid execution:
--   * diagonal: VC(a)[p] = S(pos a)  -- a's own coordinate counts a and all earlier same-process events;
--   * b's causal-past mask on process p is downward closed (`Prefix mb`), popcount = VC(b)[p].
-- Then vecLe(VC a)(VC b) projected at p gives VC(a)[p] <= VC(b)[p], i.e. S(pos a) <= popcount(mb); the
-- threshold lemma (fm_prefix_count) turns that into nth(mb, pos a) = T, which IS "a is in b's causal past".
-- exComplete discharges a concrete cross-process instance (a message 0->1) so the theorem is non-vacuous:
-- a = event (proc 0, pos 1) causally precedes b = event (proc 1, pos 1) through the message, and the VC order
-- correctly detects it.

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

andb : Bool2 -> Bool2 -> Bool2
andb T b = b
andb F b = F

andbTrueL : (a : Bool2) -> (b : Bool2) -> andb a b = T -> a = T
andbTrueL T b e = Refl
andbTrueL F b e = case e of Refl impossible

andbTrueR : (a : Bool2) -> (b : Bool2) -> andb a b = T -> b = T
andbTrueR T b e = e
andbTrueR F b e = case e of Refl impossible

-- Process p's causal-past bitmask relative to an event b: entry k = "k-th event of p causally <= b?".
data Flags = FNil | FCons Bool2 Flags

countTrue : Flags -> Natt
countTrue FNil = Z
countTrue (FCons T r) = S (countTrue r)
countTrue (FCons F r) = countTrue r

nth : Flags -> Natt -> Bool2
nth FNil _ = F
nth (FCons x r) Z = x
nth (FCons x r) (S k) = nth r k

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

data Prefix : Flags -> Type where
  PBase : (fs : Flags) -> AllF fs -> Prefix fs
  PT    : (fs : Flags) -> Prefix fs -> Prefix (FCons T fs)

-- THE THRESHOLD LEMMA (fm_prefix_count): position k is in the past exactly when k is below the popcount.
threshold : (fs : Flags) -> Prefix fs -> (k : Natt) -> nth fs k = leq (S k) (countTrue fs)
threshold fs (PBase _ af) k = rewrite allfCount fs af in rewrite allfNth fs af k in Refl
threshold (FCons T fs2) (PT _ p2) Z = Refl
threshold (FCons T fs2) (PT _ p2) (S k2) = threshold fs2 p2 k2

-- A full vector clock and its pointwise order.
data Vec = VNil | VCons Natt Vec

proj : Vec -> Natt -> Natt
proj VNil _ = Z
proj (VCons x r) Z = x
proj (VCons x r) (S i) = proj r i

vecLe : Vec -> Vec -> Bool2
vecLe VNil v = T
vecLe (VCons x u2) VNil = F
vecLe (VCons x u2) (VCons y v2) = andb (leq x y) (vecLe u2 v2)

-- Pointwise <= projects to each coordinate.
vecLeProj : (u : Vec) -> (v : Vec) -> vecLe u v = T -> (i : Natt) -> leq (proj u i) (proj v i) = T
vecLeProj VNil v h i = Refl
vecLeProj (VCons x u2) VNil h i = case h of Refl impossible
vecLeProj (VCons x u2) (VCons y v2) h Z = andbTrueL (leq x y) (vecLe u2 v2) h
vecLeProj (VCons x u2) (VCons y v2) h (S i2) = vecLeProj u2 v2 (andbTrueR (leq x y) (vecLe u2 v2) h) i2

-- The diagonal coordinate carries the whole argument: S(pos a) <= popcount(b's mask on proc a).
leCoord : (va : Vec) -> (vb : Vec) -> (p : Natt) -> (ka : Natt) -> (mb : Flags) ->
          proj va p = S ka -> proj vb p = countTrue mb -> vecLe va vb = T ->
          leq (S ka) (countTrue mb) = T
leCoord va vb p ka mb hdiag hcoord hle =
  rewrite sym hdiag in rewrite sym hcoord in vecLeProj va vb hle p

-- COMPLETENESS: if VC(a) <= VC(b) pointwise, then a is in b's causal past (nth mb (pos a) = T), given the
-- diagonal and the downward-closed past mask -- i.e. comparing vector clocks is COMPLETE for causality.
completeness : (va : Vec) -> (vb : Vec) -> (p : Natt) -> (ka : Natt) -> (mb : Flags) ->
               Prefix mb -> proj va p = S ka -> proj vb p = countTrue mb -> vecLe va vb = T ->
               nth mb ka = T
completeness va vb p ka mb pb hdiag hcoord hle =
  trans (threshold mb pb ka) (leCoord va vb p ka mb hdiag hcoord hle)

-- NON-VACUOUS concrete instance: a genuine cross-process message 0->1.
-- a = (proc 0, pos 1), VC = [2,0];  b = (proc 1, pos 1), VC = [2,2];  b's mask on proc 0 = [T,T].
-- completeness fires at coordinate p=0: S(1) <= 2 = popcount, so a is in b's cut -- which is TRUE (a precedes
-- b through the message), and the vector-clock order detected it.
exComplete : nth (FCons T (FCons T FNil)) (S Z) = T
exComplete =
  completeness (VCons (S (S Z)) (VCons Z VNil))
               (VCons (S (S Z)) (VCons (S (S Z)) VNil))
               Z (S Z)
               (FCons T (FCons T FNil))
               (PT (FCons T FNil) (PT FNil (PBase FNil AFNil)))
               Refl Refl Refl
