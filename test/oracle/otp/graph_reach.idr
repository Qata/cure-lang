%default total

-- GRAPH REACHABILITY. A graph given by an adjacency test edge; Reach is unbounded reachability (the
-- reflexive-transitive closure), ReachN is step-counted reachability (reachable in exactly k steps). Proved:
-- reachability is transitive (reachTrans, a preorder with RRefl); counted reachability COMPOSES ADDITIVELY
-- (reachnTrans: a j-step then a k-step walk is a (j+k)-step walk); and unbounded reachability EQUALS the
-- existence of a bounded walk (both directions). Every proof is edge-agnostic (only passes edge witnesses).

data Natt = Z | S Natt
data Bool2 = F | T

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

eqn : Natt -> Natt -> Bool2
eqn Z Z = T
eqn Z (S k) = F
eqn (S j) Z = F
eqn (S j) (S k) = eqn j k

edge : Natt -> Natt -> Bool2
edge u v = eqn (S u) v

data Reach : (u : Natt) -> (v : Natt) -> Type where
  RRefl : (x : Natt) -> Reach x x
  RStep : (u2 : Natt) -> (v2 : Natt) -> (mid : Natt) -> (edge u2 mid = T) -> Reach mid v2 -> Reach u2 v2

reachTrans : (u : Natt) -> (v : Natt) -> (w : Natt) -> Reach u v -> Reach v w -> Reach u w
reachTrans x x w (RRefl x) r2 = r2
reachTrans u2 v w (RStep u2 v mid e r0) r2 = RStep u2 w mid e (reachTrans mid v w r0 r2)

data ReachN : (k : Natt) -> (u : Natt) -> (v : Natt) -> Type where
  RN0 : (x : Natt) -> ReachN Z x x
  RNS : (k2 : Natt) -> (u2 : Natt) -> (v2 : Natt) -> (mid : Natt) -> (edge u2 mid = T) -> ReachN k2 mid v2 -> ReachN (S k2) u2 v2

reachnTrans : (j : Natt) -> (u : Natt) -> (v : Natt) -> (k : Natt) -> (w : Natt) -> ReachN j u v -> ReachN k v w -> ReachN (plus j k) u w
reachnTrans Z x x k w (RN0 x) r2 = r2
reachnTrans (S j0) u2 v k w (RNS j0 u2 v mid e r0) r2 = RNS (plus j0 k) u2 w mid e (reachnTrans j0 mid v k w r0 r2)

data ExReachN : (u : Natt) -> (v : Natt) -> Type where
  MkEx : (k : Natt) -> (u2 : Natt) -> (v2 : Natt) -> ReachN k u2 v2 -> ExReachN u2 v2

reachnToReach : (k : Natt) -> (u : Natt) -> (v : Natt) -> ReachN k u v -> Reach u v
reachnToReach Z x x (RN0 x) = RRefl x
reachnToReach (S k0) u2 v2 (RNS k0 u2 v2 mid e r0) = RStep u2 v2 mid e (reachnToReach k0 mid v2 r0)

reachToEx : (u : Natt) -> (v : Natt) -> Reach u v -> ExReachN u v
reachToEx x x (RRefl x) = MkEx Z x x (RN0 x)
reachToEx u2 v2 (RStep u2 v2 mid e r0) = case reachToEx mid v2 r0 of
  MkEx k mu mv rn => MkEx (S k) u2 v2 (RNS k u2 v2 mid e rn)

exToReach : (u : Natt) -> (v : Natt) -> ExReachN u v -> Reach u v
exToReach u2 v2 (MkEx k u2 v2 rn) = reachnToReach k u2 v2 rn
