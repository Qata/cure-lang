%default total

-- VECTOR CLOCKS AND THE CAUSAL ORDER. A vector clock is one Natt counter per process; the causal
-- (happens-before-or-equal) order is the POINTWISE order on clocks. The core metatheory of logical time:
-- that order is a PARTIAL ORDER (reflexive, transitive, antisymmetric), the induced strict order is
-- irreflexive, and concurrency (causal incomparability) is symmetric. This is the substrate of causality
-- for message-passing / BEAM systems.

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

leTrans : (a : Natt) -> (b : Natt) -> (c : Natt) -> leq a b = T -> leq b c = T -> leq a c = T
leTrans Z b c hab hbc = Refl
leTrans (S a2) Z c hab hbc = case hab of Refl impossible
leTrans (S a2) (S b2) Z hab hbc = case hbc of Refl impossible
leTrans (S a2) (S b2) (S c2) hab hbc = leTrans a2 b2 c2 hab hbc

leqAntisym : (a : Natt) -> (b : Natt) -> leq a b = T -> leq b a = T -> a = b
leqAntisym Z Z h1 h2 = Refl
leqAntisym Z (S k) h1 h2 = case h1 of Refl impossible
leqAntisym (S j) Z h1 h2 = case h1 of Refl impossible
leqAntisym (S j) (S k) h1 h2 = cong S (leqAntisym j k h1 h2)

eqn : Natt -> Natt -> Bool2
eqn Z Z = T
eqn Z (S k) = F
eqn (S j) Z = F
eqn (S j) (S k) = eqn j k

eqnRefl : (a : Natt) -> eqn a a = T
eqnRefl Z = Refl
eqnRefl (S k) = eqnRefl k

andb : Bool2 -> Bool2 -> Bool2
andb T b = b
andb F b = F

notb : Bool2 -> Bool2
notb T = F
notb F = T

andbTrueL : (a : Bool2) -> (b : Bool2) -> andb a b = T -> a = T
andbTrueL T b e = Refl
andbTrueL F b e = case e of Refl impossible

andbTrueR : (a : Bool2) -> (b : Bool2) -> andb a b = T -> b = T
andbTrueR T b e = e
andbTrueR F b e = case e of Refl impossible

andbIntro : (a : Bool2) -> (b : Bool2) -> a = T -> b = T -> andb a b = T
andbIntro T b ea eb = eb
andbIntro F b ea eb = case ea of Refl impossible

andbComm : (a : Bool2) -> (b : Bool2) -> andb a b = andb b a
andbComm T T = Refl
andbComm T F = Refl
andbComm F T = Refl
andbComm F F = Refl

data VC = VNil | VCons Natt VC

vcLe : VC -> VC -> Bool2
vcLe VNil VNil = T
vcLe VNil (VCons y v2) = F
vcLe (VCons x u2) VNil = F
vcLe (VCons x u2) (VCons y v2) = andb (leq x y) (vcLe u2 v2)

vcEq : VC -> VC -> Bool2
vcEq VNil VNil = T
vcEq VNil (VCons y v2) = F
vcEq (VCons x u2) VNil = F
vcEq (VCons x u2) (VCons y v2) = andb (eqn x y) (vcEq u2 v2)

vcEqRefl : (u : VC) -> vcEq u u = T
vcEqRefl VNil = Refl
vcEqRefl (VCons x u2) = andbIntro (eqn x x) (vcEq u2 u2) (eqnRefl x) (vcEqRefl u2)

vconsCong : (x : Natt) -> (y : Natt) -> (u2 : VC) -> (v2 : VC) -> (x = y) -> (u2 = v2) -> VCons x u2 = VCons y v2
vconsCong x y u2 v2 exy euv = trans (cong (\hh => VCons hh u2) exy) (cong (\tt => VCons y tt) euv)

vcLeRefl : (u : VC) -> vcLe u u = T
vcLeRefl VNil = Refl
vcLeRefl (VCons x u2) = andbIntro (leq x x) (vcLe u2 u2) (leqRefl x) (vcLeRefl u2)

vcLeTrans : (u : VC) -> (v : VC) -> (w : VC) -> vcLe u v = T -> vcLe v w = T -> vcLe u w = T
vcLeTrans VNil VNil VNil h1 h2 = Refl
vcLeTrans VNil VNil (VCons z w2) h1 h2 = case h2 of Refl impossible
vcLeTrans VNil (VCons y v2) w h1 h2 = case h1 of Refl impossible
vcLeTrans (VCons x u2) VNil w h1 h2 = case h1 of Refl impossible
vcLeTrans (VCons x u2) (VCons y v2) VNil h1 h2 = case h2 of Refl impossible
vcLeTrans (VCons x u2) (VCons y v2) (VCons z w2) h1 h2 =
  andbIntro (leq x z) (vcLe u2 w2)
    (leTrans x y z (andbTrueL (leq x y) (vcLe u2 v2) h1) (andbTrueL (leq y z) (vcLe v2 w2) h2))
    (vcLeTrans u2 v2 w2 (andbTrueR (leq x y) (vcLe u2 v2) h1) (andbTrueR (leq y z) (vcLe v2 w2) h2))

vcLeAntisym : (u : VC) -> (v : VC) -> vcLe u v = T -> vcLe v u = T -> u = v
vcLeAntisym VNil VNil h1 h2 = Refl
vcLeAntisym VNil (VCons y v2) h1 h2 = case h1 of Refl impossible
vcLeAntisym (VCons x u2) VNil h1 h2 = case h2 of Refl impossible
vcLeAntisym (VCons x u2) (VCons y v2) h1 h2 =
  vconsCong x y u2 v2
    (leqAntisym x y (andbTrueL (leq x y) (vcLe u2 v2) h1) (andbTrueL (leq y x) (vcLe v2 u2) h2))
    (vcLeAntisym u2 v2 (andbTrueR (leq x y) (vcLe u2 v2) h1) (andbTrueR (leq y x) (vcLe v2 u2) h2))

vcLt : VC -> VC -> Bool2
vcLt u v = andb (vcLe u v) (notb (vcEq u v))

vcConc : VC -> VC -> Bool2
vcConc u v = andb (notb (vcLe u v)) (notb (vcLe v u))

vcLtIrrefl : (u : VC) -> vcLt u u = F
vcLtIrrefl u = rewrite vcLeRefl u in rewrite vcEqRefl u in Refl

vcConcSym : (u : VC) -> (v : VC) -> vcConc u v = vcConc v u
vcConcSym u v = andbComm (notb (vcLe u v)) (notb (vcLe v u))
