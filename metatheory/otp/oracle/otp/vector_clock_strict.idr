%default total

-- STRICT CAUSAL PRECEDENCE IS A STRICT PARTIAL ORDER, and local events strictly advance the clock. The
-- strict happens-before order on vector clocks is u < v := u <= v AND NOT v <= u (the poset strict order).
-- Proved irreflexive, asymmetric, and transitive (causal precedence composes with no cycles). Plus: a local
-- tick strictly advances the clock (tickStrict), so successive events on ONE process are strictly ordered by
-- their clocks -- the program-order soundness of vector clocks (a leg of Fidge-Mattern).

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

leqSuccSelfF : (a : Natt) -> leq (S a) a = F
leqSuccSelfF Z = Refl
leqSuccSelfF (S k) = leqSuccSelfF k

leSucc : (a : Natt) -> leq a (S a) = T
leSucc Z = Refl
leSucc (S k) = leSucc k

leTrans : (a : Natt) -> (b : Natt) -> (c : Natt) -> leq a b = T -> leq b c = T -> leq a c = T
leTrans Z b c hab hbc = Refl
leTrans (S a2) Z c hab hbc = case hab of Refl impossible
leTrans (S a2) (S b2) Z hab hbc = case hbc of Refl impossible
leTrans (S a2) (S b2) (S c2) hab hbc = leTrans a2 b2 c2 hab hbc

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

notbTrue : (b : Bool2) -> notb b = T -> b = F
notbTrue T e = case e of Refl impossible
notbTrue F e = Refl

notbF : (b : Bool2) -> b = F -> notb b = T
notbF b e = rewrite e in Refl

boolMt : (b : Bool2) -> (c : Bool2) -> c = F -> (b = T -> c = T) -> b = F
boolMt T c hc g = case trans (sym (g Refl)) hc of Refl impossible
boolMt F c hc g = Refl

data VC = VNil | VCons Natt VC

vcLe : VC -> VC -> Bool2
vcLe VNil v = T
vcLe (VCons x u2) VNil = F
vcLe (VCons x u2) (VCons y v2) = andb (leq x y) (vcLe u2 v2)

vcLeRefl : (u : VC) -> vcLe u u = T
vcLeRefl VNil = Refl
vcLeRefl (VCons x u2) = andbIntro (leq x x) (vcLe u2 u2) (leqRefl x) (vcLeRefl u2)

vcLeTrans : (u : VC) -> (v : VC) -> (w : VC) -> vcLe u v = T -> vcLe v w = T -> vcLe u w = T
vcLeTrans VNil v w h1 h2 = Refl
vcLeTrans (VCons x u2) VNil w h1 h2 = case h1 of Refl impossible
vcLeTrans (VCons x u2) (VCons y v2) VNil h1 h2 = case h2 of Refl impossible
vcLeTrans (VCons x u2) (VCons y v2) (VCons z w2) h1 h2 =
  andbIntro (leq x z) (vcLe u2 w2)
    (leTrans x y z (andbTrueL (leq x y) (vcLe u2 v2) h1) (andbTrueL (leq y z) (vcLe v2 w2) h2))
    (vcLeTrans u2 v2 w2 (andbTrueR (leq x y) (vcLe u2 v2) h1) (andbTrueR (leq y z) (vcLe v2 w2) h2))

vcLt : VC -> VC -> Bool2
vcLt u v = andb (vcLe u v) (notb (vcLe v u))

vcLtIrrefl : (u : VC) -> vcLt u u = F
vcLtIrrefl u = rewrite vcLeRefl u in Refl

vcLtAsym : (u : VC) -> (v : VC) -> vcLt u v = T -> vcLt v u = F
vcLtAsym u v h = rewrite notbTrue (vcLe v u) (andbTrueR (vcLe u v) (notb (vcLe v u)) h) in Refl

vcLtTrans : (u : VC) -> (v : VC) -> (w : VC) -> vcLt u v = T -> vcLt v w = T -> vcLt u w = T
vcLtTrans u v w h1 h2 =
  andbIntro (vcLe u w) (notb (vcLe w u))
    (vcLeTrans u v w (andbTrueL (vcLe u v) (notb (vcLe v u)) h1) (andbTrueL (vcLe v w) (notb (vcLe w v)) h2))
    (notbF (vcLe w u)
      (boolMt (vcLe w u) (vcLe w v)
        (notbTrue (vcLe w v) (andbTrueR (vcLe v w) (notb (vcLe w v)) h2))
        (\hwu => vcLeTrans w u v hwu (andbTrueL (vcLe u v) (notb (vcLe v u)) h1))))

tick : Natt -> VC -> VC
tick i VNil = VNil
tick Z (VCons x r) = VCons (S x) r
tick (S k) (VCons x r) = VCons x (tick k r)

tickMono : (i : Natt) -> (v : VC) -> vcLe v (tick i v) = T
tickMono i VNil = Refl
tickMono Z (VCons x r) = andbIntro (leq x (S x)) (vcLe r r) (leSucc x) (vcLeRefl r)
tickMono (S k) (VCons x r) = andbIntro (leq x x) (vcLe r (tick k r)) (leqRefl x) (tickMono k r)

data InRange : (i : Natt) -> (v : VC) -> Type where
  IRHere  : (x : Natt) -> (r : VC) -> InRange Z (VCons x r)
  IRThere : (x : Natt) -> (k : Natt) -> (r : VC) -> InRange k r -> InRange (S k) (VCons x r)

tickGt : (i : Natt) -> (v : VC) -> InRange i v -> vcLe (tick i v) v = F
tickGt Z (VCons x r) (IRHere x r) = rewrite leqSuccSelfF x in Refl
tickGt (S k) (VCons x r) (IRThere x k r hir2) = rewrite leqRefl x in rewrite tickGt k r hir2 in Refl

tickStrict : (i : Natt) -> (v : VC) -> InRange i v -> vcLt v (tick i v) = T
tickStrict i v hir =
  andbIntro (vcLe v (tick i v)) (notb (vcLe (tick i v) v)) (tickMono i v) (notbF (vcLe (tick i v) v) (tickGt i v hir))
