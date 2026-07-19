%default total

-- VERIFIED EUCLIDEAN DIVISION. For every a and divisor S b0, division yields a quotient q and remainder r
-- with q*(S b0) + r = a and r < S b0. CORRECT BY CONSTRUCTION: dm returns a DivResult that BUNDLES q, r, and
-- the two proofs, indexed by the INPUTS a, b0 (so there is no stuck-computation index to unify). Fuel-bounded
-- recursion with a sufficiency argument (div_fuel_ok) and an evidence-carrying strict comparison (ltDec);
-- the recursive step reconstitutes a = S b0 + (q*(S b0)+r) = (S q)*(S b0)+r via plusMonus.

data Natt = Z | S Natt
data Bool2 = F | T

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

leSucc : (a : Natt) -> leq a (S a) = T
leSucc Z = Refl
leSucc (S k) = leSucc k

leTrans : (a : Natt) -> (b : Natt) -> (c : Natt) -> leq a b = T -> leq b c = T -> leq a c = T
leTrans Z b c hab hbc = Refl
leTrans (S a2) Z c hab hbc = case hab of Refl impossible
leTrans (S a2) (S b2) Z hab hbc = case hbc of Refl impossible
leTrans (S a2) (S b2) (S c2) hab hbc = leTrans a2 b2 c2 hab hbc

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

times : Natt -> Natt -> Natt
times Z b = Z
times (S k) b = plus b (times k b)

snatCong : (a : Natt) -> (b : Natt) -> a = b -> S a = S b
snatCong a b e = cong S e

plusAssoc : (a : Natt) -> (b : Natt) -> (c : Natt) -> plus (plus a b) c = plus a (plus b c)
plusAssoc Z b c = Refl
plusAssoc (S k) b c = cong S (plusAssoc k b c)

plusCongR : (a : Natt) -> (b : Natt) -> (c : Natt) -> b = c -> plus a b = plus a c
plusCongR a b c e = cong (plus a) e

monus : Natt -> Natt -> Natt
monus a Z = a
monus Z (S j) = Z
monus (S k) (S j) = monus k j

monusLe : (a : Natt) -> (b : Natt) -> leq (monus a b) a = T
monusLe Z Z = Refl
monusLe Z (S j) = Refl
monusLe (S a0) Z = leqRefl (S a0)
monusLe (S a0) (S b0) = leTrans (monus a0 b0) a0 (S a0) (monusLe a0 b0) (leSucc a0)

monusLt : (a : Natt) -> (b0 : Natt) -> leq (S b0) a = T -> leq (S (monus a (S b0))) a = T
monusLt Z b0 hge = case hge of Refl impossible
monusLt (S a0) b0 hge = monusLe a0 b0

plusMonus : (b : Natt) -> (a : Natt) -> leq b a = T -> plus b (monus a b) = a
plusMonus Z a h = Refl
plusMonus (S b0) Z h = case h of Refl impossible
plusMonus (S b0) (S a0) h = snatCong (plus b0 (monus a0 b0)) a0 (plusMonus b0 a0 h)

data LtDec : (x : Natt) -> (y : Natt) -> Type where
  LtYes : (x2 : Natt) -> (y2 : Natt) -> (leq (S x2) y2 = T) -> LtDec x2 y2
  LtNo  : (x2 : Natt) -> (y2 : Natt) -> (leq y2 x2 = T) -> LtDec x2 y2

ltDec : (x : Natt) -> (y : Natt) -> LtDec x y
ltDec x Z = LtNo x Z Refl
ltDec Z (S y0) = LtYes Z (S y0) Refl
ltDec (S x0) (S y0) = case ltDec x0 y0 of
  LtYes _ _ e => LtYes (S x0) (S y0) e
  LtNo _ _ e  => LtNo (S x0) (S y0) e

divFuelOk : (a : Natt) -> (b0 : Natt) -> (f : Natt) -> leq a (S f) = T -> leq (S b0) a = T -> leq (monus a (S b0)) f = T
divFuelOk a b0 f hf hge = leTrans (S (monus a (S b0))) a (S f) (monusLt a b0 hge) hf

data DivResult : (a : Natt) -> (b0 : Natt) -> Type where
  MkRes : (q : Natt) -> (r : Natt) -> (a2 : Natt) -> (b02 : Natt) -> (plus (times q (S b02)) r = a2) -> (leq (S r) (S b02) = T) -> DivResult a2 b02

dm : (fuel : Natt) -> (a : Natt) -> (b0 : Natt) -> leq a fuel = T -> DivResult a b0
dmPick : (f : Natt) -> (a : Natt) -> (b0 : Natt) -> leq a (S f) = T -> LtDec a (S b0) -> DivResult a b0
dmPick f a b0 hf (LtYes _ _ e) = MkRes Z a a b0 Refl e
dmPick f a b0 hf (LtNo _ _ e) = case dm f (monus a (S b0)) b0 (divFuelOk a b0 f hf e) of
  MkRes q r _ _ eid erem => MkRes (S q) r a b0 (trans (plusAssoc (S b0) (times q (S b0)) r) (trans (plusCongR (S b0) (plus (times q (S b0)) r) (monus a (S b0)) eid) (plusMonus (S b0) a e))) erem
dm Z Z b0 hf = MkRes Z Z Z b0 Refl Refl
dm Z (S a0) b0 hf = case hf of Refl impossible
dm (S f) a b0 hf = dmPick f a b0 hf (ltDec a (S b0))

divmod : (a : Natt) -> (b0 : Natt) -> DivResult a b0
divmod a b0 = dm a a b0 (leqRefl a)
