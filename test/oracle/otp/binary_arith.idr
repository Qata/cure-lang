%default total

-- VERIFIED BINARY ARITHMETIC. Naturals represented as bit lists (LSB first); toNat denotes them. Proved: the
-- representation is FAITHFUL -- increment is correct (toNat (inc b) = S (toNat b)) and every natural
-- round-trips (toNat (fromNat n) = n) -- and RIPPLE-CARRY ADDITION computes the right value (toNat (add a b)
-- = toNat a + toNat b), via a full-adder correctness lemma (sum + 2*carry = c + x + y) and plus/double algebra.

data Natt = Z | S Natt

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

snatCong : (a : Natt) -> (b : Natt) -> a = b -> S a = S b
snatCong a b e = cong S e

plusZero : (n : Natt) -> plus n Z = n
plusZero Z = Refl
plusZero (S k) = cong S (plusZero k)

plusSuccR : (a : Natt) -> (b : Natt) -> plus a (S b) = S (plus a b)
plusSuccR Z b = Refl
plusSuccR (S k) b = cong S (plusSuccR k b)

plusAssoc : (a : Natt) -> (b : Natt) -> (c : Natt) -> plus (plus a b) c = plus a (plus b c)
plusAssoc Z b c = Refl
plusAssoc (S k) b c = cong S (plusAssoc k b c)

plusComm : (a : Natt) -> (b : Natt) -> plus a b = plus b a
plusComm Z b = sym (plusZero b)
plusComm (S k) b = trans (cong S (plusComm k b)) (sym (plusSuccR b k))

plusCongR : (a : Natt) -> (b : Natt) -> (c : Natt) -> b = c -> plus a b = plus a c
plusCongR a b c e = cong (plus a) e

plusCongL : (a : Natt) -> (b : Natt) -> (c : Natt) -> a = b -> plus a c = plus b c
plusCongL a b c e = cong (\w => plus w c) e

plusCong2 : (a : Natt) -> (ap : Natt) -> (b : Natt) -> (bp : Natt) -> a = ap -> b = bp -> plus a b = plus ap bp
plusCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

rearrange4 : (w : Natt) -> (x : Natt) -> (y : Natt) -> (z : Natt) -> plus (plus w x) (plus y z) = plus (plus w y) (plus x z)
rearrange4 w x y z =
  trans (plusAssoc w x (plus y z))
    (trans (plusCongR w (plus x (plus y z)) (plus (plus x y) z) (sym (plusAssoc x y z)))
      (trans (plusCongR w (plus (plus x y) z) (plus (plus y x) z) (plusCongL (plus x y) (plus y x) z (plusComm x y)))
        (trans (plusCongR w (plus (plus y x) z) (plus y (plus x z)) (plusAssoc y x z))
          (sym (plusAssoc w y (plus x z))))))

double : Natt -> Natt
double Z = Z
double (S k) = S (S (double k))

doubleCong : (m : Natt) -> (n : Natt) -> m = n -> double m = double n
doubleCong m n e = cong double e

doublePlus : (p : Natt) -> (q : Natt) -> double (plus p q) = plus (double p) (double q)
doublePlus Z q = Refl
doublePlus (S k) q = cong S (cong S (doublePlus k q))

data Bit = O | I
data Bin = BNil | BCons Bit Bin

bitNat : Bit -> Natt
bitNat O = Z
bitNat I = S Z

toNat : Bin -> Natt
toNat BNil = Z
toNat (BCons O r) = double (toNat r)
toNat (BCons I r) = S (double (toNat r))

toNatBcons : (bit : Bit) -> (r : Bin) -> toNat (BCons bit r) = plus (bitNat bit) (double (toNat r))
toNatBcons O r = Refl
toNatBcons I r = Refl

inc : Bin -> Bin
inc BNil = BCons I BNil
inc (BCons O r) = BCons I r
inc (BCons I r) = BCons O (inc r)

incCorrect : (b : Bin) -> toNat (inc b) = S (toNat b)
incCorrect BNil = Refl
incCorrect (BCons O r) = Refl
incCorrect (BCons I r) = doubleCong (toNat (inc r)) (S (toNat r)) (incCorrect r)

fromNat : Natt -> Bin
fromNat Z = BNil
fromNat (S k) = inc (fromNat k)

fromNatCorrect : (n : Natt) -> toNat (fromNat n) = n
fromNatCorrect Z = Refl
fromNatCorrect (S k) = trans (incCorrect (fromNat k)) (snatCong (toNat (fromNat k)) k (fromNatCorrect k))

badd : Bit -> Bit -> Bit -> Bit
badd O O O = O
badd O O I = I
badd O I O = I
badd O I I = O
badd I O O = I
badd I O I = O
badd I I O = O
badd I I I = I

bcarry : Bit -> Bit -> Bit -> Bit
bcarry O O O = O
bcarry O O I = O
bcarry O I O = O
bcarry O I I = I
bcarry I O O = O
bcarry I O I = I
bcarry I I O = I
bcarry I I I = I

fa : (c : Bit) -> (x : Bit) -> (y : Bit) -> plus (bitNat (badd c x y)) (double (bitNat (bcarry c x y))) = plus (bitNat c) (plus (bitNat x) (bitNat y))
fa O O O = Refl
fa O O I = Refl
fa O I O = Refl
fa O I I = Refl
fa I O O = Refl
fa I O I = Refl
fa I I O = Refl
fa I I I = Refl

incIf : Bit -> Bin -> Bin
incIf O b = b
incIf I b = inc b

incIfCorrect : (c : Bit) -> (b : Bin) -> toNat (incIf c b) = plus (bitNat c) (toNat b)
incIfCorrect O b = Refl
incIfCorrect I b = incCorrect b

addc : Bit -> Bin -> Bin -> Bin
addc c BNil b = incIf c b
addc c (BCons x a2) BNil = incIf c (BCons x a2)
addc c (BCons x a2) (BCons y b2) = BCons (badd c x y) (addc (bcarry c x y) a2 b2)

addcCorrect : (c : Bit) -> (a : Bin) -> (b : Bin) -> toNat (addc c a b) = plus (bitNat c) (plus (toNat a) (toNat b))
addcCorrect c BNil b = incIfCorrect c b
addcCorrect c (BCons x a2) BNil = trans (incIfCorrect c (BCons x a2)) (plusCongR (bitNat c) (toNat (BCons x a2)) (plus (toNat (BCons x a2)) Z) (sym (plusZero (toNat (BCons x a2)))))
addcCorrect c (BCons x a2) (BCons y b2) =
  trans (toNatBcons (badd c x y) (addc (bcarry c x y) a2 b2))
    (trans (plusCongR (bitNat (badd c x y)) (double (toNat (addc (bcarry c x y) a2 b2))) (double (plus (bitNat (bcarry c x y)) (plus (toNat a2) (toNat b2)))) (doubleCong (toNat (addc (bcarry c x y) a2 b2)) (plus (bitNat (bcarry c x y)) (plus (toNat a2) (toNat b2))) (addcCorrect (bcarry c x y) a2 b2)))
      (trans (plusCongR (bitNat (badd c x y)) (double (plus (bitNat (bcarry c x y)) (plus (toNat a2) (toNat b2)))) (plus (double (bitNat (bcarry c x y))) (double (plus (toNat a2) (toNat b2)))) (doublePlus (bitNat (bcarry c x y)) (plus (toNat a2) (toNat b2))))
        (trans (plusCongR (bitNat (badd c x y)) (plus (double (bitNat (bcarry c x y))) (double (plus (toNat a2) (toNat b2)))) (plus (double (bitNat (bcarry c x y))) (plus (double (toNat a2)) (double (toNat b2)))) (plusCongR (double (bitNat (bcarry c x y))) (double (plus (toNat a2) (toNat b2))) (plus (double (toNat a2)) (double (toNat b2))) (doublePlus (toNat a2) (toNat b2))))
          (trans (sym (plusAssoc (bitNat (badd c x y)) (double (bitNat (bcarry c x y))) (plus (double (toNat a2)) (double (toNat b2)))))
            (trans (plusCongL (plus (bitNat (badd c x y)) (double (bitNat (bcarry c x y)))) (plus (bitNat c) (plus (bitNat x) (bitNat y))) (plus (double (toNat a2)) (double (toNat b2))) (fa c x y))
              (trans (plusAssoc (bitNat c) (plus (bitNat x) (bitNat y)) (plus (double (toNat a2)) (double (toNat b2))))
                (trans (plusCongR (bitNat c) (plus (plus (bitNat x) (bitNat y)) (plus (double (toNat a2)) (double (toNat b2)))) (plus (plus (bitNat x) (double (toNat a2))) (plus (bitNat y) (double (toNat b2)))) (rearrange4 (bitNat x) (bitNat y) (double (toNat a2)) (double (toNat b2))))
                  (plusCongR (bitNat c) (plus (plus (bitNat x) (double (toNat a2))) (plus (bitNat y) (double (toNat b2)))) (plus (toNat (BCons x a2)) (toNat (BCons y b2))) (plusCong2 (plus (bitNat x) (double (toNat a2))) (toNat (BCons x a2)) (plus (bitNat y) (double (toNat b2))) (toNat (BCons y b2)) (sym (toNatBcons x a2)) (sym (toNatBcons y b2)))))))))))

add : Bin -> Bin -> Bin
add a b = addc O a b

addCorrect : (a : Bin) -> (b : Bin) -> toNat (add a b) = plus (toNat a) (toNat b)
addCorrect a b = addcCorrect O a b
