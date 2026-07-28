-- Idris oracle mirror for int_order_sign.cure (rel=same). Reproduces the
-- reflected-form Int order family (So (leInt a b)), natural-number
-- multiplication, the Boolean le_nat monotonicity chain (weakening, two-sided
-- addition, scaling), the sign lemma 0 <= n, the 0 <= -1 refutation, and
-- nonnegative-scaling monotonicity, then the same closed instances (0 <= 3;
-- scaling 1 <= 2 by 2 => 2 <= 4). Both accept.
import Data.So

%default total

data Nat' = Z | S Nat'
data Int' = FromNat Nat' | NegativeSuccessor Nat'

soFalseElim : So False -> a
soFalseElim x = absurd x

leNat : Nat' -> Nat' -> Bool
leNat Z _ = True
leNat (S _) Z = False
leNat (S m) (S n) = leNat m n

leInt : Int' -> Int' -> Bool
leInt (FromNat m) (FromNat n) = leNat m n
leInt (FromNat _) (NegativeSuccessor _) = False
leInt (NegativeSuccessor _) (FromNat _) = True
leInt (NegativeSuccessor k) (NegativeSuccessor j) = leNat j k

plus : Nat' -> Nat' -> Nat'
plus Z n = n
plus (S k) n = S (plus k n)

multiply : Nat' -> Nat' -> Nat'
multiply Z _ = Z
multiply (S p) r = plus r (multiply p r)

data IsLessThanOrEqual : Int' -> Int' -> Type where
  AtMost : So (leInt l r) -> IsLessThanOrEqual l r

leNatIsReflexive : (n : Nat') -> So (leNat n n)
leNatIsReflexive Z = Oh
leNatIsReflexive (S k) = leNatIsReflexive k

leNatTransitive : (a : Nat') -> (b : Nat') -> (c : Nat') -> So (leNat a b) -> So (leNat b c) -> So (leNat a c)
leNatTransitive Z b c ab bc = Oh
leNatTransitive (S ap) Z c ab bc = soFalseElim ab
leNatTransitive (S ap) (S bp) Z ab bc = soFalseElim bc
leNatTransitive (S ap) (S bp) (S cp) ab bc = leNatTransitive ap bp cp ab bc

leNatWeakenRight : (smaller : Nat') -> (larger : Nat') -> So (leNat smaller larger) -> So (leNat smaller (S larger))
leNatWeakenRight Z larger ev = Oh
leNatWeakenRight (S sp) Z ev = soFalseElim ev
leNatWeakenRight (S sp) (S lp) ev = leNatWeakenRight sp lp ev

leNatAddLeftWeakens : (base : Nat') -> (addend : Nat') -> So (leNat base (plus addend base))
leNatAddLeftWeakens base Z = leNatIsReflexive base
leNatAddLeftWeakens base (S ap) = leNatWeakenRight base (plus ap base) (leNatAddLeftWeakens base ap)

leNatPlusIsMonotoneLeft : (a : Nat') -> (b : Nat') -> (y : Nat') -> So (leNat a b) -> So (leNat (plus a y) (plus b y))
leNatPlusIsMonotoneLeft Z b y ab = leNatAddLeftWeakens y b
leNatPlusIsMonotoneLeft (S ap) Z y ab = soFalseElim ab
leNatPlusIsMonotoneLeft (S ap) (S bp) y ab = leNatPlusIsMonotoneLeft ap bp y ab

leNatPlusIsMonotoneRight : (a : Nat') -> (x : Nat') -> (y : Nat') -> So (leNat x y) -> So (leNat (plus a x) (plus a y))
leNatPlusIsMonotoneRight Z x y xy = xy
leNatPlusIsMonotoneRight (S ap) x y xy = leNatPlusIsMonotoneRight ap x y xy

leNatPlusIsMonotone : (a : Nat') -> (b : Nat') -> (x : Nat') -> (y : Nat') -> So (leNat a b) -> So (leNat x y) -> So (leNat (plus a x) (plus b y))
leNatPlusIsMonotone a b x y ab xy =
  leNatTransitive (plus a x) (plus a y) (plus b y)
    (leNatPlusIsMonotoneRight a x y xy)
    (leNatPlusIsMonotoneLeft a b y ab)

leNatMultiplyIsMonotone : (scalar : Nat') -> (left : Nat') -> (right : Nat') -> So (leNat left right) -> So (leNat (multiply scalar left) (multiply scalar right))
leNatMultiplyIsMonotone Z left right lr = Oh
leNatMultiplyIsMonotone (S sp) left right lr =
  leNatPlusIsMonotone left right (multiply sp left) (multiply sp right) lr
    (leNatMultiplyIsMonotone sp left right lr)

fromNatLeEvidence : (l : Nat') -> (r : Nat') -> So (leNat l r) -> So (leInt (FromNat l) (FromNat r))
fromNatLeEvidence l r ev = ev

nonnegOfFromNat : (n : Nat') -> IsLessThanOrEqual (FromNat Z) (FromNat n)
nonnegOfFromNat n = AtMost Oh

zeroIsNotAtMostNegativeOne : IsLessThanOrEqual (FromNat Z) (NegativeSuccessor Z) -> Void
zeroIsNotAtMostNegativeOne (AtMost ev) = soFalseElim ev

scalingByNonnegPreservesLessThanOrEqual : (scalar : Nat') -> (left : Nat') -> (right : Nat') -> IsLessThanOrEqual (FromNat left) (FromNat right) -> IsLessThanOrEqual (FromNat (multiply scalar left)) (FromNat (multiply scalar right))
scalingByNonnegPreservesLessThanOrEqual scalar left right (AtMost ev) =
  AtMost (fromNatLeEvidence (multiply scalar left) (multiply scalar right)
    (leNatMultiplyIsMonotone scalar left right ev))

zeroAtMostThree : IsLessThanOrEqual (FromNat Z) (FromNat (S (S (S Z))))
zeroAtMostThree = nonnegOfFromNat (S (S (S Z)))

oneAtMostTwo : IsLessThanOrEqual (FromNat (S Z)) (FromNat (S (S Z)))
oneAtMostTwo = AtMost Oh

twoAtMostFour : IsLessThanOrEqual (FromNat (S (S Z))) (FromNat (S (S (S (S Z)))))
twoAtMostFour = scalingByNonnegPreservesLessThanOrEqual (S (S Z)) (S Z) (S (S Z)) oneAtMostTwo

start : Bool
start = leInt (FromNat (S (S Z))) (FromNat (S (S (S (S Z)))))
