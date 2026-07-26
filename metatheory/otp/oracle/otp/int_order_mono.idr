-- Idris oracle mirror for int_order_mono.cure (rel=same). Reproduces the
-- reflected-form Int order family (So (leInt a b)), integer addition by
-- iterated succ/pred, transitivity, and add-monotonicity, then the same closed
-- instances (-1 <= 0 <= 2 => -1 <= 2; adding -2 to 0 <= 2 => -2 <= 0). Both accept.
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

succInt : Int' -> Int'
succInt (FromNat n) = FromNat (S n)
succInt (NegativeSuccessor Z) = FromNat Z
succInt (NegativeSuccessor (S kp)) = NegativeSuccessor kp

predInt : Int' -> Int'
predInt (FromNat Z) = NegativeSuccessor Z
predInt (FromNat (S np)) = FromNat np
predInt (NegativeSuccessor k) = NegativeSuccessor (S k)

addNatSucc : Nat' -> Int' -> Int'
addNatSucc Z x = x
addNatSucc (S cp) x = succInt (addNatSucc cp x)

addNatPred : Nat' -> Int' -> Int'
addNatPred Z x = x
addNatPred (S cp) x = predInt (addNatPred cp x)

addInt : Int' -> Int' -> Int'
addInt (FromNat m) x = addNatSucc m x
addInt (NegativeSuccessor k) x = addNatPred (S k) x

data IsLessThanOrEqual : Int' -> Int' -> Type where
  AtMost : So (leInt l r) -> IsLessThanOrEqual l r

leNatTransitive : (a : Nat') -> (b : Nat') -> (c : Nat') -> So (leNat a b) -> So (leNat b c) -> So (leNat a c)
leNatTransitive Z b c ab bc = Oh
leNatTransitive (S ap) Z c ab bc = soFalseElim ab
leNatTransitive (S ap) (S bp) Z ab bc = soFalseElim bc
leNatTransitive (S ap) (S bp) (S cp) ab bc = leNatTransitive ap bp cp ab bc

leIntTransitive : (a : Int') -> (b : Int') -> (c : Int') -> So (leInt a b) -> So (leInt b c) -> So (leInt a c)
leIntTransitive (FromNat x) (FromNat y) (FromNat z) ab bc = leNatTransitive x y z ab bc
leIntTransitive (FromNat x) (NegativeSuccessor w) (FromNat z) ab bc = soFalseElim ab
leIntTransitive (FromNat x) (FromNat y) (NegativeSuccessor z) ab bc = soFalseElim bc
leIntTransitive (FromNat x) (NegativeSuccessor w) (NegativeSuccessor z) ab bc = soFalseElim ab
leIntTransitive (NegativeSuccessor x) b (FromNat z) ab bc = Oh
leIntTransitive (NegativeSuccessor x) (FromNat y) (NegativeSuccessor z) ab bc = soFalseElim bc
leIntTransitive (NegativeSuccessor x) (NegativeSuccessor w) (NegativeSuccessor z) ab bc = leNatTransitive z w x bc ab

isLessThanOrEqualIsTransitive : (left : Int') -> (middle : Int') -> (right : Int') -> IsLessThanOrEqual left middle -> IsLessThanOrEqual middle right -> IsLessThanOrEqual left right
isLessThanOrEqualIsTransitive left middle right (AtMost lm) (AtMost mr) = AtMost (leIntTransitive left middle right lm mr)

succIntIsMonotone : (a : Int') -> (b : Int') -> So (leInt a b) -> So (leInt (succInt a) (succInt b))
succIntIsMonotone (FromNat x) (FromNat y) ab = ab
succIntIsMonotone (FromNat x) (NegativeSuccessor w) ab = soFalseElim ab
succIntIsMonotone (NegativeSuccessor Z) (FromNat y) ab = Oh
succIntIsMonotone (NegativeSuccessor (S xp)) (FromNat y) ab = Oh
succIntIsMonotone (NegativeSuccessor Z) (NegativeSuccessor Z) ab = Oh
succIntIsMonotone (NegativeSuccessor Z) (NegativeSuccessor (S wp)) ab = soFalseElim ab
succIntIsMonotone (NegativeSuccessor (S xp)) (NegativeSuccessor Z) ab = Oh
succIntIsMonotone (NegativeSuccessor (S xp)) (NegativeSuccessor (S wp)) ab = ab

predIntIsMonotone : (a : Int') -> (b : Int') -> So (leInt a b) -> So (leInt (predInt a) (predInt b))
predIntIsMonotone (FromNat Z) (FromNat Z) ab = Oh
predIntIsMonotone (FromNat Z) (FromNat (S yp)) ab = Oh
predIntIsMonotone (FromNat (S xp)) (FromNat Z) ab = soFalseElim ab
predIntIsMonotone (FromNat (S xp)) (FromNat (S yp)) ab = ab
predIntIsMonotone (FromNat x) (NegativeSuccessor w) ab = soFalseElim ab
predIntIsMonotone (NegativeSuccessor x) (FromNat Z) ab = Oh
predIntIsMonotone (NegativeSuccessor x) (FromNat (S yp)) ab = Oh
predIntIsMonotone (NegativeSuccessor x) (NegativeSuccessor w) ab = ab

addNatSuccIsMonotone : (count : Nat') -> (a : Int') -> (b : Int') -> So (leInt a b) -> So (leInt (addNatSucc count a) (addNatSucc count b))
addNatSuccIsMonotone Z a b ab = ab
addNatSuccIsMonotone (S cp) a b ab = succIntIsMonotone (addNatSucc cp a) (addNatSucc cp b) (addNatSuccIsMonotone cp a b ab)

addNatPredIsMonotone : (count : Nat') -> (a : Int') -> (b : Int') -> So (leInt a b) -> So (leInt (addNatPred count a) (addNatPred count b))
addNatPredIsMonotone Z a b ab = ab
addNatPredIsMonotone (S cp) a b ab = predIntIsMonotone (addNatPred cp a) (addNatPred cp b) (addNatPredIsMonotone cp a b ab)

addIntIsMonotone : (addend : Int') -> (a : Int') -> (b : Int') -> So (leInt a b) -> So (leInt (addInt addend a) (addInt addend b))
addIntIsMonotone (FromNat m) a b ab = addNatSuccIsMonotone m a b ab
addIntIsMonotone (NegativeSuccessor k) a b ab = addNatPredIsMonotone (S k) a b ab

addingTheSameNumberPreservesLessThanOrEqual : (addend : Int') -> (left : Int') -> (right : Int') -> IsLessThanOrEqual left right -> IsLessThanOrEqual (addInt addend left) (addInt addend right)
addingTheSameNumberPreservesLessThanOrEqual addend left right (AtMost e) = AtMost (addIntIsMonotone addend left right e)

negOneAtMostZero : IsLessThanOrEqual (NegativeSuccessor Z) (FromNat Z)
negOneAtMostZero = AtMost Oh

zeroAtMostTwo : IsLessThanOrEqual (FromNat Z) (FromNat (S (S Z)))
zeroAtMostTwo = AtMost Oh

negOneAtMostTwo : IsLessThanOrEqual (NegativeSuccessor Z) (FromNat (S (S Z)))
negOneAtMostTwo = isLessThanOrEqualIsTransitive (NegativeSuccessor Z) (FromNat Z) (FromNat (S (S Z))) negOneAtMostZero zeroAtMostTwo

negTwoAtMostZero : IsLessThanOrEqual (addInt (NegativeSuccessor (S Z)) (FromNat Z)) (addInt (NegativeSuccessor (S Z)) (FromNat (S (S Z))))
negTwoAtMostZero = addingTheSameNumberPreservesLessThanOrEqual (NegativeSuccessor (S Z)) (FromNat Z) (FromNat (S (S Z))) zeroAtMostTwo

start : Bool
start = leInt (addInt (NegativeSuccessor (S Z)) (FromNat Z)) (addInt (NegativeSuccessor (S Z)) (FromNat (S (S Z))))
