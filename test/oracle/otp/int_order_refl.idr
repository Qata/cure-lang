-- Idris oracle mirror for int_order_refl.cure (rel=same). Reproduces the
-- reflected-form Int order family (So (leInt a b)) and the reflexivity
-- derivation on a local Int'/Nat'. Both sides accept.
import Data.So

%default total

data Nat' = Z | S Nat'
data Int' = FromNat Nat' | NegativeSuccessor Nat'

leNat : Nat' -> Nat' -> Bool
leNat Z _ = True
leNat (S _) Z = False
leNat (S m) (S n) = leNat m n

leInt : Int' -> Int' -> Bool
leInt (FromNat m) (FromNat n) = leNat m n
leInt (FromNat _) (NegativeSuccessor _) = False
leInt (NegativeSuccessor _) (FromNat _) = True
leInt (NegativeSuccessor k) (NegativeSuccessor j) = leNat j k

data IsLessThanOrEqual : Int' -> Int' -> Type where
  AtMost : So (leInt l r) -> IsLessThanOrEqual l r

leNatIsReflexive : (v : Nat') -> So (leNat v v)
leNatIsReflexive Z = Oh
leNatIsReflexive (S k) = leNatIsReflexive k

leIntFromNatIsReflexive : (n : Nat') -> So (leInt (FromNat n) (FromNat n))
leIntFromNatIsReflexive n = leNatIsReflexive n

leIntNegSuccIsReflexive : (k : Nat') -> So (leInt (NegativeSuccessor k) (NegativeSuccessor k))
leIntNegSuccIsReflexive k = leNatIsReflexive k

isLessThanOrEqualIsReflexive : (v : Int') -> IsLessThanOrEqual v v
isLessThanOrEqualIsReflexive (FromNat n) = AtMost (leIntFromNatIsReflexive n)
isLessThanOrEqualIsReflexive (NegativeSuccessor k) = AtMost (leIntNegSuccIsReflexive k)

twoAtMostTwo : IsLessThanOrEqual (FromNat (S (S Z))) (FromNat (S (S Z)))
twoAtMostTwo = isLessThanOrEqualIsReflexive (FromNat (S (S Z)))

negThreeAtMostNegThree : IsLessThanOrEqual (NegativeSuccessor (S (S Z))) (NegativeSuccessor (S (S Z)))
negThreeAtMostNegThree = isLessThanOrEqualIsReflexive (NegativeSuccessor (S (S Z)))

start : Bool
start = leInt (FromNat (S (S Z))) (FromNat (S (S Z)))
