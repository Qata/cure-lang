-- Verified-LIA Task 1 mirror: structural natural scaling and signed integer
-- multiplication over the canonical FromNat/NegativeSuccessor presentation.
%default total

data Nat' = Z | S Nat'
data Int' = FromNat Nat' | NegativeSuccessor Nat'

succInt : Int' -> Int'
succInt (FromNat n) = FromNat (S n)
succInt (NegativeSuccessor Z) = FromNat Z
succInt (NegativeSuccessor (S k)) = NegativeSuccessor k

addNatSucc : Nat' -> Int' -> Int'
addNatSucc Z x = x
addNatSucc (S k) x = succInt (addNatSucc k x)

negateInt : Int' -> Int'
negateInt (FromNat Z) = FromNat Z
negateInt (FromNat (S n)) = NegativeSuccessor n
negateInt (NegativeSuccessor n) = FromNat (S n)

-- Mirror Cure's actual repeated integer addition directly, including negatives.
predInt : Int' -> Int'
predInt (FromNat Z) = NegativeSuccessor Z
predInt (FromNat (S n)) = FromNat n
predInt (NegativeSuccessor n) = NegativeSuccessor (S n)

addNatPred : Nat' -> Int' -> Int'
addNatPred Z x = x
addNatPred (S k) x = predInt (addNatPred k x)

addInt : Int' -> Int' -> Int'
addInt (FromNat n) x = addNatSucc n x
addInt (NegativeSuccessor n) x = addNatPred (S n) x

scaleNatInt : Nat' -> Int' -> Int'
scaleNatInt Z value = FromNat Z
scaleNatInt (S k) value = addInt value (scaleNatInt k value)

multiplyInt : Int' -> Int' -> Int'
multiplyInt (FromNat n) value = scaleNatInt n value
multiplyInt (NegativeSuccessor n) value = negateInt (scaleNatInt (S n) value)

zeroScaleNegative : scaleNatInt Z (NegativeSuccessor (S Z)) = FromNat Z
zeroScaleNegative = Refl

positiveScaleNegative : scaleNatInt (S (S Z)) (NegativeSuccessor Z) = NegativeSuccessor (S Z)
positiveScaleNegative = Refl

positiveTimesPositive : multiplyInt (FromNat (S (S Z))) (FromNat (S (S (S Z)))) = FromNat (S (S (S (S (S (S Z))))))
positiveTimesPositive = Refl

positiveTimesNegative : multiplyInt (FromNat (S (S Z))) (NegativeSuccessor Z) = NegativeSuccessor (S Z)
positiveTimesNegative = Refl

negativeTimesPositive : multiplyInt (NegativeSuccessor Z) (FromNat (S (S (S Z)))) = NegativeSuccessor (S (S Z))
negativeTimesPositive = Refl

negativeTimesNegative : multiplyInt (NegativeSuccessor Z) (NegativeSuccessor (S Z)) = FromNat (S (S Z))
negativeTimesNegative = Refl

start : Bool
start = True
