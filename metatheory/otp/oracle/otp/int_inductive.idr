-- Idris oracle mirror for int_inductive.cure (rel=same). The Cure side uses
-- the real Std.Int.negate; this reproduces the same algorithm on a local Int'.
%default total

data Nat' = Z | S Nat'
data Int' = FromNat Nat' | NegativeSuccessor Nat'

negate' : Int' -> Int'
negate' (FromNat Z)     = FromNat Z
negate' (FromNat (S k)) = NegativeSuccessor k
negate' (NegativeSuccessor k) = FromNat (S k)

magnitude : Int' -> Nat'
magnitude (FromNat n) = n
magnitude (NegativeSuccessor n) = S n

start : Nat'
start = magnitude (negate' (FromNat (S (S Z))))
