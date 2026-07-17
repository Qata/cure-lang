%default total

trans' : {0 a, b, c : t} -> a = b -> b = c -> a = c
trans' e1 e2 = rewrite e1 in e2

data Config = MkConfig Nat Nat

data LStep : Config -> Config -> Type where
  LAnswer : (p : Nat) -> (a : Nat) -> LStep (MkConfig (S p) a) (MkConfig p (S a))

total_ : Config -> Nat
total_ (MkConfig p a) = plus p a

plus_succ_right : (m : Nat) -> (n : Nat) -> plus m (S n) = S (plus m n)
plus_succ_right Z n = Refl
plus_succ_right (S k) n = cong S (plus_succ_right k n)

plus_zero_right : (m : Nat) -> plus m Z = m
plus_zero_right Z = Refl
plus_zero_right (S k) = cong S (plus_zero_right k)

step_conserves : (p : Nat) -> (a : Nat) -> LStep (MkConfig (S p) a) (MkConfig p (S a)) ->
                 total_ (MkConfig (S p) a) = total_ (MkConfig p (S a))
step_conserves p a _ = rewrite plus_succ_right p a in Refl

data LStar : Config -> Config -> Type where
  LDone : LStar c c
  LThen : LStep x y -> LStar y z -> LStar x z

total_invariant : LStar b a2 -> total_ b = total_ a2
total_invariant LDone = Refl
total_invariant (LThen (LAnswer p a) rest) =
  trans' (step_conserves p a (LAnswer p a)) (total_invariant rest)

drain : (n : Nat) -> (m : Nat) -> LStar (MkConfig n Z) (MkConfig Z m) -> n = m
drain n m r = rewrite sym (plus_zero_right n) in total_invariant r

a_step : LStep (MkConfig (S Z) Z) (MkConfig Z (S Z))
a_step = LAnswer Z Z

no_answer_without_cap : LStep (MkConfig Z a) after -> Void
no_answer_without_cap (LAnswer _ _) impossible
