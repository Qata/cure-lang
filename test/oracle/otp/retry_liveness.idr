%default total

data Nat' = Z | S Nat'
data Bool' = F | T
data State = Retry Nat' | Done | GaveUp

leq : Nat' -> Nat' -> Bool'
leq Z b = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leq_refl : (a : Nat') -> leq a a = T
leq_refl Z = Refl
leq_refl (S k) = leq_refl k

lt : Nat' -> Nat' -> Bool'
lt a Z = F
lt a (S j) = leq a j

is_terminal : State -> Bool'
is_terminal (Retry n) = F
is_terminal Done = T
is_terminal GaveUp = T

step : State -> State
step (Retry Z) = GaveUp
step (Retry (S k)) = Retry k
step Done = Done
step GaveUp = GaveUp

measure : State -> Nat'
measure (Retry n) = S n
measure Done = Z
measure GaveUp = Z

measure_decreases : (s : State) -> is_terminal s = F -> lt (measure (step s)) (measure s) = T
measure_decreases (Retry Z) h = Refl
measure_decreases (Retry (S k)) h = leq_refl (S k)
measure_decreases Done Refl impossible
measure_decreases GaveUp Refl impossible

run : State -> Nat' -> State
run s Z = s
run s (S m) = run (step s) m

reaches_terminal : (n : Nat') -> is_terminal (run (Retry n) (measure (Retry n))) = T
reaches_terminal Z = Refl
reaches_terminal (S k) = reaches_terminal k
