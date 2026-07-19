%default total

data Nat' = Z | S Nat'
data Bool' = F | T
data Event = Acquire | Release

leq : Nat' -> Nat' -> Bool'
leq Z b = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

step : Nat' -> Event -> Nat'
step n Acquire = case n of
  Z => S Z
  S k => S k
step n Release = case n of
  Z => Z
  S k => k

inv : Nat' -> Bool'
inv n = leq n (S Z)

inv_step : (n : Nat') -> (e : Event) -> inv n = T -> inv (step n e) = T
inv_step Z Acquire h = Refl
inv_step (S k) Acquire h = h
inv_step Z Release h = Refl
inv_step (S Z) Release h = Refl
inv_step (S (S j)) Release Refl impossible

data Run : Nat' -> Nat' -> Type where
  RDone : Run s s
  RStep : (e : Event) -> Run (step s e) s2 -> Run s s2

inv_reachable : (s : Nat') -> inv s = T -> Run s s2 -> inv s2 = T
inv_reachable s h RDone = h
inv_reachable s h (RStep e run2) = inv_reachable (step s e) (inv_step s e h) run2

mutex_safe : Run Z s2 -> inv s2 = T
mutex_safe run = inv_reachable Z Refl run
