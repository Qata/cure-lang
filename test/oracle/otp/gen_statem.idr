%default total

plus_n_z : (n : Nat) -> n + 0 = n
plus_n_z 0 = Refl
plus_n_z (S k) = rewrite plus_n_z k in Refl

plus_n_s : (m : Nat) -> (n : Nat) -> m + (S n) = S (m + n)
plus_n_s 0 n = Refl
plus_n_s (S k) n = rewrite plus_n_s k n in Refl

plus_comm : (m : Nat) -> (n : Nat) -> m + n = n + m
plus_comm 0 n = rewrite plus_n_z n in Refl
plus_comm (S k) n = rewrite plus_n_s n k in rewrite plus_comm k n in Refl

data SConfig = MkSC Nat Nat

unproc : SConfig -> Nat
unproc (MkSC p q) = p + q

data SStep : SConfig -> SConfig -> Type where
  SHandle : SStep (MkSC (S p) q) (MkSC p q)
  SPostpone : SStep (MkSC (S p) q) (MkSC p (S q))
  SRedeliver : SStep (MkSC p q) (MkSC (q + p) 0)

handle_progresses : (p : Nat) -> (q : Nat) -> unproc (MkSC (S p) q) = S (unproc (MkSC p q))
handle_progresses p q = Refl

postpone_conserves : (p : Nat) -> (q : Nat) -> unproc (MkSC (S p) q) = unproc (MkSC p (S q))
postpone_conserves p q = rewrite plus_n_s p q in Refl

redeliver_conserves : (p : Nat) -> (q : Nat) -> unproc (MkSC p q) = unproc (MkSC (q + p) 0)
redeliver_conserves p q = rewrite plus_n_z (q + p) in plus_comm p q
