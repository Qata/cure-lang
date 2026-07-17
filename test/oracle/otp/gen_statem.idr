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
plus_assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = a + (b + c)
plus_assoc Z b c = Refl
plus_assoc (S k) b c = rewrite plus_assoc k b c in Refl
plus_cong_r : (a : Nat) -> x = y -> a + x = a + y
plus_cong_r a e = cong (\z => a + z) e
data SRun : SConfig -> SConfig -> Type where
  SRDone : SRun c c
  SRMore : SStep c1 c2 -> SRun c2 c3 -> SRun c1 c3
step_handles : SStep b a -> Nat
step_handles SHandle = S Z
step_handles SPostpone = Z
step_handles SRedeliver = Z
handle_count : SRun c1 c2 -> Nat
handle_count SRDone = Z
handle_count (SRMore s rest) = step_handles s + handle_count rest
srun_single : SStep c1 c2 -> SRun c1 c2
srun_single s = SRMore s SRDone
srun_trans : SRun c1 c2 -> SRun c2 c3 -> SRun c1 c3
srun_trans SRDone r2 = r2
srun_trans (SRMore s rest) r2 = SRMore s (srun_trans rest r2)
handle_count_trans : (r1 : SRun c1 c2) -> (r2 : SRun c2 c3) -> handle_count (srun_trans r1 r2) = handle_count r1 + handle_count r2
handle_count_trans SRDone r2 = Refl
handle_count_trans (SRMore s rest) r2 = trans (plus_cong_r (step_handles s) (handle_count_trans rest r2)) (sym (plus_assoc (step_handles s) (handle_count rest) (handle_count r2)))
