%default total

data Tag = TA | TB | TC

plus_n_z : (n : Nat) -> n + 0 = n
plus_n_z 0 = Refl
plus_n_z (S k) = rewrite plus_n_z k in Refl

plus_n_s : (m : Nat) -> (n : Nat) -> m + (S n) = S (m + n)
plus_n_s 0 n = Refl
plus_n_s (S k) n = rewrite plus_n_s k n in Refl

plus_comm : (m : Nat) -> (n : Nat) -> m + n = n + m
plus_comm 0 n = rewrite plus_n_z n in Refl
plus_comm (S k) n = rewrite plus_n_s n k in rewrite plus_comm k n in Refl

plus_assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = a + (b + c)
plus_assoc 0 b c = Refl
plus_assoc (S k) b c = rewrite plus_assoc k b c in Refl

data MS = MkMS Nat Nat Nat

msadd : MS -> MS -> MS
msadd (MkMS a b c) (MkMS d e f) = MkMS (a + d) (b + e) (c + f)

msadd_comm : (x : MS) -> (y : MS) -> msadd x y = msadd y x
msadd_comm (MkMS a b c) (MkMS d e f) =
  rewrite plus_comm a d in
  rewrite plus_comm b e in
  rewrite plus_comm c f in Refl

msadd_assoc : (x : MS) -> (y : MS) -> (z : MS) -> msadd (msadd x y) z = msadd x (msadd y z)
msadd_assoc (MkMS a b c) (MkMS d e f) (MkMS g h i) =
  rewrite plus_assoc a d g in rewrite plus_assoc b e h in rewrite plus_assoc c f i in Refl

msadd_zero_left : (y : MS) -> msadd (MkMS 0 0 0) y = y
msadd_zero_left (MkMS d e f) = Refl

data Pat = PZero | POne | PAtom Tag | PPlus Pat Pat | PTimes Pat Pat | PStar Pat

data Accepts : Pat -> MS -> Type where
  AOne   : Accepts POne (MkMS 0 0 0)
  AAtomA : Accepts (PAtom TA) (MkMS 1 0 0)
  AAtomB : Accepts (PAtom TB) (MkMS 0 1 0)
  AAtomC : Accepts (PAtom TC) (MkMS 0 0 1)
  APlusL : Accepts e m -> Accepts (PPlus e f) m
  APlusR : Accepts f m -> Accepts (PPlus e f) m
  ATimes : (m1 : MS) -> (m2 : MS) -> Accepts e m1 -> Accepts f m2 -> Accepts (PTimes e f) (msadd m1 m2)
  AStar0 : Accepts (PStar e) (MkMS 0 0 0)
  AStarN : (m1 : MS) -> (m2 : MS) -> Accepts e m1 -> Accepts (PStar e) m2 -> Accepts (PStar e) (msadd m1 m2)

plus_pat_comm : Accepts (PPlus e f) m -> Accepts (PPlus f e) m
plus_pat_comm (APlusL ae) = APlusR ae
plus_pat_comm (APlusR af) = APlusL af

times_comm : Accepts (PTimes e f) m -> Accepts (PTimes f e) m
times_comm (ATimes m1 m2 ae af) = rewrite msadd_comm m1 m2 in ATimes m2 m1 af ae

times_assoc : Accepts (PTimes (PTimes e f) g) m -> Accepts (PTimes e (PTimes f g)) m
times_assoc (ATimes _ mg (ATimes me mf acc_e acc_f) acc_g) =
  rewrite msadd_assoc me mf mg in ATimes me (msadd mf mg) acc_e (ATimes mf mg acc_f acc_g)

one_times : Accepts (PTimes POne e) m -> Accepts e m
one_times (ATimes _ m2 AOne ae) = rewrite msadd_zero_left m2 in ae
