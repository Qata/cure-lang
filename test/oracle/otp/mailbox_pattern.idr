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

data B = F | T

Uninhabited (F = T) where
  uninhabited Refl impossible

orb : B -> B -> B
orb F y = y
orb T y = T

andb : B -> B -> B
andb F y = F
andb T y = y

data BOr : B -> B -> Type where
  BOrL : x = T -> BOr x y
  BOrR : y = T -> BOr x y

orb_true : (x : B) -> (y : B) -> orb x y = T -> BOr x y
orb_true T y e = BOrL Refl
orb_true F T e = BOrR Refl
orb_true F F e = absurd e

data BAnd : B -> B -> Type where
  BAndBoth : x = T -> y = T -> BAnd x y

andb_true : (x : B) -> (y : B) -> andb x y = T -> BAnd x y
andb_true T T e = BAndBoth Refl Refl
andb_true T F e = absurd e
andb_true F y e = absurd e

nullable : Pat -> B
nullable PZero = F
nullable POne = T
nullable (PAtom t) = F
nullable (PPlus a b) = orb (nullable a) (nullable b)
nullable (PTimes a b) = andb (nullable a) (nullable b)
nullable (PStar a) = T

nullable_sound : (pat : Pat) -> nullable pat = T -> Accepts pat (MkMS 0 0 0)
nullable_sound PZero e = absurd e
nullable_sound POne e = AOne
nullable_sound (PAtom t) e = absurd e
nullable_sound (PPlus a b) e = case orb_true (nullable a) (nullable b) e of
  BOrL pa => APlusL (nullable_sound a pa)
  BOrR pb => APlusR (nullable_sound b pb)
nullable_sound (PTimes a b) e = case andb_true (nullable a) (nullable b) e of
  BAndBoth pa pb => ATimes (MkMS 0 0 0) (MkMS 0 0 0) (nullable_sound a pa) (nullable_sound b pb)
nullable_sound (PStar a) e = AStar0

singleton : Tag -> MS
singleton TA = MkMS 1 0 0
singleton TB = MkMS 0 1 0
singleton TC = MkMS 0 0 1

deriv : Pat -> Tag -> Pat
deriv PZero t = PZero
deriv POne t = PZero
deriv (PAtom TA) TA = POne
deriv (PAtom TA) TB = PZero
deriv (PAtom TA) TC = PZero
deriv (PAtom TB) TA = PZero
deriv (PAtom TB) TB = POne
deriv (PAtom TB) TC = PZero
deriv (PAtom TC) TA = PZero
deriv (PAtom TC) TB = PZero
deriv (PAtom TC) TC = POne
deriv (PPlus a b) t = PPlus (deriv a t) (deriv b t)
deriv (PTimes a b) t = PPlus (PTimes (deriv a t) b) (PTimes a (deriv b t))
deriv (PStar a) t = PTimes (deriv a t) (PStar a)

ms_swap : (x : MS) -> (y : MS) -> (z : MS) -> msadd (msadd x y) z = msadd (msadd x z) y
ms_swap x y z =
  rewrite msadd_assoc x y z in
  rewrite msadd_comm y z in
  rewrite msadd_assoc x z y in Refl

mutual
  deriv_sound : (pat : Pat) -> (t : Tag) -> (m : MS) -> Accepts (deriv pat t) m -> Accepts pat (msadd m (singleton t))
  deriv_sound (PPlus a b) t m (APlusL da) = APlusL (deriv_sound a t m da)
  deriv_sound (PPlus a b) t m (APlusR db) = APlusR (deriv_sound b t m db)
  deriv_sound (PTimes a b) t _ (APlusL (ATimes m1 m2 da ab)) =
    rewrite ms_swap m1 m2 (singleton t) in ATimes (msadd m1 (singleton t)) m2 (deriv_sound a t m1 da) ab
  deriv_sound (PTimes a b) t _ (APlusR (ATimes m1 m2 aa db)) =
    rewrite msadd_assoc m1 m2 (singleton t) in ATimes m1 (msadd m2 (singleton t)) aa (deriv_sound b t m2 db)
  deriv_sound (PStar a) t _ (ATimes m1 m2 da as) =
    rewrite ms_swap m1 m2 (singleton t) in AStarN (msadd m1 (singleton t)) m2 (deriv_sound a t m1 da) as
  deriv_sound (PAtom TA) TA _ AOne = AAtomA
  deriv_sound (PAtom TB) TB _ AOne = AAtomB
  deriv_sound (PAtom TC) TC _ AOne = AAtomC

star_unfold : Accepts (PStar a) m -> Accepts (PPlus POne (PTimes a (PStar a))) m
star_unfold AStar0 = APlusL AOne
star_unfold (AStarN m1 m2 ae as) = APlusR (ATimes m1 m2 ae as)

star_fold : Accepts (PPlus POne (PTimes a (PStar a))) m -> Accepts (PStar a) m
star_fold (APlusL AOne) = AStar0
star_fold (APlusR (ATimes m1 m2 ae as)) = AStarN m1 m2 ae as

dist_fwd : Accepts (PTimes a (PPlus b c)) m -> Accepts (PPlus (PTimes a b) (PTimes a c)) m
dist_fwd (ATimes m1 m2 aa (APlusL ab)) = APlusL (ATimes m1 m2 aa ab)
dist_fwd (ATimes m1 m2 aa (APlusR ac)) = APlusR (ATimes m1 m2 aa ac)

dist_bwd : Accepts (PPlus (PTimes a b) (PTimes a c)) m -> Accepts (PTimes a (PPlus b c)) m
dist_bwd (APlusL (ATimes m1 m2 aa ab)) = ATimes m1 m2 aa (APlusL ab)
dist_bwd (APlusR (ATimes m1 m2 aa ac)) = ATimes m1 m2 aa (APlusR ac)
