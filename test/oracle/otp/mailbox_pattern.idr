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

absurd_pzero : Accepts PZero m -> b
absurd_pzero AOne impossible

plus_assoc_fwd : Accepts (PPlus (PPlus a b) c) m -> Accepts (PPlus a (PPlus b c)) m
plus_assoc_fwd (APlusL (APlusL aa)) = APlusL aa
plus_assoc_fwd (APlusL (APlusR ab)) = APlusR (APlusL ab)
plus_assoc_fwd (APlusR ac) = APlusR (APlusR ac)

plus_assoc_bwd : Accepts (PPlus a (PPlus b c)) m -> Accepts (PPlus (PPlus a b) c) m
plus_assoc_bwd (APlusL aa) = APlusL (APlusL aa)
plus_assoc_bwd (APlusR (APlusL ab)) = APlusL (APlusR ab)
plus_assoc_bwd (APlusR (APlusR ac)) = APlusR ac

plus_zero_fwd : Accepts (PPlus a PZero) m -> Accepts a m
plus_zero_fwd (APlusL aa) = aa
plus_zero_fwd (APlusR az) = absurd_pzero az

zero_times : Accepts (PTimes PZero a) m -> Accepts PZero m
zero_times (ATimes m1 m2 az aa) = absurd_pzero az

plus_zero_bwd : Accepts a m -> Accepts (PPlus a PZero) m
plus_zero_bwd acc = APlusL acc

data Incl : Pat -> Pat -> Type where
  IRefl : Incl e e
  IZero : Incl PZero f
  IPlus : Incl e g -> Incl f g -> Incl (PPlus e f) g
  IInL : Incl e f -> Incl e (PPlus f g)
  IInR : Incl e g -> Incl e (PPlus f g)
  ITimes : Incl e1 e2 -> Incl f1 f2 -> Incl (PTimes e1 f1) (PTimes e2 f2)
  IStar : Incl e f -> Incl (PStar e) (PStar f)
  ITrans : Incl e f -> Incl f g -> Incl e g

mutual
  incl_times : Incl e1 e2 -> Incl f1 f2 -> Accepts (PTimes e1 f1) m -> Accepts (PTimes e2 f2) m
  incl_times s1 s2 (ATimes m1 m2 a1 a2) = ATimes m1 m2 (incl_sound s1 a1) (incl_sound s2 a2)
  incl_star : Incl e f -> Accepts (PStar e) m -> Accepts (PStar f) m
  incl_star s AStar0 = AStar0
  incl_star s (AStarN m1 m2 ae as) = AStarN m1 m2 (incl_sound s ae) (incl_star s as)
  incl_sound : Incl e f -> Accepts e m -> Accepts f m
  incl_sound IRefl acc = acc
  incl_sound IZero acc = absurd_pzero acc
  incl_sound (IPlus se sf) (APlusL ae) = incl_sound se ae
  incl_sound (IPlus se sf) (APlusR af) = incl_sound sf af
  incl_sound (IInL sef) acc = APlusL (incl_sound sef acc)
  incl_sound (IInR seg) acc = APlusR (incl_sound seg acc)
  incl_sound (ITimes s1 s2) acc = incl_times s1 s2 acc
  incl_sound (IStar s) acc = incl_star s acc
  incl_sound (ITrans sef sfg) acc = incl_sound sfg (incl_sound sef acc)

deriv_mono : (t : Tag) -> Incl e f -> Incl (deriv e t) (deriv f t)
deriv_mono t IRefl = IRefl
deriv_mono t IZero = IZero
deriv_mono t (IPlus se sf) = IPlus (deriv_mono t se) (deriv_mono t sf)
deriv_mono t (IInL sef) = IInL (deriv_mono t sef)
deriv_mono t (IInR seg) = IInR (deriv_mono t seg)
deriv_mono t (ITimes s1 s2) = IPlus (IInL (ITimes (deriv_mono t s1) s2)) (IInR (ITimes s1 (deriv_mono t s2)))
deriv_mono t (IStar s) = ITimes (deriv_mono t s) (IStar s)
deriv_mono t (ITrans sef sfg) = ITrans (deriv_mono t sef) (deriv_mono t sfg)

data Word = WNil | WCons Tag Word

parikh : Word -> MS
parikh WNil = MkMS 0 0 0
parikh (WCons t rest) = msadd (singleton t) (parikh rest)

dfold : Pat -> Word -> Pat
dfold e WNil = e
dfold e (WCons t rest) = dfold (deriv e t) rest

matches_word_sound : (e : Pat) -> (w : Word) -> (nullable (dfold e w) = T) -> Accepts e (parikh w)
matches_word_sound e WNil h = nullable_sound e h
matches_word_sound e (WCons t rest) h =
  rewrite msadd_comm (singleton t) (parikh rest) in deriv_sound e t (parikh rest) (matches_word_sound (deriv e t) rest h)

plus_zero_l : (a : Nat) -> (b : Nat) -> (a + b = 0) -> a = 0
plus_zero_l 0 b e = Refl
plus_zero_l (S k) b Refl impossible

plus_zero_r : (a : Nat) -> (b : Nat) -> (a + b = 0) -> b = 0
plus_zero_r 0 b e = e
plus_zero_r (S k) b Refl impossible

msa : MS -> Nat
msa (MkMS a b c) = a
msb : MS -> Nat
msb (MkMS a b c) = b
msc : MS -> Nat
msc (MkMS a b c) = c

msadd_zero_l : (x : MS) -> (y : MS) -> (msadd x y = MkMS 0 0 0) -> x = MkMS 0 0 0
msadd_zero_l (MkMS a b c) (MkMS d e f) prf =
  rewrite plus_zero_l a d (cong msa prf) in
  rewrite plus_zero_l b e (cong msb prf) in
  rewrite plus_zero_l c f (cong msc prf) in Refl

msadd_zero_r : (x : MS) -> (y : MS) -> (msadd x y = MkMS 0 0 0) -> y = MkMS 0 0 0
msadd_zero_r (MkMS a b c) (MkMS d e f) prf =
  rewrite plus_zero_r a d (cong msa prf) in
  rewrite plus_zero_r b e (cong msb prf) in
  rewrite plus_zero_r c f (cong msc prf) in Refl

orb_t_r : (x : B) -> orb x T = T
orb_t_r F = Refl
orb_t_r T = Refl

orb_r : (x : B) -> {y : B} -> (y = T) -> orb x y = T
orb_r x py = rewrite py in orb_t_r x

nc_gen : {pat : Pat} -> {m : MS} -> Accepts pat m -> (m = MkMS 0 0 0) -> nullable pat = T
nc_gen AOne q = Refl
nc_gen AAtomA Refl impossible
nc_gen AAtomB Refl impossible
nc_gen AAtomC Refl impossible
nc_gen (APlusL ae) q = rewrite nc_gen ae q in Refl
nc_gen (APlusR {e} af) q = orb_r (nullable e) (nc_gen af q)
nc_gen (ATimes m1 m2 ae af) q = rewrite nc_gen ae (msadd_zero_l m1 m2 q) in nc_gen af (msadd_zero_r m1 m2 q)
nc_gen AStar0 q = Refl
nc_gen (AStarN m1 m2 ae as) q = Refl

nullable_complete : (pat : Pat) -> Accepts pat (MkMS 0 0 0) -> nullable pat = T
nullable_complete pat acc = nc_gen acc Refl

s_inj : {a, b : Nat} -> S a = S b -> a = b
s_inj Refl = Refl

cong3 : (f : x -> y -> z -> w) -> {a1,a2 : x} -> {b1,b2 : y} -> {c1,c2 : z} -> a1 = a2 -> b1 = b2 -> c1 = c2 -> f a1 b1 c1 = f a2 b2 c2
cong3 f Refl Refl Refl = Refl

plus_x_s1 : (a : Nat) -> a + (S Z) = S a
plus_x_s1 a = trans (plus_n_s a Z) (cong S (plus_n_z a))

data PSplit : Nat -> Nat -> Nat -> Type where
  PSL : {a, b, n : Nat} -> (a2 : Nat) -> a = S a2 -> a2 + b = n -> PSplit a b n
  PSR : {a, b, n : Nat} -> (b2 : Nat) -> b = S b2 -> a + b2 = n -> PSplit a b n

plus_succ_split : (a, b, n : Nat) -> a + b = S n -> PSplit a b n
plus_succ_split 0 b n e = PSR n e Refl
plus_succ_split (S k) b n e = PSL k Refl (s_inj e)

data Split : MS -> MS -> MS -> Tag -> Type where
  SplitL : {m1, m2, m : MS} -> {t : Tag} -> (m1p : MS) -> m1 = msadd m1p (singleton t) -> m = msadd m1p m2 -> Split m1 m2 m t
  SplitR : {m1, m2, m : MS} -> {t : Tag} -> (m2p : MS) -> m2 = msadd m2p (singleton t) -> m = msadd m1 m2p -> Split m1 m2 m t

msadd_split : (m1, m2, m : MS) -> (t : Tag) -> msadd m1 m2 = msadd m (singleton t) -> Split m1 m2 m t
msadd_split (MkMS a1 b1 c1) (MkMS a2 b2 c2) (MkMS am bm cm) TA e =
  case plus_succ_split a1 a2 am (trans (cong msa e) (plus_x_s1 am)) of
    PSL k ea en => SplitL (MkMS k b1 c1)
      (cong3 MkMS (trans ea (sym (plus_x_s1 k))) (sym (plus_n_z b1)) (sym (plus_n_z c1)))
      (cong3 MkMS (sym en) (sym (trans (cong msb e) (plus_n_z bm))) (sym (trans (cong msc e) (plus_n_z cm))))
    PSR k eb en => SplitR (MkMS k b2 c2)
      (cong3 MkMS (trans eb (sym (plus_x_s1 k))) (sym (plus_n_z b2)) (sym (plus_n_z c2)))
      (cong3 MkMS (sym en) (sym (trans (cong msb e) (plus_n_z bm))) (sym (trans (cong msc e) (plus_n_z cm))))
msadd_split (MkMS a1 b1 c1) (MkMS a2 b2 c2) (MkMS am bm cm) TB e =
  case plus_succ_split b1 b2 bm (trans (cong msb e) (plus_x_s1 bm)) of
    PSL k eb en => SplitL (MkMS a1 k c1)
      (cong3 MkMS (sym (plus_n_z a1)) (trans eb (sym (plus_x_s1 k))) (sym (plus_n_z c1)))
      (cong3 MkMS (sym (trans (cong msa e) (plus_n_z am))) (sym en) (sym (trans (cong msc e) (plus_n_z cm))))
    PSR k eb en => SplitR (MkMS a2 k c2)
      (cong3 MkMS (sym (plus_n_z a2)) (trans eb (sym (plus_x_s1 k))) (sym (plus_n_z c2)))
      (cong3 MkMS (sym (trans (cong msa e) (plus_n_z am))) (sym en) (sym (trans (cong msc e) (plus_n_z cm))))
msadd_split (MkMS a1 b1 c1) (MkMS a2 b2 c2) (MkMS am bm cm) TC e =
  case plus_succ_split c1 c2 cm (trans (cong msc e) (plus_x_s1 cm)) of
    PSL k ec en => SplitL (MkMS a1 b1 k)
      (cong3 MkMS (sym (plus_n_z a1)) (sym (plus_n_z b1)) (trans ec (sym (plus_x_s1 k))))
      (cong3 MkMS (sym (trans (cong msa e) (plus_n_z am))) (sym (trans (cong msb e) (plus_n_z bm))) (sym en))
    PSR k ec en => SplitR (MkMS a2 b2 k)
      (cong3 MkMS (sym (plus_n_z a2)) (sym (plus_n_z b2)) (trans ec (sym (plus_x_s1 k))))
      (cong3 MkMS (sym (trans (cong msa e) (plus_n_z am))) (sym (trans (cong msb e) (plus_n_z bm))) (sym en))

zero_is_succ : {0 g : Type} -> (n : Nat) -> Z = S n -> g
zero_is_succ n Refl impossible

ms_singleton_nonzero : {0 g : Type} -> (m : MS) -> (t : Tag) -> msadd m (singleton t) = MkMS 0 0 0 -> g
ms_singleton_nonzero (MkMS a b c) TA e = zero_is_succ a (sym (trans (sym (plus_x_s1 a)) (cong msa e)))
ms_singleton_nonzero (MkMS a b c) TB e = zero_is_succ b (sym (trans (sym (plus_x_s1 b)) (cong msb e)))
ms_singleton_nonzero (MkMS a b c) TC e = zero_is_succ c (sym (trans (sym (plus_x_s1 c)) (cong msc e)))

singleton_cancel : (m : MS) -> (t : Tag) -> singleton t = msadd m (singleton t) -> m = MkMS 0 0 0
singleton_cancel (MkMS a b c) TA e = cong3 MkMS (sym (s_inj (trans (cong msa e) (plus_x_s1 a)))) (trans (sym (plus_n_z b)) (sym (cong msb e))) (trans (sym (plus_n_z c)) (sym (cong msc e)))
singleton_cancel (MkMS a b c) TB e = cong3 MkMS (trans (sym (plus_n_z a)) (sym (cong msa e))) (sym (s_inj (trans (cong msb e) (plus_x_s1 b)))) (trans (sym (plus_n_z c)) (sym (cong msc e)))
singleton_cancel (MkMS a b c) TC e = cong3 MkMS (trans (sym (plus_n_z a)) (sym (cong msa e))) (trans (sym (plus_n_z b)) (sym (cong msb e))) (sym (s_inj (trans (cong msc e) (plus_x_s1 c))))

deriv_atom : (s, t : Tag) -> (m : MS) -> singleton s = msadd m (singleton t) -> Accepts (deriv (PAtom s) t) m
deriv_atom TA TA m q = rewrite singleton_cancel m TA q in AOne
deriv_atom TA TB (MkMS a b c) q = zero_is_succ b (trans (cong msb q) (plus_x_s1 b))
deriv_atom TA TC (MkMS a b c) q = zero_is_succ c (trans (cong msc q) (plus_x_s1 c))
deriv_atom TB TA (MkMS a b c) q = zero_is_succ a (trans (cong msa q) (plus_x_s1 a))
deriv_atom TB TB m q = rewrite singleton_cancel m TB q in AOne
deriv_atom TB TC (MkMS a b c) q = zero_is_succ c (trans (cong msc q) (plus_x_s1 c))
deriv_atom TC TA (MkMS a b c) q = zero_is_succ a (trans (cong msa q) (plus_x_s1 a))
deriv_atom TC TB (MkMS a b c) q = zero_is_succ b (trans (cong msb q) (plus_x_s1 b))
deriv_atom TC TC m q = rewrite singleton_cancel m TC q in AOne

dc_gen : {pat : Pat} -> (t : Tag) -> (m : MS) -> {idx : MS} -> Accepts pat idx -> idx = msadd m (singleton t) -> Accepts (deriv pat t) m
dc_gen t m AOne q = ms_singleton_nonzero m t (sym q)
dc_gen t m AAtomA q = deriv_atom TA t m q
dc_gen t m AAtomB q = deriv_atom TB t m q
dc_gen t m AAtomC q = deriv_atom TC t m q
dc_gen t m (APlusL ae) q = APlusL (dc_gen t m ae q)
dc_gen t m (APlusR af) q = APlusR (dc_gen t m af q)
dc_gen t m (ATimes m1 m2 ae af) q = case msadd_split m1 m2 m t q of
  SplitL m1p e1 e2 => APlusL (rewrite e2 in ATimes m1p m2 (dc_gen t m1p ae e1) af)
  SplitR m2p e1 e2 => APlusR (rewrite e2 in ATimes m1 m2p ae (dc_gen t m2p af e1))
dc_gen t m AStar0 q = ms_singleton_nonzero m t (sym q)
dc_gen t m (AStarN m1 m2 ae as) q = case msadd_split m1 m2 m t q of
  SplitL m1p e1 e2 => rewrite e2 in ATimes m1p m2 (dc_gen t m1p ae e1) as
  SplitR m2p e1 e2 => case dc_gen t m2p as e1 of
    ATimes p1 p2 ad astar => rewrite (trans e2 (trans (sym (msadd_assoc m1 p1 p2)) (trans (cong (\x => msadd x p2) (msadd_comm m1 p1)) (msadd_assoc p1 m1 p2)))) in ATimes p1 (msadd m1 p2) ad (AStarN m1 p2 ae astar)

deriv_complete : (pat : Pat) -> (t : Tag) -> (m : MS) -> Accepts pat (msadd m (singleton t)) -> Accepts (deriv pat t) m
deriv_complete pat t m acc = dc_gen t m acc Refl

matches_word_complete : (e : Pat) -> (w : Word) -> Accepts e (parikh w) -> nullable (dfold e w) = T
matches_word_complete e WNil acc = nullable_complete e acc
matches_word_complete e (WCons t rest) acc = matches_word_complete (deriv e t) rest (deriv_complete e t (parikh rest) (rewrite msadd_comm (parikh rest) (singleton t) in acc))
