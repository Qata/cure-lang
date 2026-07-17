%default total

data Tag = TA | TB | TC
data Local = LEnd | LSend Tag Local | LRecv Tag Local | LPar Local Local
data MS = MkMS Nat Nat Nat

add : Nat -> Nat -> Nat
add Z n = n
add (S k) n = S (add k n)

msum : MS -> MS -> MS
msum (MkMS a1 b1 c1) (MkMS a2 b2 c2) = MkMS (add a1 a2) (add b1 b2) (add c1 c2)

bump : Tag -> MS -> MS
bump TA (MkMS a b c) = MkMS (S a) b c
bump TB (MkMS a b c) = MkMS a (S b) c
bump TC (MkMS a b c) = MkMS a b (S c)

recvs : Local -> MS
recvs LEnd = MkMS 0 0 0
recvs (LSend t k) = recvs k
recvs (LRecv t k) = bump t (recvs k)
recvs (LPar a b) = msum (recvs a) (recvs b)

sends : Local -> MS
sends LEnd = MkMS 0 0 0
sends (LSend t k) = bump t (sends k)
sends (LRecv t k) = sends k
sends (LPar a b) = msum (sends a) (sends b)

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)
dual (LPar a b) = LPar (dual a) (dual b)

bump_cong : (t : Tag) -> a = b -> bump t a = bump t b
bump_cong t prf = cong (bump t) prf

msum_cong : a1 = b1 -> a2 = b2 -> msum a1 a2 = msum b1 b2
msum_cong ea eb = cong2 msum ea eb

recvs_dual : (l : Local) -> recvs (dual l) = sends l
recvs_dual LEnd = Refl
recvs_dual (LSend t k) = bump_cong t (recvs_dual k)
recvs_dual (LRecv t k) = recvs_dual k
recvs_dual (LPar a b) = msum_cong (recvs_dual a) (recvs_dual b)

sends_dual : (l : Local) -> sends (dual l) = recvs l
sends_dual LEnd = Refl
sends_dual (LSend t k) = sends_dual k
sends_dual (LRecv t k) = bump_cong t (sends_dual k)
sends_dual (LPar a b) = msum_cong (sends_dual a) (sends_dual b)

data Compat : Local -> Local -> Type where
  CEnd : Compat LEnd LEnd
  CSR : (t : Tag) -> Compat l r -> Compat (LSend t l) (LRecv t r)
  CRS : (t : Tag) -> Compat l r -> Compat (LRecv t l) (LSend t r)
  CPar : Compat la ra -> Compat lb rb -> Compat (LPar la lb) (LPar ra rb)

compat_recv_send : Compat l r -> recvs l = sends r
compat_recv_send CEnd = Refl
compat_recv_send (CSR t c2) = compat_recv_send c2
compat_recv_send (CRS t c2) = bump_cong t (compat_recv_send c2)
compat_recv_send (CPar ca cb) = msum_cong (compat_recv_send ca) (compat_recv_send cb)

compat_send_recv : Compat l r -> sends l = recvs r
compat_send_recv CEnd = Refl
compat_send_recv (CSR t c2) = bump_cong t (compat_send_recv c2)
compat_send_recv (CRS t c2) = compat_send_recv c2
compat_send_recv (CPar ca cb) = msum_cong (compat_send_recv ca) (compat_send_recv cb)

seq : Local -> Local -> Local
seq LEnd t = t
seq (LSend tg k) t = LSend tg (seq k t)
seq (LRecv tg k) t = LRecv tg (seq k t)
seq (LPar a b) t = LPar a (seq b t)

add_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> add (add x y) z = add x (add y z)
add_assoc Z y z = Refl
add_assoc (S k) y z = rewrite add_assoc k y z in Refl

mkms_cong : a1 = a2 -> b1 = b2 -> c1 = c2 -> MkMS a1 b1 c1 = MkMS a2 b2 c2
mkms_cong Refl Refl Refl = Refl

msum_assoc : (m : MS) -> (n : MS) -> (p : MS) -> msum (msum m n) p = msum m (msum n p)
msum_assoc (MkMS a1 b1 c1) (MkMS a2 b2 c2) (MkMS a3 b3 c3) =
  mkms_cong (add_assoc a1 a2 a3) (add_assoc b1 b2 b3) (add_assoc c1 c2 c3)

bump_msum_dist : (t : Tag) -> (m : MS) -> (n : MS) -> bump t (msum m n) = msum (bump t m) n
bump_msum_dist TA (MkMS a1 b1 c1) (MkMS a2 b2 c2) = Refl
bump_msum_dist TB (MkMS a1 b1 c1) (MkMS a2 b2 c2) = Refl
bump_msum_dist TC (MkMS a1 b1 c1) (MkMS a2 b2 c2) = Refl

msum_empty_l : (n : MS) -> n = msum (MkMS 0 0 0) n
msum_empty_l (MkMS a b c) = Refl

recvs_hom : (s : Local) -> (t : Local) -> recvs (seq s t) = msum (recvs s) (recvs t)
recvs_hom LEnd t = msum_empty_l (recvs t)
recvs_hom (LSend tg k) t = recvs_hom k t
recvs_hom (LRecv tg k) t = trans (cong (bump tg) (recvs_hom k t)) (bump_msum_dist tg (recvs k) (recvs t))
recvs_hom (LPar a b) t = trans (cong (msum (recvs a)) (recvs_hom b t)) (sym (msum_assoc (recvs a) (recvs b) (recvs t)))

sends_hom : (s : Local) -> (t : Local) -> sends (seq s t) = msum (sends s) (sends t)
sends_hom LEnd t = msum_empty_l (sends t)
sends_hom (LSend tg k) t = trans (cong (bump tg) (sends_hom k t)) (bump_msum_dist tg (sends k) (sends t))
sends_hom (LRecv tg k) t = sends_hom k t
sends_hom (LPar a b) t = trans (cong (msum (sends a)) (sends_hom b t)) (sym (msum_assoc (sends a) (sends b) (sends t)))
