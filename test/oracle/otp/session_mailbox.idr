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
