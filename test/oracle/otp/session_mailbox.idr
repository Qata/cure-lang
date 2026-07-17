%default total

data Tag = TA | TB | TC
data Local = LEnd | LSend Tag Local | LRecv Tag Local
data MS = MkMS Nat Nat Nat

bump : Tag -> MS -> MS
bump TA (MkMS a b c) = MkMS (S a) b c
bump TB (MkMS a b c) = MkMS a (S b) c
bump TC (MkMS a b c) = MkMS a b (S c)

recvs : Local -> MS
recvs LEnd = MkMS 0 0 0
recvs (LSend t k) = recvs k
recvs (LRecv t k) = bump t (recvs k)

sends : Local -> MS
sends LEnd = MkMS 0 0 0
sends (LSend t k) = bump t (sends k)
sends (LRecv t k) = sends k

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)

bump_cong : (t : Tag) -> a = b -> bump t a = bump t b
bump_cong t prf = cong (bump t) prf

recvs_dual : (l : Local) -> recvs (dual l) = sends l
recvs_dual LEnd = Refl
recvs_dual (LSend t k) = bump_cong t (recvs_dual k)
recvs_dual (LRecv t k) = recvs_dual k

sends_dual : (l : Local) -> sends (dual l) = recvs l
sends_dual LEnd = Refl
sends_dual (LSend t k) = sends_dual k
sends_dual (LRecv t k) = bump_cong t (sends_dual k)
