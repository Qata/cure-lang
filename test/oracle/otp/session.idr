%default total

data Tag = TA | TB | TC
data SType = SEnd | SSend Tag SType | SRecv Tag SType

dual : SType -> SType
dual SEnd = SEnd
dual (SSend t k) = SRecv t (dual k)
dual (SRecv t k) = SSend t (dual k)

dual_involution : (s : SType) -> dual (dual s) = s
dual_involution SEnd = Refl
dual_involution (SSend t k) = rewrite dual_involution k in Refl
dual_involution (SRecv t k) = rewrite dual_involution k in Refl

data Compat : SType -> SType -> Type where
  CEnd : Compat SEnd SEnd
  CSR : (t : Tag) -> Compat l r -> Compat (SSend t l) (SRecv t r)
  CRS : (t : Tag) -> Compat l r -> Compat (SRecv t l) (SSend t r)

ssend_cong : (t : Tag) -> a = b -> SSend t a = SSend t b
ssend_cong t e = cong (SSend t) e

srecv_cong : (t : Tag) -> a = b -> SRecv t a = SRecv t b
srecv_cong t e = cong (SRecv t) e

compat_dual : Compat l r -> l = dual r
compat_dual CEnd = Refl
compat_dual (CSR t c2) = ssend_cong t (compat_dual c2)
compat_dual (CRS t c2) = srecv_cong t (compat_dual c2)
