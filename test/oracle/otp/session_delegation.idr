%default total

data Tag = TA | TB | TC
data SType = SEnd | SSend Tag SType | SRecv Tag SType | SDeleg SType SType | SResume SType SType

dual : SType -> SType
dual SEnd = SEnd
dual (SSend t k) = SRecv t (dual k)
dual (SRecv t k) = SSend t (dual k)
dual (SDeleg a k) = SResume a (dual k)
dual (SResume a k) = SDeleg a (dual k)

dual_involution : (s : SType) -> dual (dual s) = s
dual_involution SEnd = Refl
dual_involution (SSend t k) = rewrite dual_involution k in Refl
dual_involution (SRecv t k) = rewrite dual_involution k in Refl
dual_involution (SDeleg a k) = rewrite dual_involution k in Refl
dual_involution (SResume a k) = rewrite dual_involution k in Refl

data Compat : SType -> SType -> Type where
  CEnd : Compat SEnd SEnd
  CSR : (t : Tag) -> Compat l r -> Compat (SSend t l) (SRecv t r)
  CRS : (t : Tag) -> Compat l r -> Compat (SRecv t l) (SSend t r)
  CDel : (a : SType) -> Compat l r -> Compat (SDeleg a l) (SResume a r)
  CRes : (a : SType) -> Compat l r -> Compat (SResume a l) (SDeleg a r)

ssend_cong : (t : Tag) -> a = b -> SSend t a = SSend t b
ssend_cong t prf = cong (SSend t) prf

srecv_cong : (t : Tag) -> a = b -> SRecv t a = SRecv t b
srecv_cong t prf = cong (SRecv t) prf

sdeleg_cong : (a : SType) -> x = y -> SDeleg a x = SDeleg a y
sdeleg_cong a prf = cong (SDeleg a) prf

sresume_cong : (a : SType) -> x = y -> SResume a x = SResume a y
sresume_cong a prf = cong (SResume a) prf

compat_dual : Compat l r -> l = dual r
compat_dual CEnd = Refl
compat_dual (CSR t c2) = ssend_cong t (compat_dual c2)
compat_dual (CRS t c2) = srecv_cong t (compat_dual c2)
compat_dual (CDel a c2) = sdeleg_cong a (compat_dual c2)
compat_dual (CRes a c2) = sresume_cong a (compat_dual c2)
