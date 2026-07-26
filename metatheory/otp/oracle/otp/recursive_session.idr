%default total

data Tag = TA | TB | TC
data RSType = REnd | RSend Tag RSType | RRecv Tag RSType | RVar | RMu RSType

subst : RSType -> RSType -> RSType
subst REnd u = REnd
subst (RSend t k) u = RSend t (subst k u)
subst (RRecv t k) u = RRecv t (subst k u)
subst RVar u = u
subst (RMu body) u = RMu body

unfold : RSType -> RSType
unfold REnd = REnd
unfold (RSend t k) = RSend t k
unfold (RRecv t k) = RRecv t k
unfold RVar = RVar
unfold (RMu body) = subst body (RMu body)

rdual : RSType -> RSType
rdual REnd = REnd
rdual (RSend t k) = RRecv t (rdual k)
rdual (RRecv t k) = RSend t (rdual k)
rdual RVar = RVar
rdual (RMu body) = RMu (rdual body)

rdual_involution : (s : RSType) -> rdual (rdual s) = s
rdual_involution REnd = Refl
rdual_involution (RSend t k) = rewrite rdual_involution k in Refl
rdual_involution (RRecv t k) = rewrite rdual_involution k in Refl
rdual_involution RVar = Refl
rdual_involution (RMu body) = rewrite rdual_involution body in Refl

subst_dual : (s : RSType) -> (u : RSType) -> rdual (subst s u) = subst (rdual s) (rdual u)
subst_dual REnd u = Refl
subst_dual (RSend t k) u = rewrite subst_dual k u in Refl
subst_dual (RRecv t k) u = rewrite subst_dual k u in Refl
subst_dual RVar u = Refl
subst_dual (RMu body) u = Refl

dual_unfold_commute : (body : RSType) -> rdual (unfold (RMu body)) = unfold (RMu (rdual body))
dual_unfold_commute body = subst_dual body (RMu body)

rdual_unfold : (s : RSType) -> rdual (unfold s) = unfold (rdual s)
rdual_unfold REnd = Refl
rdual_unfold (RSend t k) = Refl
rdual_unfold (RRecv t k) = Refl
rdual_unfold RVar = Refl
rdual_unfold (RMu body) = subst_dual body (RMu body)
