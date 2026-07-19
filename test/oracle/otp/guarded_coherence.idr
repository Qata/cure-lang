%default total

data Role = RA | RB | RC
data Tag = TA | TB | TC
data B = F | T
data Global = GEnd | GMsg Role Role Tag Global | GRec Global | GVar

role_eq : Role -> Role -> B
role_eq RA RA = T
role_eq RA RB = F
role_eq RA RC = F
role_eq RB RA = F
role_eq RB RB = T
role_eq RB RC = F
role_eq RC RA = F
role_eq RC RB = F
role_eq RC RC = T

gsubst : Global -> Global -> Global
gsubst GEnd s = GEnd
gsubst (GMsg from to t k) s = GMsg from to t (gsubst k s)
gsubst (GRec body) s = GRec body
gsubst GVar s = s

head_guarded : Global -> B
head_guarded GEnd = T
head_guarded (GMsg from to t k) = T
head_guarded (GRec body) = head_guarded body
head_guarded GVar = F

guarded_subst : (body : Global) -> (s : Global) -> head_guarded body = T -> head_guarded (gsubst body s) = T
guarded_subst GEnd s hg = Refl
guarded_subst (GMsg from to t k) s hg = Refl
guarded_subst (GRec b) s hg = hg
guarded_subst GVar s Refl impossible

unfold_productive : (body : Global) -> head_guarded body = T -> head_guarded (gsubst body (GRec body)) = T
unfold_productive body hg = guarded_subst body (GRec body) hg

data GCoherent : Global -> Type where
  GCoEnd : GCoherent GEnd
  GCoMsg : role_eq p q = F -> GCoherent k -> GCoherent (GMsg p q t k)
  GCoRec : head_guarded body = T -> GCoherent body -> GCoherent (GRec body)
  GCoVar : GCoherent GVar

gcoherent_head_distinct : GCoherent (GMsg p q t k) -> role_eq p q = F
gcoherent_head_distinct (GCoMsg neq ck) = neq

gcoherent_guard : GCoherent (GRec body) -> head_guarded body = T
gcoherent_guard (GCoRec hg cb) = hg

gcoherent_productive : (body : Global) -> GCoherent (GRec body) -> head_guarded (gsubst body (GRec body)) = T
gcoherent_productive body c = unfold_productive body (gcoherent_guard c)

pingpong_gcoherent : GCoherent (GRec (GMsg RA RB TA GVar))
pingpong_gcoherent = GCoRec Refl (GCoMsg Refl GCoVar)
