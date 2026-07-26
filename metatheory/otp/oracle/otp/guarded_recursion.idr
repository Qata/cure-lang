%default total

data Role = RA | RB | RC
data Tag = TA | TB | TC
data B = F | T
data Global = GEnd | GMsg Role Role Tag Global | GRec Global | GVar

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

pingpong_guarded : head_guarded (GRec (GMsg RA RB TA GVar)) = T
pingpong_guarded = Refl

pingpong_unfolds_to_comm : gsubst (GMsg RA RB TA GVar) (GRec (GMsg RA RB TA GVar)) = GMsg RA RB TA (GRec (GMsg RA RB TA GVar))
pingpong_unfolds_to_comm = Refl

barerec_unguarded : head_guarded (GRec GVar) = F
barerec_unguarded = Refl
