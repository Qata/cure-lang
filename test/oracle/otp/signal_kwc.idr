%default total

data Sender = SA | SB
data Tag = TA | TB
data Reason = Normal | Abnormal | Kill
data Sig = SMsg Tag | SLink | SExit Reason | SMon | SDown Reason

is_death : Sig -> Bool
is_death (SMsg t) = False
is_death SLink = False
is_death (SExit r) = True
is_death SMon = False
is_death (SDown r) = True

data SItem = MkItem Sender Sig

is_death_item : SItem -> Bool
is_death_item (MkItem s g) = is_death g

data SList = SNil | SCons SItem SList

proj : Sender -> SList -> SList
proj s SNil = SNil
proj SA (SCons (MkItem SA g) rest) = SCons (MkItem SA g) (proj SA rest)
proj SB (SCons (MkItem SA g) rest) = proj SB rest
proj SA (SCons (MkItem SB g) rest) = proj SA rest
proj SB (SCons (MkItem SB g) rest) = SCons (MkItem SB g) (proj SB rest)

data Interleave : SList -> SList -> SList -> Type where
  ILNil : Interleave SNil SNil SNil
  ILLeft : Interleave xs ys mbox -> Interleave (SCons (MkItem SA g) xs) ys (SCons (MkItem SA g) mbox)
  ILRight : Interleave xs ys mbox -> Interleave xs (SCons (MkItem SB g) ys) (SCons (MkItem SB g) mbox)

proj_left : Interleave xs ys mbox -> proj SA mbox = xs
proj_left ILNil = Refl
proj_left (ILLeft il2) = rewrite proj_left il2 in Refl
proj_left (ILRight il2) = proj_left il2

proj_right : Interleave xs ys mbox -> proj SB mbox = ys
proj_right ILNil = Refl
proj_right (ILLeft il2) = proj_right il2
proj_right (ILRight il2) = rewrite proj_right il2 in Refl

data DeathLast : SList -> Type where
  DLNil : DeathLast SNil
  DLOne : DeathLast (SCons it SNil)
  DLCons : is_death_item it = False -> DeathLast (SCons h2 t2) -> DeathLast (SCons it (SCons h2 t2))

death_last_proj : Interleave xs ys mbox -> DeathLast xs -> DeathLast (proj SA mbox)
death_last_proj il dl = rewrite proj_left il in dl

death_last_proj_b : Interleave xs ys mbox -> DeathLast ys -> DeathLast (proj SB mbox)
death_last_proj_b il dl = rewrite proj_right il in dl

example_interleave : Interleave (SCons (MkItem SA (SMsg TA)) (SCons (MkItem SA (SExit Normal)) SNil)) (SCons (MkItem SB (SMsg TB)) SNil) (SCons (MkItem SA (SMsg TA)) (SCons (MkItem SB (SMsg TB)) (SCons (MkItem SA (SExit Normal)) SNil)))
example_interleave = ILLeft (ILRight (ILLeft ILNil))

example_death_last : DeathLast (SCons (MkItem SA (SMsg TA)) (SCons (MkItem SA (SExit Normal)) SNil))
example_death_last = DLCons Refl DLOne

example_kwc : DeathLast (proj SA (SCons (MkItem SA (SMsg TA)) (SCons (MkItem SB (SMsg TB)) (SCons (MkItem SA (SExit Normal)) SNil))))
example_kwc = death_last_proj example_interleave example_death_last
