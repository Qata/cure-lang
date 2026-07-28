%default total

data Sender = SA | SB
data Tag = TA | TB | TC
data Msg = MkMsg Sender Tag
data MList = MNil | MCons Msg MList

proj : Sender -> MList -> MList
proj s MNil = MNil
proj SA (MCons (MkMsg SA t) rest) = MCons (MkMsg SA t) (proj SA rest)
proj SB (MCons (MkMsg SA t) rest) = proj SB rest
proj SA (MCons (MkMsg SB t) rest) = proj SA rest
proj SB (MCons (MkMsg SB t) rest) = MCons (MkMsg SB t) (proj SB rest)

data Interleave : MList -> MList -> MList -> Type where
  ILNil : Interleave MNil MNil MNil
  ILLeft : Interleave xs ys mbox -> Interleave (MCons (MkMsg SA t) xs) ys (MCons (MkMsg SA t) mbox)
  ILRight : Interleave xs ys mbox -> Interleave xs (MCons (MkMsg SB t) ys) (MCons (MkMsg SB t) mbox)

proj_left : Interleave xs ys mbox -> proj SA mbox = xs
proj_left ILNil = Refl
proj_left (ILLeft il2) = rewrite proj_left il2 in Refl
proj_left (ILRight il2) = proj_left il2

proj_right : Interleave xs ys mbox -> proj SB mbox = ys
proj_right ILNil = Refl
proj_right (ILLeft il2) = proj_right il2
proj_right (ILRight il2) = rewrite proj_right il2 in Refl
