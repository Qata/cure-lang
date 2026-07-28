%default total

data Tag = TA | TB | TC
data Mailbox = BNil | BCons Tag Mailbox
data MList = MNil | MCons Tag MList
data Protocol = PDone | PExpect Tag Protocol

ptags : Protocol -> MList
ptags PDone = MNil
ptags (PExpect t rest) = MCons t (ptags rest)

data SingleRecv : Tag -> Mailbox -> Mailbox -> Type where
  SVHere : SingleRecv t (BCons t rest) rest
  SVSkip : SingleRecv t rest after -> SingleRecv t (BCons h rest) (BCons h after)

data ConvRecv : Protocol -> Mailbox -> Mailbox -> MList -> Type where
  CRDone : ConvRecv PDone mbox mbox MNil
  CRStep : (t : Tag) -> SingleRecv t before mid -> ConvRecv rest mid after msgs -> ConvRecv (PExpect t rest) before after (MCons t msgs)

mcons_cong : (t : Tag) -> xs = ys -> MCons t xs = MCons t ys
mcons_cong t e = cong (MCons t) e

conv_order : ConvRecv proto before after received -> received = ptags proto
conv_order CRDone = Refl
conv_order (CRStep t sv cr2) = mcons_cong t (conv_order cr2)
