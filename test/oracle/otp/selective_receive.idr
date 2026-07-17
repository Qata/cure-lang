%default total

data Tag = TInc | TDec | TQuery
data TagList = TNil | TCons Tag TagList

data Accepted : Tag -> Type where
  AccInc : Accepted TInc
  AccQuery : Accepted TQuery

data AllAccepted : TagList -> Type where
  AANil : AllAccepted TNil
  AACons : Accepted t -> AllAccepted rest -> AllAccepted (TCons t rest)

data SelRecv : TagList -> Tag -> TagList -> Type where
  SelHere : SelRecv (TCons x rest) x rest
  SelSkip : SelRecv rest x rest2 -> SelRecv (TCons y rest) x (TCons y rest2)

preserves : AllAccepted before -> SelRecv before x after -> AllAccepted after
preserves (AACons accx rest_acc) SelHere = rest_acc
preserves (AACons accy rest_acc) (SelSkip s2) = AACons accy (preserves rest_acc s2)

received_accepted : AllAccepted before -> SelRecv before x after -> Accepted x
received_accepted (AACons accx rest_acc) SelHere = accx
received_accepted (AACons accy rest_acc) (SelSkip s2) = received_accepted rest_acc s2

example : SelRecv (TCons TInc (TCons TQuery TNil)) TQuery (TCons TInc TNil)
example = SelSkip SelHere
