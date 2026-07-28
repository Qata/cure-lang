%default total

data Tag = TInc | TDec | TQuery
data TagList = TNil | TCons Tag TagList

data Accepted : Tag -> Type where
  AccInc : Accepted TInc
  AccQuery : Accepted TQuery

data AllAccepted : TagList -> Type where
  AANil : AllAccepted TNil
  AACons : Accepted t -> AllAccepted rest -> AllAccepted (TCons t rest)

data Config = MkConfig TagList TagList

data WT : Config -> Type where
  MkWT : AllAccepted e -> AllAccepted m -> WT (MkConfig e m)

data Step : Config -> Config -> Type where
  SSend : Accepted t -> Step (MkConfig e m) (MkConfig (TCons t e) m)
  SArrive : Step (MkConfig (TCons t e) m) (MkConfig e (TCons t m))
  SRecv : Step (MkConfig e (TCons t m)) (MkConfig e m)

preservation : WT b -> Step b a -> WT a
preservation (MkWT ae am) (SSend acc) = MkWT (AACons acc ae) am
preservation (MkWT (AACons at ae2) am) SArrive = MkWT ae2 (AACons at am)
preservation (MkWT ae (AACons rat am2)) SRecv = MkWT ae am2
