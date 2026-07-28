%default total

data Tag = TInc | TQuery | TDown
data TagList = TNil | TCons Tag TagList

data Accepted : Tag -> Type where
  AccInc : Accepted TInc
  AccQuery : Accepted TQuery
  AccDown : Accepted TDown

data AllAccepted : TagList -> Type where
  AANil : AllAccepted TNil
  AACons : Accepted t -> AllAccepted rest -> AllAccepted (TCons t rest)

data Config = MkConfig TagList TagList

data WT : Config -> Type where
  MkWT : AllAccepted e -> AllAccepted m -> WT (MkConfig e m)

data MRef = MkMRef (Accepted TDown)

monitor_accepts : MRef -> Accepted TDown
monitor_accepts (MkMRef a) = a

data Step : Config -> Config -> Type where
  SDown : MRef -> Step (MkConfig e m) (MkConfig (TCons TDown e) m)

preservation : WT b -> Step b a -> WT a
preservation (MkWT ae am) (SDown (MkMRef accdown)) = MkWT (AACons accdown ae) am

establish : MRef
establish = MkMRef AccDown
