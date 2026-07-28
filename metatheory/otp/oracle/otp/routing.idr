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

data System = SNil | SCons Config System

data WTSys : System -> Type where
  WSNil : WTSys SNil
  WSCons : WT c -> WTSys rest -> WTSys (SCons c rest)

data Deliver : System -> System -> Type where
  DeliverHere : Accepted t -> Deliver (SCons (MkConfig e m) rest) (SCons (MkConfig (TCons t e) m) rest)
  DeliverThere : Deliver rest rest2 -> Deliver (SCons c rest) (SCons c rest2)

deliver_preservation : WTSys b -> Deliver b a -> WTSys a
deliver_preservation (WSCons (MkWT ae am) wrest) (DeliverHere acc) = WSCons (MkWT (AACons acc ae) am) wrest
deliver_preservation (WSCons wtc wrest) (DeliverThere d2) = WSCons wtc (deliver_preservation wrest d2)
