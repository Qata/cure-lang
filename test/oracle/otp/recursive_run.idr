%default total

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList

data Handles : Tag -> TagList -> Type where
  HHere : Handles t (TCons t rest)
  HThere : Handles t rest -> Handles t (TCons y rest)

data AllHandled : TagList -> TagList -> Type where
  AHNil : AllHandled TNil iface
  AHCons : Handles t iface -> AllHandled rest iface -> AllHandled (TCons t rest) iface

data Config = MkConfig TagList TagList

data WTat : Config -> TagList -> Type where
  MkWTat : AllHandled e iface -> AllHandled m iface -> WTat (MkConfig e m) iface

data StepAt : TagList -> Config -> Config -> Type where
  SSendAt : Handles t i -> StepAt i (MkConfig e m) (MkConfig (TCons t e) m)
  SArriveAt : StepAt i (MkConfig (TCons t e) m) (MkConfig e (TCons t m))
  SRecvAt : StepAt i (MkConfig e (TCons t m)) (MkConfig e m)

preservation_at : {i : TagList} -> {0 b : Config} -> {0 a : Config} -> WTat b i -> StepAt i b a -> WTat a i
preservation_at (MkWTat ae am) (SSendAt mem) = MkWTat (AHCons mem ae) am
preservation_at (MkWTat ae am) SArriveAt = case ae of
  AHCons at ae2 => MkWTat ae2 (AHCons at am)
  AHNil impossible
preservation_at (MkWTat ae am) SRecvAt = case am of
  AHCons rat am2 => MkWTat ae am2
  AHNil impossible

data RunsAt : TagList -> Config -> Type where
  RAStart : RunsAt i (MkConfig TNil TNil)
  RAStep : RunsAt i before -> StepAt i before after -> RunsAt i after

adequacy_at : {i : TagList} -> {0 c : Config} -> RunsAt i c -> WTat c i
adequacy_at RAStart = MkWTat AHNil AHNil
adequacy_at (RAStep prev step) = preservation_at (adequacy_at prev) step
