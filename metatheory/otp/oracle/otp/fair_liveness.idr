%default total

data Bool' = F | T
data P = Idle | Crit
data Config = MkConfig P P
data Move = Enter1 | Exit1 | Enter2 | Exit2
data EList = ENil | ECons Move EList

step : Config -> Move -> Config
step (MkConfig p1 p2) Enter1 = case p2 of
  Idle => MkConfig Crit p2
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit1 = MkConfig Idle p2
step (MkConfig p1 p2) Enter2 = case p1 of
  Idle => MkConfig p1 Crit
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit2 = MkConfig p1 Idle

p1_crit : Config -> Bool'
p1_crit (MkConfig Idle p2) = F
p1_crit (MkConfig Crit p2) = T

p1_idle : Config -> Bool'
p1_idle (MkConfig Idle p2) = T
p1_idle (MkConfig Crit p2) = F

runs : Config -> EList -> Config
runs c ENil = c
runs c (ECons m rest) = runs (step c m) rest

data Fair : Config -> EList -> Type where
  FairNow  : Fair (MkConfig Idle Idle) (ECons Enter1 rest)
  FairStep : Fair (step c m) rest -> Fair c (ECons m rest)

data EvP1Crit : Config -> EList -> Type where
  EvNow   : p1_crit c = T -> EvP1Crit c sched
  EvLater : EvP1Crit (step c m) rest -> EvP1Crit c (ECons m rest)

fair_enters : Fair c sched -> EvP1Crit c sched
fair_enters FairNow = EvLater (EvNow Refl)
fair_enters (FairStep f2) = EvLater (fair_enters f2)

data P2Only : EList -> Type where
  P2Nil   : P2Only ENil
  P2Enter : P2Only rest -> P2Only (ECons Enter2 rest)
  P2Exit  : P2Only rest -> P2Only (ECons Exit2 rest)

enter2_keeps_idle : (c : Config) -> p1_idle c = T -> p1_idle (step c Enter2) = T
enter2_keeps_idle (MkConfig Idle p2) h = Refl
enter2_keeps_idle (MkConfig Crit p2) Refl impossible

exit2_keeps_idle : (c : Config) -> p1_idle c = T -> p1_idle (step c Exit2) = T
exit2_keeps_idle (MkConfig Idle p2) h = Refl
exit2_keeps_idle (MkConfig Crit p2) Refl impossible

starved : (c : Config) -> P2Only sched -> p1_idle c = T -> p1_idle (runs c sched) = T
starved c P2Nil h = h
starved c (P2Enter p2o2) h = starved (step c Enter2) p2o2 (enter2_keeps_idle c h)
starved c (P2Exit p2o2) h = starved (step c Exit2) p2o2 (exit2_keeps_idle c h)
