%default total

data Bool' = F | T
data P = Idle | Crit
data Config = MkConfig P P
data Move = Enter1 | Exit1 | Enter2 | Exit2

mutex : Config -> Bool'
mutex (MkConfig Idle p2) = T
mutex (MkConfig Crit Idle) = T
mutex (MkConfig Crit Crit) = F

step : Config -> Move -> Config
step (MkConfig p1 p2) Enter1 = case p2 of
  Idle => MkConfig Crit p2
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit1 = MkConfig Idle p2
step (MkConfig p1 p2) Enter2 = case p1 of
  Idle => MkConfig p1 Crit
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit2 = MkConfig p1 Idle

mutex_step : (c : Config) -> (m : Move) -> mutex c = T -> mutex (step c m) = T
mutex_step (MkConfig p1 Idle) Enter1 h = Refl
mutex_step (MkConfig Idle Crit) Enter1 h = Refl
mutex_step (MkConfig Crit Crit) Enter1 Refl impossible
mutex_step (MkConfig p1 p2) Exit1 h = Refl
mutex_step (MkConfig Idle p2) Enter2 h = Refl
mutex_step (MkConfig Crit Idle) Enter2 h = Refl
mutex_step (MkConfig Crit Crit) Enter2 Refl impossible
mutex_step (MkConfig Idle p2) Exit2 h = Refl
mutex_step (MkConfig Crit p2) Exit2 h = Refl

data Run : Config -> Config -> Type where
  RDone : Run c c
  RStep : (m : Move) -> Run (step c m) c2 -> Run c c2

mutex_reachable : (c : Config) -> mutex c = T -> Run c c2 -> mutex c2 = T
mutex_reachable c h RDone = h
mutex_reachable c h (RStep m run2) = mutex_reachable (step c m) (mutex_step c m h) run2

mutex_safe : Run (MkConfig Idle Idle) c2 -> mutex c2 = T
mutex_safe run = mutex_reachable (MkConfig Idle Idle) Refl run
