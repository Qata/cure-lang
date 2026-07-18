%default total

data Bool' = F | T
data P = Idle | Crit
data Config = MkConfig P P
data Move = Enter1 | Exit1 | Enter2 | Exit2

step : Config -> Move -> Config
step (MkConfig p1 p2) Enter1 = case p2 of
  Idle => MkConfig Crit p2
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit1 = MkConfig Idle p2
step (MkConfig p1 p2) Enter2 = case p1 of
  Idle => MkConfig p1 Crit
  Crit => MkConfig p1 p2
step (MkConfig p1 p2) Exit2 = MkConfig p1 Idle

peq : P -> P -> Bool'
peq Idle Idle = T
peq Idle Crit = F
peq Crit Idle = F
peq Crit Crit = T

andb : Bool' -> Bool' -> Bool'
andb T b = b
andb F b = F

same : Config -> Config -> Bool'
same (MkConfig a1 b1) (MkConfig a2 b2) = andb (peq a1 a2) (peq b1 b2)

pick : Config -> Move
pick (MkConfig Idle Idle) = Enter1
pick (MkConfig Idle Crit) = Exit2
pick (MkConfig Crit p2) = Exit1

deadlock_free : (c : Config) -> same (step c (pick c)) c = F
deadlock_free (MkConfig Idle Idle) = Refl
deadlock_free (MkConfig Idle Crit) = Refl
deadlock_free (MkConfig Crit Idle) = Refl
deadlock_free (MkConfig Crit Crit) = Refl
