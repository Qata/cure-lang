%default total

data P = Idle | Crit
data Procs = PNil | PCons P Procs
data Move = Acquire | Release

data AllIdle : Procs -> Type where
  AINil  : AllIdle PNil
  AICons : AllIdle rest -> AllIdle (PCons Idle rest)

data AtMostOne : Procs -> Type where
  AMONil  : AtMostOne PNil
  AMOIdle : AtMostOne rest -> AtMostOne (PCons Idle rest)
  AMOCrit : AllIdle rest -> AtMostOne (PCons Crit rest)

allidle_amo : (procs : Procs) -> AllIdle procs -> AtMostOne procs
allidle_amo PNil ai = AMONil
allidle_amo (PCons Idle rest) (AICons ai2) = AMOIdle (allidle_amo rest ai2)

data IdleDec : Procs -> Type where
  IYes : AllIdle procs -> IdleDec procs
  INo  : IdleDec procs

check_idle : (procs : Procs) -> IdleDec procs
check_idle PNil = IYes AINil
check_idle (PCons Idle rest) = case check_idle rest of
  IYes ai => IYes (AICons ai)
  INo => INo
check_idle (PCons Crit rest) = INo

acquire : Procs -> Procs
acquire PNil = PNil
acquire (PCons p rest) = PCons Crit rest

acquire_amo : (procs : Procs) -> AllIdle procs -> AtMostOne (acquire procs)
acquire_amo PNil ai = AMONil
acquire_amo (PCons Idle rest) (AICons ai2) = AMOCrit ai2

release : Procs -> Procs
release PNil = PNil
release (PCons p rest) = PCons Idle (release rest)

release_ai : (procs : Procs) -> AllIdle (release procs)
release_ai PNil = AINil
release_ai (PCons p rest) = AICons (release_ai rest)

acquire_step : (procs : Procs) -> IdleDec procs -> Procs
acquire_step procs (IYes ai) = acquire procs
acquire_step procs INo = procs

step : Procs -> Move -> Procs
step procs Acquire = acquire_step procs (check_idle procs)
step procs Release = release procs

step_amo : (procs : Procs) -> (m : Move) -> AtMostOne procs -> AtMostOne (step procs m)
step_amo procs Acquire h with (check_idle procs)
  step_amo procs Acquire h | IYes ai = acquire_amo procs ai
  step_amo procs Acquire h | INo = h
step_amo procs Release h = allidle_amo (release procs) (release_ai procs)

data Run : Procs -> Procs -> Type where
  RDone : Run procs procs
  RStep : (m : Move) -> Run (step procs m) procs2 -> Run procs procs2

amo_reachable : (procs : Procs) -> AtMostOne procs -> Run procs procs2 -> AtMostOne procs2
amo_reachable procs h RDone = h
amo_reachable procs h (RStep m run2) = amo_reachable (step procs m) (step_amo procs m h) run2

mutex_safe : (procs : Procs) -> AllIdle procs -> Run procs procs2 -> AtMostOne procs2
mutex_safe procs ai run = amo_reachable procs (allidle_amo procs ai) run
