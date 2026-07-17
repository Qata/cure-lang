%default total

data Tag = TInc | TQuery | TExit
data TagList = TNil | TCons Tag TagList
data Accepted : Tag -> Type where
  AccInc : Accepted TInc
  AccQuery : Accepted TQuery
  AccExit : Accepted TExit
data AllAccepted : TagList -> Type where
  AANil : AllAccepted TNil
  AACons : Accepted t -> AllAccepted rest -> AllAccepted (TCons t rest)
data Trap = Trapping | NotTrapping
data Reason = Normal | Abnormal | Kill
data Proc = Alive TagList TagList Trap | Dead
data WTP : Proc -> Type where
  WTAlive : AllAccepted e -> AllAccepted m -> WTP (Alive e m tr)
  WTDead : WTP Dead
data Step : Reason -> Proc -> Proc -> Type where
  SNormalTrap : Accepted TExit -> Step Normal (Alive e m Trapping) (Alive (TCons TExit e) m Trapping)
  SNormalSurvive : Step Normal (Alive e m NotTrapping) (Alive e m NotTrapping)
  SAbnormalTrap : Accepted TExit -> Step Abnormal (Alive e m Trapping) (Alive (TCons TExit e) m Trapping)
  SAbnormalProp : Step Abnormal (Alive e m NotTrapping) Dead
  SKillTrap : Step Kill (Alive e m Trapping) Dead
  SKillNoTrap : Step Kill (Alive e m NotTrapping) Dead
preservation : WTP b -> Step r b a -> WTP a
preservation wt (SNormalTrap accexit) = case wt of WTAlive ae am => WTAlive (AACons accexit ae) am
preservation wt SNormalSurvive = wt
preservation wt (SAbnormalTrap accexit) = case wt of WTAlive ae am => WTAlive (AACons accexit ae) am
preservation wt SAbnormalProp = WTDead
preservation wt SKillTrap = WTDead
preservation wt SKillNoTrap = WTDead
