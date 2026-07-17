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

data Proc = Alive TagList TagList Trap | Dead

data WTP : Proc -> Type where
  WTAlive : AllAccepted e -> AllAccepted m -> WTP (Alive e m tr)
  WTDead : WTP Dead

data Link : Trap -> Type where
  LinkTrap : Accepted TExit -> Link Trapping
  LinkNoTrap : Link NotTrapping

data Step : Proc -> Proc -> Type where
  SExitTrap : Accepted TExit -> Step (Alive e m Trapping) (Alive (TCons TExit e) m Trapping)
  SExitProp : Step (Alive e m NotTrapping) Dead

preservation : WTP b -> Step b a -> WTP a
preservation (WTAlive ae am) (SExitTrap accexit) = WTAlive (AACons accexit ae) am
preservation _ SExitProp = WTDead

trap_accepts : Link Trapping -> Accepted TExit
trap_accepts (LinkTrap a) = a

establish_trap : Link Trapping
establish_trap = LinkTrap AccExit

establish_notrap : Link NotTrapping
establish_notrap = LinkNoTrap
