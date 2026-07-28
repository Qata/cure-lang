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

data LState = Linked | Unlinked
data LinkRef : LState -> Type where
  LinkedTrap : Accepted TExit -> LinkRef Linked
  LinkedNoTrap : LinkRef Linked
  Severed : LinkRef Unlinked

unlink : LinkRef Linked -> LinkRef Unlinked
unlink l = Severed

data Step : Proc -> Proc -> Type where
  SExitTrap : LinkRef Linked -> Accepted TExit -> Step (Alive e m Trapping) (Alive (TCons TExit e) m Trapping)
  SExitProp : LinkRef Linked -> Step (Alive e m NotTrapping) Dead

preservation : WTP b -> Step b a -> WTP a
preservation wt (SExitTrap lref accexit) = case wt of WTAlive ae am => WTAlive (AACons accexit ae) am
preservation wt (SExitProp lref) = WTDead

establish : LinkRef Linked
establish = LinkedTrap AccExit
