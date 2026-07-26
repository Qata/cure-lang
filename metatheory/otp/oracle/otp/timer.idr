%default total

data Tag = TInc | TQuery | TTimeout
data TagList = TNil | TCons Tag TagList

data Accepted : Tag -> Type where
  AccInc : Accepted TInc
  AccQuery : Accepted TQuery
  AccTimeout : Accepted TTimeout

data AllAccepted : TagList -> Type where
  AANil : AllAccepted TNil
  AACons : Accepted t -> AllAccepted rest -> AllAccepted (TCons t rest)

data Config = MkConfig TagList TagList

data WT : Config -> Type where
  MkWT : AllAccepted e -> AllAccepted m -> WT (MkConfig e m)

data TState = Pending | Cancelled

data TimerRef : Tag -> TState -> Type where
  MkTimer : Accepted t -> TimerRef t Pending
  Killed : TimerRef t Cancelled

cancel : TimerRef t Pending -> TimerRef t Cancelled
cancel r = Killed

data Step : Config -> Config -> Type where
  SFire : TimerRef t Pending -> Step (MkConfig e m) (MkConfig (TCons t e) m)

preservation : WT b -> Step b a -> WT a
preservation (MkWT ae am) (SFire (MkTimer acc)) = MkWT (AACons acc ae) am

scheduled_accepted : TimerRef t Pending -> Accepted t
scheduled_accepted (MkTimer a) = a

schedule_timeout : TimerRef TTimeout Pending
schedule_timeout = MkTimer AccTimeout
