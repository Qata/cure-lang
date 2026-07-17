%default total

data Phase = Up | Down
data Sup : Nat -> Phase -> Type where
  Alive : Sup n Up
  Stopped : Sup Z Down
data Fail : Nat -> Phase -> Nat -> Phase -> Type where
  FRestart : Fail (S n) Up n Up
  FShutdown : Fail Z Up Z Down
on_fail : Sup b1 p1 -> Fail b1 p1 b2 p2 -> Sup b2 p2
on_fail sup FRestart = Alive
on_fail sup FShutdown = Stopped
