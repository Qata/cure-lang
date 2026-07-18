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
data FailRun : Nat -> Phase -> Nat -> Phase -> Type where
  FRDone : FailRun b p b p
  FRMore : Fail b1 p1 bm pm -> FailRun bm pm b2 p2 -> FailRun b1 p1 b2 p2
eventually_down : (n : Nat) -> FailRun n Up Z Down
eventually_down Z = FRMore FShutdown FRDone
eventually_down (S k) = FRMore FRestart (eventually_down k)
run_len : FailRun b1 p1 b2 p2 -> Nat
run_len FRDone = Z
run_len (FRMore f rest) = S (run_len rest)
eventually_down_len : (n : Nat) -> run_len (eventually_down n) = S n
eventually_down_len Z = Refl
eventually_down_len (S k) = cong S (eventually_down_len k)
