%default total

data Nat' = Z | S Nat'
data SupState = Running Nat' | GaveUp

on_failure : SupState -> SupState
on_failure GaveUp = GaveUp
on_failure (Running Z) = GaveUp
on_failure (Running (S k)) = Running k

crashes : SupState -> Nat' -> SupState
crashes s Z = s
crashes s (S m) = crashes (on_failure s) m

-- bounded intensity => escalation: S b failures from budget b end in GaveUp.
supervisor_escalates : (b : Nat') -> crashes (Running b) (S b) = GaveUp
supervisor_escalates Z = Refl
supervisor_escalates (S k) = supervisor_escalates k

-- no premature give-up: after exactly b failures the supervisor is still Running Z.
honours_budget : (b : Nat') -> crashes (Running b) b = Running Z
honours_budget Z = Refl
honours_budget (S k) = honours_budget k
