%default total

data Nat' = Z | S Nat'
data Tree = L Nat' Nat' Nat' | Dead

tick : Tree -> Tree
tick Dead = Dead
tick (L o (S k) cap) = L o k cap
tick (L (S j) Z cap) = L j cap cap
tick (L Z Z cap) = Dead

crashes : Tree -> Nat' -> Tree
crashes s Z = s
crashes s (S m) = crashes (tick s) m

-- death is absorbing: escalation past the root is irreversible.
dead_absorbing : (n : Nat') -> crashes Dead n = Dead
dead_absorbing Z = Refl
dead_absorbing (S m) = dead_absorbing m

-- inner-exhaustion cycle: one full inner cycle consumes one outer restart, resets inner to cap.
inner_cycle : (j : Nat') -> (i : Nat') -> (cap : Nat') ->
              crashes (L (S j) i cap) (S i) = L j cap cap
inner_cycle j Z cap = Refl
inner_cycle j (S m) cap = inner_cycle j m cap

-- final cycle => tree death: with the outer budget exhausted, the last inner cycle kills the tree.
final_cycle : (i : Nat') -> (cap : Nat') -> crashes (L Z i cap) (S i) = Dead
final_cycle Z cap = Refl
final_cycle (S m) cap = final_cycle m cap
