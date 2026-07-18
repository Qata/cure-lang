%default total

data Nat' = Z | S Nat'
data Bool' = F | T
data AState = AFree | AHeld
data Event = Acquire | Release

leq : Nat' -> Nat' -> Bool'
leq Z b = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

stepA : AState -> Event -> AState
stepA a Acquire = AHeld
stepA a Release = AFree

stepC : Nat' -> Event -> Nat'
stepC n Acquire = case n of
  Z => S Z
  S k => S k
stepC n Release = case n of
  Z => Z
  S k => k

data R : Nat' -> AState -> Type where
  RFree : R Z AFree
  RHeld : R (S Z) AHeld

sim_step : (e : Event) -> R c a -> R (stepC c e) (stepA a e)
sim_step Acquire RFree = RHeld
sim_step Release RFree = RFree
sim_step Acquire RHeld = RHeld
sim_step Release RHeld = RFree

data EList = ENil | ECons Event EList

runC : Nat' -> EList -> Nat'
runC c ENil = c
runC c (ECons e rest) = runC (stepC c e) rest

runA : AState -> EList -> AState
runA a ENil = a
runA a (ECons e rest) = runA (stepA a e) rest

sim_run : (c : Nat') -> (a : AState) -> (es : EList) -> R c a -> R (runC c es) (runA a es)
sim_run c a ENil r = r
sim_run c a (ECons e rest) r = sim_run (stepC c e) (stepA a e) rest (sim_step e r)

refines : (es : EList) -> R (runC Z es) (runA AFree es)
refines es = sim_run Z AFree es RFree

r_bounds : R c a -> leq c (S Z) = T
r_bounds RFree = Refl
r_bounds RHeld = Refl

mutex_by_refinement : (es : EList) -> leq (runC Z es) (S Z) = T
mutex_by_refinement es = r_bounds (refines es)
