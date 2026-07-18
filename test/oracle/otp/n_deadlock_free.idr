%default total

data Bool' = F | T
data P = Idle | Crit
data Procs = PNil | PCons P Procs

neg : Bool' -> Bool'
neg F = T
neg T = F

all_idle_b : Procs -> Bool'
all_idle_b PNil = T
all_idle_b (PCons Idle rest) = all_idle_b rest
all_idle_b (PCons Crit rest) = F

acquire : Procs -> Procs
acquire PNil = PNil
acquire (PCons p rest) = PCons Crit rest

release : Procs -> Procs
release PNil = PNil
release (PCons p rest) = PCons Idle (release rest)

release_all_idle : (procs : Procs) -> all_idle_b (release procs) = T
release_all_idle PNil = Refl
release_all_idle (PCons p rest) = release_all_idle rest

stepped : Procs -> Bool' -> Procs
stepped procs T = acquire procs
stepped procs F = release procs

deadlock_step : (p : P) -> (rest : Procs) -> (b : Bool') -> all_idle_b (stepped (PCons p rest) b) = neg b
deadlock_step p rest T = Refl
deadlock_step p rest F = release_all_idle rest

deadlock_free : (p : P) -> (rest : Procs) -> all_idle_b (stepped (PCons p rest) (all_idle_b (PCons p rest))) = neg (all_idle_b (PCons p rest))
deadlock_free p rest = deadlock_step p rest (all_idle_b (PCons p rest))
