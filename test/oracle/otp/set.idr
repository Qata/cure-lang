%default total

data Key = KA | KB | KC
data B = F | T

orb : B -> B -> B
orb F b = b
orb T b = T

key_eq : Key -> Key -> B
key_eq KA KA = T
key_eq KA KB = F
key_eq KA KC = F
key_eq KB KA = F
key_eq KB KB = T
key_eq KB KC = F
key_eq KC KA = F
key_eq KC KB = F
key_eq KC KC = T

data Set = SetNil | SetCons Key Set

mem : Key -> Set -> B
mem x SetNil = F
mem x (SetCons k rest) = case key_eq x k of
  T => T
  F => mem x rest

union : Set -> Set -> Set
union SetNil s2 = s2
union (SetCons k rest) s2 = SetCons k (union rest s2)

union_member : (x : Key) -> (s1 : Set) -> (s2 : Set) -> mem x (union s1 s2) = orb (mem x s1) (mem x s2)
union_member x SetNil s2 = Refl
union_member KA (SetCons KA rest) s2 = Refl
union_member KA (SetCons KB rest) s2 = union_member KA rest s2
union_member KA (SetCons KC rest) s2 = union_member KA rest s2
union_member KB (SetCons KA rest) s2 = union_member KB rest s2
union_member KB (SetCons KB rest) s2 = Refl
union_member KB (SetCons KC rest) s2 = union_member KB rest s2
union_member KC (SetCons KA rest) s2 = union_member KC rest s2
union_member KC (SetCons KB rest) s2 = union_member KC rest s2
union_member KC (SetCons KC rest) s2 = Refl
