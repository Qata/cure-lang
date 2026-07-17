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

orb_comm : (a : B) -> (b : B) -> orb a b = orb b a
orb_comm F F = Refl
orb_comm F T = Refl
orb_comm T F = Refl
orb_comm T T = Refl

orb_idem : (a : B) -> orb a a = a
orb_idem F = Refl
orb_idem T = Refl

union_comm_member : (x : Key) -> (s1 : Set) -> (s2 : Set) -> mem x (union s1 s2) = mem x (union s2 s1)
union_comm_member x s1 s2 = trans (union_member x s1 s2) (trans (orb_comm (mem x s1) (mem x s2)) (sym (union_member x s2 s1)))

union_idem_member : (x : Key) -> (s : Set) -> mem x (union s s) = mem x s
union_idem_member x s = trans (union_member x s s) (orb_idem (mem x s))

orb_assoc : (a : B) -> (b : B) -> (c : B) -> orb (orb a b) c = orb a (orb b c)
orb_assoc F b c = Refl
orb_assoc T b c = Refl

orb_cong_l : (c : B) -> a = a2 -> orb a c = orb a2 c
orb_cong_l c e = cong (\y => orb y c) e

orb_cong_r : (a : B) -> b = b2 -> orb a b = orb a b2
orb_cong_r a e = cong (\y => orb a y) e

union_assoc_member : (x : Key) -> (s1 : Set) -> (s2 : Set) -> (s3 : Set) -> mem x (union (union s1 s2) s3) = mem x (union s1 (union s2 s3))
union_assoc_member x s1 s2 s3 =
  trans (union_member x (union s1 s2) s3)
    (trans (orb_cong_l (mem x s3) (union_member x s1 s2))
      (trans (orb_assoc (mem x s1) (mem x s2) (mem x s3))
        (trans (orb_cong_r (mem x s1) (sym (union_member x s2 s3)))
          (sym (union_member x s1 (union s2 s3))))))
