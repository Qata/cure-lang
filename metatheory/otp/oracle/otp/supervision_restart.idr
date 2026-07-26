%default total

data Nat' = Z | S Nat'
data Children = CNil | CCons Nat' Children

-- one_for_all: bump EVERY child's generation.
bump_all : Children -> Children
bump_all CNil = CNil
bump_all (CCons g rest) = CCons (S g) (bump_all rest)

-- one_for_one: bump ONLY the child at index i.
bump_at : Children -> Nat' -> Children
bump_at CNil Z = CNil
bump_at (CCons g rest) Z = CCons (S g) rest
bump_at CNil (S j) = CNil
bump_at (CCons g rest) (S j) = CCons g (bump_at rest j)

-- rest_for_one: bump the child at i and ALL after it.
bump_from : Children -> Nat' -> Children
bump_from cs Z = bump_all cs
bump_from CNil (S j) = CNil
bump_from (CCons g rest) (S j) = CCons g (bump_from rest j)

nth : Children -> Nat' -> Nat'
nth CNil Z = Z
nth (CCons g rest) Z = g
nth CNil (S j) = Z
nth (CCons g rest) (S j) = nth rest j

-- AllBumped(cs, cs2): cs2 is cs with EVERY generation incremented.
data AllBumped : Children -> Children -> Type where
  ABNil : AllBumped CNil CNil
  ABCons : AllBumped rest rest2 -> AllBumped (CCons g rest) (CCons (S g) rest2)

-- one_for_all restarts every child.
one_for_all_correct : (cs : Children) -> AllBumped cs (bump_all cs)
one_for_all_correct CNil = ABNil
one_for_all_correct (CCons g rest) = ABCons (one_for_all_correct rest)

-- rest_for_one at the first child = one_for_all.
rest_for_one_head_is_all : (cs : Children) -> bump_from cs Z = bump_all cs
rest_for_one_head_is_all cs = Refl

-- one_for_one isolates healthy children: a LATER failure leaves the head untouched.
one_for_one_isolates : (g : Nat') -> (rest : Children) -> (i : Nat') ->
                       nth (bump_at (CCons g rest) (S i)) Z = g
one_for_one_isolates g rest i = Refl
