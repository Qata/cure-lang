%default total

data Nat' = Z | S Nat'
data Bool' = F | T
data List = LNil | LCons Nat' List

leq : Nat' -> Nat' -> Bool'
leq Z b = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

eq : Nat' -> Nat' -> Bool'
eq Z Z = T
eq Z (S j) = F
eq (S k) Z = F
eq (S k) (S j) = eq k j

data LeDec : Nat' -> Nat' -> Type where
  LeYes : (x2 : Nat') -> (y2 : Nat') -> leq x2 y2 = T -> LeDec x2 y2
  LeNo  : (x2 : Nat') -> (y2 : Nat') -> leq y2 x2 = T -> LeDec x2 y2

cmp : (x : Nat') -> (y : Nat') -> LeDec x y
cmp Z y = LeYes Z y Refl
cmp (S x2) Z = LeNo (S x2) Z Refl
cmp (S x2) (S y2) = case cmp x2 y2 of
  LeYes _ _ e => LeYes (S x2) (S y2) e
  LeNo _ _ e => LeNo (S x2) (S y2) e

mutual
  insert_pick : (x : Nat') -> (y : Nat') -> (rest : List) -> LeDec x y -> List
  insert_pick x y rest (LeYes _ _ e) = LCons x (LCons y rest)
  insert_pick x y rest (LeNo _ _ e) = LCons y (insert x rest)

  insert : Nat' -> List -> List
  insert x LNil = LCons x LNil
  insert x (LCons y rest) = insert_pick x y rest (cmp x y)

sort : List -> List
sort LNil = LNil
sort (LCons x rest) = insert x (sort rest)

bump : Bool' -> Nat' -> Nat'
bump T n = S n
bump F n = n

count : Nat' -> List -> Nat'
count x LNil = Z
count x (LCons y rest) = bump (eq x y) (count x rest)

bump_cong : (b : Bool') -> n1 = n2 -> bump b n1 = bump b n2
bump_cong b e = rewrite e in Refl

bump_swap : (a : Bool') -> (b : Bool') -> (n : Nat') -> bump a (bump b n) = bump b (bump a n)
bump_swap T T n = Refl
bump_swap T F n = Refl
bump_swap F T n = Refl
bump_swap F F n = Refl

insert_count : (z : Nat') -> (x : Nat') -> (l : List) -> count z (insert x l) = count z (LCons x l)
insert_count z x LNil = Refl
insert_count z x (LCons y rest) with (cmp x y)
  insert_count z x (LCons y rest) | LeYes _ _ e = Refl
  insert_count z x (LCons y rest) | LeNo _ _ e = trans (bump_cong (eq z y) (insert_count z x rest)) (bump_swap (eq z y) (eq z x) (count z rest))

sort_count : (z : Nat') -> (l : List) -> count z (sort l) = count z l
sort_count z LNil = Refl
sort_count z (LCons x rest) = trans (insert_count z x (sort rest)) (bump_cong (eq z x) (sort_count z rest))
