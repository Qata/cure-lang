%default total

data Nat' = Z | S Nat'
data Bool' = F | T
data List = LNil | LCons Nat' List

leq : Nat' -> Nat' -> Bool'
leq Z b = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

le_trans : (a : Nat') -> (b : Nat') -> (c : Nat') -> leq a b = T -> leq b c = T -> leq a c = T
le_trans Z b c hab hbc = Refl
le_trans (S a2) Z c Refl hbc impossible
le_trans (S a2) (S b2) Z hab Refl impossible
le_trans (S a2) (S b2) (S c2) hab hbc = le_trans a2 b2 c2 hab hbc

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

data LeAll : Nat' -> List -> Type where
  LANil  : LeAll x LNil
  LACons : (y : Nat') -> (rest : List) -> leq x y = T -> LeAll x rest -> LeAll x (LCons y rest)

data Sorted : List -> Type where
  SNil  : Sorted LNil
  SCons : (x : Nat') -> (rest : List) -> LeAll x rest -> Sorted rest -> Sorted (LCons x rest)

leall_trans : (x : Nat') -> (y : Nat') -> (l : List) -> leq x y = T -> LeAll y l -> LeAll x l
leall_trans x y LNil hxy LANil = LANil
leall_trans x y (LCons z rest) hxy (LACons z rest hyz hl2) = LACons z rest (le_trans x y z hxy hyz) (leall_trans x y rest hxy hl2)

insert_leall : (z : Nat') -> (x : Nat') -> (l : List) -> leq z x = T -> LeAll z l -> LeAll z (insert x l)
insert_leall z x LNil hz hl = LACons x LNil hz LANil
insert_leall z x (LCons y rest) hz hl with (cmp x y)
  insert_leall z x (LCons y rest) hz hl | LeYes _ _ e = LACons x (LCons y rest) hz hl
  insert_leall z x (LCons y rest) hz (LACons y rest hzy hl2) | LeNo _ _ e = LACons y (insert x rest) hzy (insert_leall z x rest hz hl2)

insert_sorted : (x : Nat') -> (l : List) -> Sorted l -> Sorted (insert x l)
insert_sorted x LNil h = SCons x LNil LANil SNil
insert_sorted x (LCons y rest) (SCons y rest la sr) with (cmp x y)
  insert_sorted x (LCons y rest) (SCons y rest la sr) | LeYes _ _ e = SCons x (LCons y rest) (LACons y rest e (leall_trans x y rest e la)) (SCons y rest la sr)
  insert_sorted x (LCons y rest) (SCons y rest la sr) | LeNo _ _ e = SCons y (insert x rest) (insert_leall y x rest e la) (insert_sorted x rest sr)

sort : List -> List
sort LNil = LNil
sort (LCons x rest) = insert x (sort rest)

sort_sorted : (l : List) -> Sorted (sort l)
sort_sorted LNil = SNil
sort_sorted (LCons x rest) = insert_sorted x (sort rest) (sort_sorted rest)
