%default total

-- MERGE OF TWO SORTED LISTS IS SORTED. Merge interleaves two lists and is not structurally recursive on a
-- single argument; routing it through ONE comparison helper defeats size-change totality (the LCons y r2
-- reconstruction escapes l2's scope). The total formulation splits into three functions: merge2 recurses on
-- l1, mergeInto recurses on l2 (reconstruct-equal preserved), mergePick routes the ordering decision. The
-- proofs mirror that shape and match the decision parameter directly.

data Bool2 = F | T
data Natt = Z | S Natt
data Listt = LNil | LCons Natt Listt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

data Equ : (a : Type) -> a -> a -> Type where
  Refl2 : Equ a x x

leTrans : (a : Natt) -> (b : Natt) -> (c : Natt) -> Equ Bool2 (leq a b) T -> Equ Bool2 (leq b c) T -> Equ Bool2 (leq a c) T
leTrans Z b c hab hbc = Refl2
leTrans (S a2) Z c hab hbc = case hab of Refl2 impossible
leTrans (S a2) (S b2) Z hab hbc = case hbc of Refl2 impossible
leTrans (S a2) (S b2) (S c2) hab hbc = leTrans a2 b2 c2 hab hbc

data LeDec : (x : Natt) -> (y : Natt) -> Type where
  LeYes : (x2 : Natt) -> (y2 : Natt) -> Equ Bool2 (leq x2 y2) T -> LeDec x2 y2
  LeNo  : (x2 : Natt) -> (y2 : Natt) -> Equ Bool2 (leq y2 x2) T -> LeDec x2 y2

cmp : (x : Natt) -> (y : Natt) -> LeDec x y
cmp Z y = LeYes Z y Refl2
cmp (S x2) Z = LeNo (S x2) Z Refl2
cmp (S x2) (S y2) = case cmp x2 y2 of
  LeYes _ _ e => LeYes (S x2) (S y2) e
  LeNo _ _ e  => LeNo (S x2) (S y2) e

data LeAll : (x : Natt) -> (l : Listt) -> Type where
  LANil  : LeAll x LNil
  LACons : (y : Natt) -> (rest : Listt) -> Equ Bool2 (leq x y) T -> LeAll x rest -> LeAll x (LCons y rest)

data Sorted : (l : Listt) -> Type where
  SNil  : Sorted LNil
  SCons : (x : Natt) -> (rest : Listt) -> LeAll x rest -> Sorted rest -> Sorted (LCons x rest)

leallTrans : (x : Natt) -> (y : Natt) -> (l : Listt) -> Equ Bool2 (leq x y) T -> LeAll y l -> LeAll x l
leallTrans x y LNil hxy LANil = LANil
leallTrans x y (LCons z rest) hxy (LACons z rest hyz hl2) = LACons z rest (leTrans x y z hxy hyz) (leallTrans x y rest hxy hl2)

mergePick : (x : Natt) -> (r1 : Listt) -> (y : Natt) -> (r2 : Listt) -> LeDec x y -> Listt
mergeInto : Natt -> Listt -> Listt -> Listt
merge2 : Listt -> Listt -> Listt
mergePick x r1 y r2 (LeYes _ _ e) = LCons x (merge2 r1 (LCons y r2))
mergePick x r1 y r2 (LeNo _ _ e)  = LCons y (mergeInto x r1 r2)
mergeInto x r1 LNil = LCons x r1
mergeInto x r1 (LCons y r2) = mergePick x r1 y r2 (cmp x y)
merge2 LNil l2 = l2
merge2 (LCons x r1) l2 = mergeInto x r1 l2

mergePickLeall : (z : Natt) -> (x : Natt) -> (r1 : Listt) -> (y : Natt) -> (r2 : Listt) -> LeAll z (LCons x r1) -> LeAll z (LCons y r2) -> (d : LeDec x y) -> LeAll z (mergePick x r1 y r2 d)
mergeIntoLeall : (z : Natt) -> (x : Natt) -> (r1 : Listt) -> (l2 : Listt) -> LeAll z (LCons x r1) -> LeAll z l2 -> LeAll z (mergeInto x r1 l2)
mergeLeall : (z : Natt) -> (l1 : Listt) -> (l2 : Listt) -> LeAll z l1 -> LeAll z l2 -> LeAll z (merge2 l1 l2)
mergePickLeall z x r1 y r2 h1 h2 (LeYes _ _ e) = case h1 of
  LACons x3 r13 hzx h1r => LACons x (merge2 r1 (LCons y r2)) hzx (mergeLeall z r1 (LCons y r2) h1r h2)
mergePickLeall z x r1 y r2 h1 h2 (LeNo _ _ e) = case h2 of
  LACons y3 r23 hzy h2r => LACons y (mergeInto x r1 r2) hzy (mergeIntoLeall z x r1 r2 h1 h2r)
mergeIntoLeall z x r1 LNil h1 h2 = h1
mergeIntoLeall z x r1 (LCons y r2) h1 h2 = mergePickLeall z x r1 y r2 h1 h2 (cmp x y)
mergeLeall z LNil l2 h1 h2 = h2
mergeLeall z (LCons x r1) l2 h1 h2 = mergeIntoLeall z x r1 l2 h1 h2

mergePickSorted : (x : Natt) -> (r1 : Listt) -> (y : Natt) -> (r2 : Listt) -> Sorted (LCons x r1) -> Sorted (LCons y r2) -> (d : LeDec x y) -> Sorted (mergePick x r1 y r2 d)
mergeIntoSorted : (x : Natt) -> (r1 : Listt) -> (l2 : Listt) -> Sorted (LCons x r1) -> Sorted l2 -> Sorted (mergeInto x r1 l2)
mergeSorted : (l1 : Listt) -> (l2 : Listt) -> Sorted l1 -> Sorted l2 -> Sorted (merge2 l1 l2)
mergePickSorted x r1 y r2 s1 s2 (LeYes _ _ e) = case s1 of
  SCons x r1 la1 sr1 => case s2 of
    SCons y r2 la2 sr2 => SCons x (merge2 r1 (LCons y r2)) (mergeLeall x r1 (LCons y r2) la1 (LACons y r2 e (leallTrans x y r2 e la2))) (mergeSorted r1 (LCons y r2) sr1 (SCons y r2 la2 sr2))
mergePickSorted x r1 y r2 s1 s2 (LeNo _ _ e) = case s1 of
  SCons x r1 la1 sr1 => case s2 of
    SCons y r2 la2 sr2 => SCons y (mergeInto x r1 r2) (mergeIntoLeall y x r1 r2 (LACons x r1 e (leallTrans y x r1 e la1)) la2) (mergeIntoSorted x r1 r2 (SCons x r1 la1 sr1) sr2)
mergeIntoSorted x r1 LNil s1 s2 = s1
mergeIntoSorted x r1 (LCons y r2) s1 s2 = mergePickSorted x r1 y r2 s1 s2 (cmp x y)
mergeSorted LNil l2 s1 s2 = s2
mergeSorted (LCons x r1) l2 s1 s2 = mergeIntoSorted x r1 l2 s1 s2
