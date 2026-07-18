%default total

-- MERGE IS A PERMUTATION OF THE CONCATENATION — count-preservation, the second half of merge-sort
-- correctness (merge_sorted was sortedness). Two lists are permutations iff every element occurs the same
-- number of times, so `count z (merge2 l1 l2) = plus (count z l1) (count z l2)` says merge loses and
-- invents nothing. Same three-function split as merge_sorted; count routes through countPick so the
-- equality test freezes visible (the A6 lesson), and the arithmetic uses plusZero / plusSuccR.

data Bool2 = F | T
data Natt = Z | S Natt
data Listt = LNil | LCons Natt Listt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

data LeDec : (x : Natt) -> (y : Natt) -> Type where
  LeYes : (x2 : Natt) -> (y2 : Natt) -> (leq x2 y2 = T) -> LeDec x2 y2
  LeNo  : (x2 : Natt) -> (y2 : Natt) -> (leq y2 x2 = T) -> LeDec x2 y2

cmp : (x : Natt) -> (y : Natt) -> LeDec x y
cmp Z y = LeYes Z y Refl
cmp (S x2) Z = LeNo (S x2) Z Refl
cmp (S x2) (S y2) = case cmp x2 y2 of
  LeYes _ _ e => LeYes (S x2) (S y2) e
  LeNo _ _ e  => LeNo (S x2) (S y2) e

mergePick : (x : Natt) -> (r1 : Listt) -> (y : Natt) -> (r2 : Listt) -> LeDec x y -> Listt
mergeInto : Natt -> Listt -> Listt -> Listt
merge2 : Listt -> Listt -> Listt
mergePick x r1 y r2 (LeYes _ _ e) = LCons x (merge2 r1 (LCons y r2))
mergePick x r1 y r2 (LeNo _ _ e)  = LCons y (mergeInto x r1 r2)
mergeInto x r1 LNil = LCons x r1
mergeInto x r1 (LCons y r2) = mergePick x r1 y r2 (cmp x y)
merge2 LNil l2 = l2
merge2 (LCons x r1) l2 = mergeInto x r1 l2

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

eqn : Natt -> Natt -> Bool2
eqn Z Z = T
eqn Z (S k) = F
eqn (S j) Z = F
eqn (S j) (S k) = eqn j k

countPick : Natt -> Natt -> Listt -> Bool2 -> Natt
count : Natt -> Listt -> Natt
countPick z w r T = S (count z r)
countPick z w r F = count z r
count z LNil = Z
count z (LCons w r) = countPick z w r (eqn z w)

plusZero : (n : Natt) -> plus n Z = n
plusZero Z = Refl
plusZero (S k) = cong S (plusZero k)

plusSuccR : (a : Natt) -> (b : Natt) -> plus a (S b) = S (plus a b)
plusSuccR Z b = Refl
plusSuccR (S k) b = cong S (plusSuccR k b)

mergePickCount : (z : Natt) -> (x : Natt) -> (r1 : Listt) -> (y : Natt) -> (r2 : Listt) -> (d : LeDec x y) -> count z (mergePick x r1 y r2 d) = plus (count z (LCons x r1)) (count z (LCons y r2))
mergeIntoCount : (z : Natt) -> (x : Natt) -> (r1 : Listt) -> (l2 : Listt) -> count z (mergeInto x r1 l2) = plus (count z (LCons x r1)) (count z l2)
mergeCount : (z : Natt) -> (l1 : Listt) -> (l2 : Listt) -> count z (merge2 l1 l2) = plus (count z l1) (count z l2)
mergePickCount z x r1 y r2 (LeYes _ _ e) with (eqn z x)
  _ | T = cong S (mergeCount z r1 (LCons y r2))
  _ | F = mergeCount z r1 (LCons y r2)
mergePickCount z x r1 y r2 (LeNo _ _ e) with (eqn z y)
  _ | T = trans (cong S (mergeIntoCount z x r1 r2)) (sym (plusSuccR (count z (LCons x r1)) (count z r2)))
  _ | F = mergeIntoCount z x r1 r2
mergeIntoCount z x r1 LNil = sym (plusZero (count z (LCons x r1)))
mergeIntoCount z x r1 (LCons y r2) = mergePickCount z x r1 y r2 (cmp x y)
mergeCount z LNil l2 = Refl
mergeCount z (LCons x r1) l2 = mergeIntoCount z x r1 l2
