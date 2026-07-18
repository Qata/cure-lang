%default total

-- HEAP-MERGE PRESERVES THE MULTISET. count z (merge2 h1 h2) = count z h1 + count z h2 for every z, so the
-- mergeable heap loses and invents nothing. The tree analog of list merge-permutation; each node contributes
-- THREE summands (root indicator + left + right), forcing plus-associativity/commutativity juggling (swap12,
-- plusSuccR) the two-summand list case did not need. Corollaries: insert adds exactly one element, deleteMin
-- removes exactly the root. count routes the equality test through countPick so it refines (needs `with`).

data Bool2 = F | T
data Natt = Z | S Natt

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

data Tree = Empty | Node Natt Tree Tree

mergePick : (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (y : Natt) -> (l2 : Tree) -> (r2 : Tree) -> LeDec x y -> Tree
mergeInto : Natt -> Tree -> Tree -> Tree -> Tree
merge2 : Tree -> Tree -> Tree
mergePick x l1 r1 y l2 r2 (LeYes _ _ e) = Node x l1 (merge2 r1 (Node y l2 r2))
mergePick x l1 r1 y l2 r2 (LeNo _ _ e)  = Node y l2 (mergeInto x l1 r1 r2)
mergeInto x l1 r1 Empty = Node x l1 r1
mergeInto x l1 r1 (Node y l2 r2) = mergePick x l1 r1 y l2 r2 (cmp x y)
merge2 Empty h2 = h2
merge2 (Node x l1 r1) h2 = mergeInto x l1 r1 h2

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

plusZero : (n : Natt) -> plus n Z = n
plusZero Z = Refl
plusZero (S k) = cong S (plusZero k)

plusAssoc : (a : Natt) -> (b : Natt) -> (c : Natt) -> plus (plus a b) c = plus a (plus b c)
plusAssoc Z b c = Refl
plusAssoc (S k) b c = cong S (plusAssoc k b c)

plusSuccR : (a : Natt) -> (b : Natt) -> plus a (S b) = S (plus a b)
plusSuccR Z b = Refl
plusSuccR (S k) b = cong S (plusSuccR k b)

plusComm : (a : Natt) -> (b : Natt) -> plus a b = plus b a
plusComm Z b = sym (plusZero b)
plusComm (S k) b = trans (cong S (plusComm k b)) (sym (plusSuccR b k))

plusCongR : (a : Natt) -> (b : Natt) -> (c : Natt) -> b = c -> plus a b = plus a c
plusCongR a b c e = cong (plus a) e

plusCongL : (a : Natt) -> (b : Natt) -> (c : Natt) -> a = b -> plus a c = plus b c
plusCongL a b c e = cong (\w => plus w c) e

swap12 : (a : Natt) -> (b : Natt) -> (c : Natt) -> plus a (plus b c) = plus b (plus a c)
swap12 a b c = trans (sym (plusAssoc a b c)) (trans (plusCongL (plus a b) (plus b a) c (plusComm a b)) (plusAssoc b a c))

data EqDec : (x : Natt) -> (y : Natt) -> Type where
  EqYes : (x2 : Natt) -> (y2 : Natt) -> (x2 = y2) -> EqDec x2 y2
  EqNo  : (x2 : Natt) -> (y2 : Natt) -> EqDec x2 y2

eqDec : (x : Natt) -> (y : Natt) -> EqDec x y
eqDec Z Z = EqYes Z Z Refl
eqDec Z (S k) = EqNo Z (S k)
eqDec (S j) Z = EqNo (S j) Z
eqDec (S j) (S k) = case eqDec j k of
  EqYes _ _ e => EqYes (S j) (S k) (cong S e)
  EqNo _ _    => EqNo (S j) (S k)

countPick : Natt -> Natt -> Tree -> Tree -> EqDec z w -> Natt
count : Natt -> Tree -> Natt
countPick z w l r (EqYes _ _ e) = S (plus (count z l) (count z r))
countPick z w l r (EqNo _ _)    = plus (count z l) (count z r)
count z Empty = Z
count z (Node w l r) = countPick z w l r (eqDec z w)

mergePickCount : (z : Natt) -> (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (y : Natt) -> (l2 : Tree) -> (r2 : Tree) -> (d : LeDec x y) -> count z (mergePick x l1 r1 y l2 r2 d) = plus (count z (Node x l1 r1)) (count z (Node y l2 r2))
mergeIntoCount : (z : Natt) -> (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (h2 : Tree) -> count z (mergeInto x l1 r1 h2) = plus (count z (Node x l1 r1)) (count z h2)
mergeCount : (z : Natt) -> (h1 : Tree) -> (h2 : Tree) -> count z (merge2 h1 h2) = plus (count z h1) (count z h2)
mergePickCount z x l1 r1 y l2 r2 (LeYes _ _ e) with (eqDec z x)
  _ | (EqYes _ _ eq) = cong S (trans (plusCongR (count z l1) (count z (merge2 r1 (Node y l2 r2))) (plus (count z r1) (count z (Node y l2 r2))) (mergeCount z r1 (Node y l2 r2))) (sym (plusAssoc (count z l1) (count z r1) (count z (Node y l2 r2)))))
  _ | (EqNo _ _)     = trans (plusCongR (count z l1) (count z (merge2 r1 (Node y l2 r2))) (plus (count z r1) (count z (Node y l2 r2))) (mergeCount z r1 (Node y l2 r2))) (sym (plusAssoc (count z l1) (count z r1) (count z (Node y l2 r2))))
mergePickCount z x l1 r1 y l2 r2 (LeNo _ _ e) with (eqDec z y)
  _ | (EqYes _ _ eq) = trans (cong S (trans (plusCongR (count z l2) (count z (mergeInto x l1 r1 r2)) (plus (count z (Node x l1 r1)) (count z r2)) (mergeIntoCount z x l1 r1 r2)) (swap12 (count z l2) (count z (Node x l1 r1)) (count z r2)))) (sym (plusSuccR (count z (Node x l1 r1)) (plus (count z l2) (count z r2))))
  _ | (EqNo _ _)     = trans (plusCongR (count z l2) (count z (mergeInto x l1 r1 r2)) (plus (count z (Node x l1 r1)) (count z r2)) (mergeIntoCount z x l1 r1 r2)) (swap12 (count z l2) (count z (Node x l1 r1)) (count z r2))
mergeIntoCount z x l1 r1 Empty = sym (plusZero (count z (Node x l1 r1)))
mergeIntoCount z x l1 r1 (Node y l2 r2) = mergePickCount z x l1 r1 y l2 r2 (cmp x y)
mergeCount z Empty h2 = Refl
mergeCount z (Node x l1 r1) h2 = mergeIntoCount z x l1 r1 h2

singleton : Natt -> Tree
singleton x = Node x Empty Empty

insert : Natt -> Tree -> Tree
insert x h = merge2 (singleton x) h

deleteMin : Tree -> Tree
deleteMin Empty = Empty
deleteMin (Node k l r) = merge2 l r

insertCount : (z : Natt) -> (x : Natt) -> (h : Tree) -> count z (insert x h) = plus (count z (Node x Empty Empty)) (count z h)
insertCount z x h = mergeCount z (Node x Empty Empty) h

deleteMinCount : (z : Natt) -> (k : Natt) -> (l : Tree) -> (r : Tree) -> count z (deleteMin (Node k l r)) = plus (count z l) (count z r)
deleteMinCount z k l r = mergeCount z l r
