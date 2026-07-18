%default total

-- A VERIFIED PRIORITY QUEUE on the mergeable min-heap. insert and deleteMin are defined in terms of merge2
-- (insert = merge with a singleton; deleteMin = merge the root's two subtrees) and PRESERVE the heap
-- invariant. The defining correctness is min-at-root: heapBelow proves a heap's root is a lower bound of
-- EVERY element, so findMin returns the minimum (findMinIsMin: findMin h <= every element of h).

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

leTrans : (a : Natt) -> (b : Natt) -> (c : Natt) -> leq a b = T -> leq b c = T -> leq a c = T
leTrans Z b c hab hbc = Refl
leTrans (S a2) Z c hab hbc = case hab of Refl impossible
leTrans (S a2) (S b2) Z hab hbc = case hbc of Refl impossible
leTrans (S a2) (S b2) (S c2) hab hbc = leTrans a2 b2 c2 hab hbc

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

rootLe : Natt -> Tree -> Bool2
rootLe x Empty = T
rootLe x (Node y l r) = leq x y

data Heap : Tree -> Type where
  HEmpty : Heap Empty
  HNode  : (x : Natt) -> (l : Tree) -> (r : Tree) -> (rootLe x l = T) -> (rootLe x r = T) -> Heap l -> Heap r -> Heap (Node x l r)

mergePick : (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (y : Natt) -> (l2 : Tree) -> (r2 : Tree) -> LeDec x y -> Tree
mergeInto : Natt -> Tree -> Tree -> Tree -> Tree
merge2 : Tree -> Tree -> Tree
mergePick x l1 r1 y l2 r2 (LeYes _ _ e) = Node x l1 (merge2 r1 (Node y l2 r2))
mergePick x l1 r1 y l2 r2 (LeNo _ _ e)  = Node y l2 (mergeInto x l1 r1 r2)
mergeInto x l1 r1 Empty = Node x l1 r1
mergeInto x l1 r1 (Node y l2 r2) = mergePick x l1 r1 y l2 r2 (cmp x y)
merge2 Empty h2 = h2
merge2 (Node x l1 r1) h2 = mergeInto x l1 r1 h2

mergePickRle : (z : Natt) -> (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (y : Natt) -> (l2 : Tree) -> (r2 : Tree) -> (rootLe z (Node x l1 r1) = T) -> (rootLe z (Node y l2 r2) = T) -> (d : LeDec x y) -> rootLe z (mergePick x l1 r1 y l2 r2 d) = T
mergeIntoRle : (z : Natt) -> (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (h2 : Tree) -> (rootLe z (Node x l1 r1) = T) -> (rootLe z h2 = T) -> rootLe z (mergeInto x l1 r1 h2) = T
mergeRootLe : (z : Natt) -> (h1 : Tree) -> (h2 : Tree) -> (rootLe z h1 = T) -> (rootLe z h2 = T) -> rootLe z (merge2 h1 h2) = T
mergePickRle z x l1 r1 y l2 r2 hz1 hz2 (LeYes _ _ e) = hz1
mergePickRle z x l1 r1 y l2 r2 hz1 hz2 (LeNo _ _ e)  = hz2
mergeIntoRle z x l1 r1 Empty hz1 hz2 = hz1
mergeIntoRle z x l1 r1 (Node y l2 r2) hz1 hz2 = mergePickRle z x l1 r1 y l2 r2 hz1 hz2 (cmp x y)
mergeRootLe z Empty h2 hz1 hz2 = hz2
mergeRootLe z (Node x l1 r1) h2 hz1 hz2 = mergeIntoRle z x l1 r1 h2 hz1 hz2

mergePickHeap : (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (y : Natt) -> (l2 : Tree) -> (r2 : Tree) -> Heap (Node x l1 r1) -> Heap (Node y l2 r2) -> (d : LeDec x y) -> Heap (mergePick x l1 r1 y l2 r2 d)
mergeIntoHeap : (x : Natt) -> (l1 : Tree) -> (r1 : Tree) -> (h2 : Tree) -> Heap (Node x l1 r1) -> Heap h2 -> Heap (mergeInto x l1 r1 h2)
mergeHeap : (h1 : Tree) -> (h2 : Tree) -> Heap h1 -> Heap h2 -> Heap (merge2 h1 h2)
mergePickHeap x l1 r1 y l2 r2 s1 s2 (LeYes _ _ e) = case s1 of
  HNode x l1 r1 hxl1 hxr1 hl1 hr1 => HNode x l1 (merge2 r1 (Node y l2 r2)) hxl1 (mergeRootLe x r1 (Node y l2 r2) hxr1 e) hl1 (mergeHeap r1 (Node y l2 r2) hr1 s2)
mergePickHeap x l1 r1 y l2 r2 s1 s2 (LeNo _ _ e) = case s2 of
  HNode y l2 r2 hyl2 hyr2 hl2 hr2 => HNode y l2 (mergeInto x l1 r1 r2) hyl2 (mergeIntoRle y x l1 r1 r2 e hyr2) hl2 (mergeIntoHeap x l1 r1 r2 s1 hr2)
mergeIntoHeap x l1 r1 Empty s1 s2 = s1
mergeIntoHeap x l1 r1 (Node y l2 r2) s1 s2 = mergePickHeap x l1 r1 y l2 r2 s1 s2 (cmp x y)
mergeHeap Empty h2 s1 s2 = s2
mergeHeap (Node x l1 r1) h2 s1 s2 = mergeIntoHeap x l1 r1 h2 s1 s2

data Below : (b : Natt) -> (h : Tree) -> Type where
  BEmpty : Below b Empty
  BNode  : (x : Natt) -> (l : Tree) -> (r : Tree) -> (leq b x = T) -> Below b l -> Below b r -> Below b (Node x l r)

rootLeTrans : (b : Natt) -> (x : Natt) -> (l : Tree) -> (leq b x = T) -> (rootLe x l = T) -> rootLe b l = T
rootLeTrans b x Empty hbx hxl = Refl
rootLeTrans b x (Node z ll rr) hbx hxl = leTrans b x z hbx hxl

heapBelow : (b : Natt) -> (h : Tree) -> (rootLe b h = T) -> Heap h -> Below b h
heapBelow b Empty hbh HEmpty = BEmpty
heapBelow b (Node x l r) hbh (HNode x l r hxl hxr shl shr) =
  BNode x l r hbh (heapBelow b l (rootLeTrans b x l hbh hxl) shl) (heapBelow b r (rootLeTrans b x r hbh hxr) shr)

singleton : Natt -> Tree
singleton x = Node x Empty Empty

insert : Natt -> Tree -> Tree
insert x h = merge2 (singleton x) h

deleteMin : Tree -> Tree
deleteMin Empty = Empty
deleteMin (Node k l r) = merge2 l r

findMin : Tree -> Natt
findMin Empty = Z
findMin (Node k l r) = k

hSingleton : (x : Natt) -> Heap (singleton x)
hSingleton x = HNode x Empty Empty Refl Refl HEmpty HEmpty

insertHeap : (x : Natt) -> (h : Tree) -> Heap h -> Heap (insert x h)
insertHeap x h sh = mergeHeap (singleton x) h (hSingleton x) sh

deleteMinHeap : (h : Tree) -> Heap h -> Heap (deleteMin h)
deleteMinHeap Empty HEmpty = HEmpty
deleteMinHeap (Node k l r) (HNode k l r hkl hkr shl shr) = mergeHeap l r shl shr

findMinIsMin : (h : Tree) -> Heap h -> Below (findMin h) h
findMinIsMin Empty HEmpty = BEmpty
findMinIsMin (Node x l r) (HNode x l r hxl hxr shl shr) = heapBelow x (Node x l r) (leqRefl x) (HNode x l r hxl hxr shl shr)
