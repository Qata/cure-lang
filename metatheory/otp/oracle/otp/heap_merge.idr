%default total

-- A VERIFIED MERGEABLE MIN-HEAP (priority queue). Heap-merge preserves the heap-order invariant. Merge is
-- the same non-structural (two-tree) recursion as list merge, so it uses the three-function total split
-- (merge2 on h1, mergeInto on h2 with h2 in scope, mergePick routing the key comparison). The invariant Heap
-- says each node's key is <= both child roots and both children are heaps; mergeHeap proves merge2 keeps it,
-- with the merged root the min of the two roots (mergeRootLe). The priority-queue primitive used by schedulers.

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
