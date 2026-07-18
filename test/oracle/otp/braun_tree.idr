%default total

-- BRAUN TREES: balanced-by-construction functional arrays. The Braun invariant is a SIZE-symmetry property --
-- at every node the left subtree's size equals the right's, or is exactly one larger. The classic Braun insert
-- (seat x at the root, push the old root into the right subtree, swap the subtrees) both INCREMENTS the size
-- (sizeInsert) and PRESERVES the invariant (braunInsert) -- the subtree swap trades the balance disjuncts.

data Natt = Z | S Natt

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

snatCong : (a : Natt) -> (b : Natt) -> a = b -> S a = S b
snatCong a b e = cong S e

plusZero : (n : Natt) -> plus n Z = n
plusZero Z = Refl
plusZero (S k) = cong S (plusZero k)

plusSuccR : (a : Natt) -> (b : Natt) -> plus a (S b) = S (plus a b)
plusSuccR Z b = Refl
plusSuccR (S k) b = cong S (plusSuccR k b)

plusComm : (a : Natt) -> (b : Natt) -> plus a b = plus b a
plusComm Z b = sym (plusZero b)
plusComm (S k) b = trans (cong S (plusComm k b)) (sym (plusSuccR b k))

plusCongL : (a : Natt) -> (b : Natt) -> (c : Natt) -> a = b -> plus a c = plus b c
plusCongL a b c e = cong (\w => plus w c) e

data BTree = Leaf | Node Natt BTree BTree

size : BTree -> Natt
size Leaf = Z
size (Node y l r) = S (plus (size l) (size r))

data Bal : (m : Natt) -> (n : Natt) -> Type where
  BalEq : (m2 : Natt) -> (n2 : Natt) -> (m2 = n2) -> Bal m2 n2
  BalHi : (m2 : Natt) -> (n2 : Natt) -> (m2 = S n2) -> Bal m2 n2

data Braun : BTree -> Type where
  BLeaf : Braun Leaf
  BNode : (y : Natt) -> (l : BTree) -> (r : BTree) -> Braun l -> Braun r -> Bal (size l) (size r) -> Braun (Node y l r)

insert : Natt -> BTree -> BTree
insert x Leaf = Node x Leaf Leaf
insert x (Node y l r) = Node x (insert y r) l

sizeInsert : (x : Natt) -> (t : BTree) -> size (insert x t) = S (size t)
sizeInsert x Leaf = Refl
sizeInsert x (Node y l r) =
  trans (snatCong (plus (size (insert y r)) (size l)) (plus (S (size r)) (size l)) (plusCongL (size (insert y r)) (S (size r)) (size l) (sizeInsert y r)))
    (snatCong (S (plus (size r) (size l))) (S (plus (size l) (size r))) (snatCong (plus (size r) (size l)) (plus (size l) (size r)) (plusComm (size r) (size l))))

braunInsert : (x : Natt) -> (t : BTree) -> Braun t -> Braun (insert x t)
braunInsert x Leaf BLeaf = BNode x Leaf Leaf BLeaf BLeaf (BalEq Z Z Refl)
braunInsert x (Node y l r) (BNode y l r bl br bal) = case bal of
  BalEq _ _ e => BNode x (insert y r) l (braunInsert y r br) bl (BalHi (size (insert y r)) (size l) (trans (sizeInsert y r) (snatCong (size r) (size l) (sym e))))
  BalHi _ _ e => BNode x (insert y r) l (braunInsert y r br) bl (BalEq (size (insert y r)) (size l) (trans (sizeInsert y r) (sym e)))
