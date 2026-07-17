%default total

data Key = KA | KB | KC
data Cmp = KLt | KEq | KGt
data B = F | T

kcmp : Key -> Key -> Cmp
kcmp KA KA = KEq
kcmp KA KB = KLt
kcmp KA KC = KLt
kcmp KB KA = KGt
kcmp KB KB = KEq
kcmp KB KC = KLt
kcmp KC KA = KGt
kcmp KC KB = KGt
kcmp KC KC = KEq

data Tree = Leaf | Node Tree Key Tree

member : Key -> Tree -> B
member k Leaf = F
member k (Node l v r) = case kcmp k v of
  KLt => member k l
  KEq => T
  KGt => member k r

insert : Key -> Tree -> Tree
insert k Leaf = Node Leaf k Leaf
insert k (Node l v r) = case kcmp k v of
  KLt => Node (insert k l) v r
  KEq => Node l v r
  KGt => Node l v (insert k r)

member_leaf : (k : Key) -> member k Leaf = F
member_leaf k = Refl

insert_member : (k : Key) -> (t : Tree) -> member k (insert k t) = T
insert_member KA Leaf = Refl
insert_member KB Leaf = Refl
insert_member KC Leaf = Refl
insert_member KA (Node l KA r) = Refl
insert_member KA (Node l KB r) = insert_member KA l
insert_member KA (Node l KC r) = insert_member KA l
insert_member KB (Node l KA r) = insert_member KB r
insert_member KB (Node l KB r) = Refl
insert_member KB (Node l KC r) = insert_member KB l
insert_member KC (Node l KA r) = insert_member KC r
insert_member KC (Node l KB r) = insert_member KC r
insert_member KC (Node l KC r) = Refl

insert_preserves : (x : Key) -> (k : Key) -> (t : Tree) -> member x t = T -> member x (insert k t) = T
insert_preserves x k Leaf Refl impossible
insert_preserves KA KA (Node l KA r) e = Refl
insert_preserves KA KB (Node l KA r) e = Refl
insert_preserves KA KC (Node l KA r) e = Refl
insert_preserves KA KA (Node l KB r) e = insert_preserves KA KA l e
insert_preserves KA KB (Node l KB r) e = e
insert_preserves KA KC (Node l KB r) e = e
insert_preserves KA KA (Node l KC r) e = insert_preserves KA KA l e
insert_preserves KA KB (Node l KC r) e = insert_preserves KA KB l e
insert_preserves KA KC (Node l KC r) e = e
insert_preserves KB KA (Node l KA r) e = e
insert_preserves KB KB (Node l KA r) e = insert_preserves KB KB r e
insert_preserves KB KC (Node l KA r) e = insert_preserves KB KC r e
insert_preserves KB KA (Node l KB r) e = Refl
insert_preserves KB KB (Node l KB r) e = Refl
insert_preserves KB KC (Node l KB r) e = Refl
insert_preserves KB KA (Node l KC r) e = insert_preserves KB KA l e
insert_preserves KB KB (Node l KC r) e = insert_preserves KB KB l e
insert_preserves KB KC (Node l KC r) e = e
insert_preserves KC KA (Node l KA r) e = e
insert_preserves KC KB (Node l KA r) e = insert_preserves KC KB r e
insert_preserves KC KC (Node l KA r) e = insert_preserves KC KC r e
insert_preserves KC KA (Node l KB r) e = e
insert_preserves KC KB (Node l KB r) e = e
insert_preserves KC KC (Node l KB r) e = insert_preserves KC KC r e
insert_preserves KC KA (Node l KC r) e = Refl
insert_preserves KC KB (Node l KC r) e = Refl
insert_preserves KC KC (Node l KC r) e = Refl
