%default total

data Tree = Leaf | Node Tree Nat Tree

add : Nat -> Nat -> Nat
add Z n = n
add (S k) n = S (add k n)

mirror : Tree -> Tree
mirror Leaf = Leaf
mirror (Node l v r) = Node (mirror r) v (mirror l)

size : Tree -> Nat
size Leaf = Z
size (Node l v r) = S (add (size l) (size r))

snat_cong : a = b -> S a = S b
snat_cong Refl = Refl

add_cong : a1 = b1 -> a2 = b2 -> add a1 a2 = add b1 b2
add_cong Refl Refl = Refl

node_cong : (v : Nat) -> l1 = l2 -> r1 = r2 -> Node l1 v r1 = Node l2 v r2
node_cong v Refl Refl = Refl

add_zero_r : (x : Nat) -> add x Z = x
add_zero_r Z = Refl
add_zero_r (S k) = snat_cong (add_zero_r k)

add_succ_r : (x : Nat) -> (y : Nat) -> add x (S y) = S (add x y)
add_succ_r Z y = Refl
add_succ_r (S k) y = snat_cong (add_succ_r k y)

add_comm : (x : Nat) -> (y : Nat) -> add x y = add y x
add_comm Z y = sym (add_zero_r y)
add_comm (S k) y = trans (snat_cong (add_comm k y)) (sym (add_succ_r y k))

mirror_involution : (t : Tree) -> mirror (mirror t) = t
mirror_involution Leaf = Refl
mirror_involution (Node l v r) = node_cong v (mirror_involution l) (mirror_involution r)

size_mirror : (t : Tree) -> size (mirror t) = size t
size_mirror Leaf = Refl
size_mirror (Node l v r) = snat_cong (trans (add_cong (size_mirror r) (size_mirror l)) (add_comm (size r) (size l)))
