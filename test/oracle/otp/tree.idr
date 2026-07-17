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

data TList = TNil | TCons Nat TList

lapp : TList -> TList -> TList
lapp TNil ys = ys
lapp (TCons h t) ys = TCons h (lapp t ys)

lrev : TList -> TList
lrev TNil = TNil
lrev (TCons h t) = lapp (lrev t) (TCons h TNil)

tcons_cong : (h : Nat) -> a = b -> TCons h a = TCons h b
tcons_cong h Refl = Refl

lapp_cong : (c : TList) -> a = b -> lapp a c = lapp b c
lapp_cong c Refl = Refl

lapp_cong2 : a1 = b1 -> a2 = b2 -> lapp a1 a2 = lapp b1 b2
lapp_cong2 Refl Refl = Refl

lapp_assoc : (xs : TList) -> (ys : TList) -> (zs : TList) -> lapp (lapp xs ys) zs = lapp xs (lapp ys zs)
lapp_assoc TNil ys zs = Refl
lapp_assoc (TCons h t) ys zs = tcons_cong h (lapp_assoc t ys zs)

lapp_nil_r : (xs : TList) -> lapp xs TNil = xs
lapp_nil_r TNil = Refl
lapp_nil_r (TCons h t) = tcons_cong h (lapp_nil_r t)

lrev_app : (xs : TList) -> (ys : TList) -> lrev (lapp xs ys) = lapp (lrev ys) (lrev xs)
lrev_app TNil ys = sym (lapp_nil_r (lrev ys))
lrev_app (TCons h t) ys = trans (lapp_cong (TCons h TNil) (lrev_app t ys)) (lapp_assoc (lrev ys) (lrev t) (TCons h TNil))

lrev_cons : (v : Nat) -> (xs : TList) -> lrev (TCons v xs) = lapp (lrev xs) (TCons v TNil)
lrev_cons v xs = Refl

lapp_cons : (v : Nat) -> (xs : TList) -> lapp (TCons v TNil) xs = TCons v xs
lapp_cons v xs = Refl

flatten : Tree -> TList
flatten Leaf = TNil
flatten (Node l v r) = lapp (flatten l) (TCons v (flatten r))

flatten_mirror : (t : Tree) -> flatten (mirror t) = lrev (flatten t)
flatten_mirror Leaf = Refl
flatten_mirror (Node l v r) = trans (lapp_cong2 (flatten_mirror r) (trans (tcons_cong v (flatten_mirror l)) (sym (lapp_cons v (lrev (flatten l)))))) (sym (trans (lrev_app (flatten l) (TCons v (flatten r))) (trans (lapp_cong (lrev (flatten l)) (lrev_cons v (flatten r))) (lapp_assoc (lrev (flatten r)) (TCons v TNil) (lrev (flatten l))))))
