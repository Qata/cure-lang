%default total

data OKey = OA | OB | OC
data OBit = OF | OT

orb : OBit -> OBit -> OBit
orb OF b = b
orb OT b = OT

andb : OBit -> OBit -> OBit
andb OF b = OF
andb OT b = b

cmp : OKey -> OKey -> OBit
cmp OA OA = OF
cmp OA OB = OT
cmp OA OC = OT
cmp OB OA = OF
cmp OB OB = OF
cmp OB OC = OT
cmp OC OA = OF
cmp OC OB = OF
cmp OC OC = OF

keq : OKey -> OKey -> OBit
keq OA OA = OT
keq OA OB = OF
keq OA OC = OF
keq OB OA = OF
keq OB OB = OT
keq OB OC = OF
keq OC OA = OF
keq OC OB = OF
keq OC OC = OT

ofNeOt : OF = OT -> Void
ofNeOt Refl impossible

orb_of_r : (a : OBit) -> orb a OF = a
orb_of_r OF = Refl
orb_of_r OT = Refl

andb_l : (a : OBit) -> (c : OBit) -> andb a c = OT -> a = OT
andb_l OT c e = Refl
andb_l OF c e = void (ofNeOt e)

andb_r : (a : OBit) -> (c : OBit) -> andb a c = OT -> c = OT
andb_r OT c e = e
andb_r OF c e = void (ofNeOt e)

strict_trans : (x : OKey) -> (y : OKey) -> (z : OKey) -> cmp x y = OT -> cmp y z = OT -> cmp x z = OT
strict_trans OA OA OA p q = void (ofNeOt p)
strict_trans OA OB OA p q = void (ofNeOt q)
strict_trans OA OC OA p q = void (ofNeOt q)
strict_trans OA y OB p q = Refl
strict_trans OA y OC p q = Refl
strict_trans OB OA OA p q = void (ofNeOt p)
strict_trans OB OB OA p q = void (ofNeOt p)
strict_trans OB OC OA p q = void (ofNeOt q)
strict_trans OB OA OB p q = void (ofNeOt p)
strict_trans OB OB OB p q = void (ofNeOt p)
strict_trans OB OC OB p q = void (ofNeOt q)
strict_trans OB y OC p q = Refl
strict_trans OC OA z p q = void (ofNeOt p)
strict_trans OC OB z p q = void (ofNeOt p)
strict_trans OC OC z p q = void (ofNeOt p)

strict_neq : (x : OKey) -> (y : OKey) -> cmp x y = OT -> keq x y = OF
strict_neq OA OA p = void (ofNeOt p)
strict_neq OA OB p = Refl
strict_neq OA OC p = Refl
strict_neq OB OA p = void (ofNeOt p)
strict_neq OB OB p = void (ofNeOt p)
strict_neq OB OC p = Refl
strict_neq OC OA p = void (ofNeOt p)
strict_neq OC OB p = void (ofNeOt p)
strict_neq OC OC p = void (ofNeOt p)

strict_neq_r : (x : OKey) -> (y : OKey) -> cmp y x = OT -> keq x y = OF
strict_neq_r OA OA p = void (ofNeOt p)
strict_neq_r OA OB p = void (ofNeOt p)
strict_neq_r OA OC p = void (ofNeOt p)
strict_neq_r OB OA p = Refl
strict_neq_r OB OB p = void (ofNeOt p)
strict_neq_r OB OC p = void (ofNeOt p)
strict_neq_r OC OA p = Refl
strict_neq_r OC OB p = Refl
strict_neq_r OC OC p = void (ofNeOt p)

data Tree = Leaf | Node Tree OKey Tree

mem : OKey -> Tree -> OBit
mem x Leaf = OF
mem x (Node l v r) = case cmp x v of
  OT => mem x l
  OF => case keq x v of
    OT => OT
    OF => mem x r

lmem : OKey -> Tree -> OBit
lmem x Leaf = OF
lmem x (Node l v r) = orb (keq x v) (orb (lmem x l) (lmem x r))

alllt : Tree -> OKey -> OBit
alllt Leaf b = OT
alllt (Node l v r) b = andb (cmp v b) (andb (alllt l b) (alllt r b))

allgt : Tree -> OKey -> OBit
allgt Leaf b = OT
allgt (Node l v r) b = andb (cmp b v) (andb (allgt l b) (allgt r b))

isbst : Tree -> OBit
isbst Leaf = OT
isbst (Node l v r) = andb (isbst l) (andb (isbst r) (andb (alllt l v) (allgt r v)))

below_not_lmem : (x : OKey) -> (b : OKey) -> (t : Tree) -> cmp x b = OT -> allgt t b = OT -> lmem x t = OF
below_not_lmem x b Leaf pxb pgt = Refl
below_not_lmem x b (Node l v r) pxb pgt =
  rewrite strict_neq x v (strict_trans x b v pxb (andb_l (cmp b v) (andb (allgt l b) (allgt r b)) pgt)) in
  rewrite below_not_lmem x b l pxb (andb_l (allgt l b) (allgt r b) (andb_r (cmp b v) (andb (allgt l b) (allgt r b)) pgt)) in
  rewrite below_not_lmem x b r pxb (andb_r (allgt l b) (allgt r b) (andb_r (cmp b v) (andb (allgt l b) (allgt r b)) pgt)) in Refl

above_not_lmem : (x : OKey) -> (b : OKey) -> (t : Tree) -> cmp b x = OT -> alllt t b = OT -> lmem x t = OF
above_not_lmem x b Leaf pbx plt = Refl
above_not_lmem x b (Node l v r) pbx plt =
  rewrite strict_neq_r x v (strict_trans v b x (andb_l (cmp v b) (andb (alllt l b) (alllt r b)) plt) pbx) in
  rewrite above_not_lmem x b l pbx (andb_l (alllt l b) (alllt r b) (andb_r (cmp v b) (andb (alllt l b) (alllt r b)) plt)) in
  rewrite above_not_lmem x b r pbx (andb_r (alllt l b) (alllt r b) (andb_r (cmp v b) (andb (alllt l b) (alllt r b)) plt)) in Refl

mem_eq_lmem : (x : OKey) -> (t : Tree) -> isbst t = OT -> mem x t = lmem x t
mem_eq_lmem x Leaf bst = Refl
mem_eq_lmem OA (Node l OA r) bst = Refl
mem_eq_lmem OB (Node l OB r) bst = Refl
mem_eq_lmem OC (Node l OC r) bst = Refl
mem_eq_lmem OA (Node l OB r) bst =
  rewrite below_not_lmem OA OB r Refl (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) in
  rewrite orb_of_r (lmem OA l) in
  mem_eq_lmem OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)
mem_eq_lmem OA (Node l OC r) bst =
  rewrite below_not_lmem OA OC r Refl (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))) in
  rewrite orb_of_r (lmem OA l) in
  mem_eq_lmem OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)
mem_eq_lmem OB (Node l OC r) bst =
  rewrite below_not_lmem OB OC r Refl (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))) in
  rewrite orb_of_r (lmem OB l) in
  mem_eq_lmem OB l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)
mem_eq_lmem OB (Node l OA r) bst =
  rewrite above_not_lmem OB OA l Refl (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) in
  mem_eq_lmem OB r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))
mem_eq_lmem OC (Node l OA r) bst =
  rewrite above_not_lmem OC OA l Refl (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) in
  mem_eq_lmem OC r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))
mem_eq_lmem OC (Node l OB r) bst =
  rewrite above_not_lmem OC OB l Refl (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) in
  mem_eq_lmem OC r (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))
