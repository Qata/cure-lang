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

andb_intro : (a : OBit) -> (c : OBit) -> a = OT -> c = OT -> andb a c = OT
andb_intro OT c pa pc = pc
andb_intro OF c pa pc = void (ofNeOt pa)

allgt_weaken : (t : Tree) -> (v : OKey) -> (w : OKey) -> cmp w v = OT -> allgt t v = OT -> allgt t w = OT
allgt_weaken Leaf v w pwv pgt = Refl
allgt_weaken (Node l u r) v w pwv pgt = andb_intro (cmp w u) (andb (allgt l w) (allgt r w)) (strict_trans w v u pwv (andb_l (cmp v u) (andb (allgt l v) (allgt r v)) pgt)) (andb_intro (allgt l w) (allgt r w) (allgt_weaken l v w pwv (andb_l (allgt l v) (allgt r v) (andb_r (cmp v u) (andb (allgt l v) (allgt r v)) pgt))) (allgt_weaken r v w pwv (andb_r (allgt l v) (allgt r v) (andb_r (cmp v u) (andb (allgt l v) (allgt r v)) pgt))))

alllt_weaken : (t : Tree) -> (v : OKey) -> (w : OKey) -> cmp v w = OT -> alllt t v = OT -> alllt t w = OT
alllt_weaken Leaf v w pvw plt = Refl
alllt_weaken (Node l u r) v w pvw plt = andb_intro (cmp u w) (andb (alllt l w) (alllt r w)) (strict_trans u v w (andb_l (cmp u v) (andb (alllt l v) (alllt r v)) plt) pvw) (andb_intro (alllt l w) (alllt r w) (alllt_weaken l v w pvw (andb_l (alllt l v) (alllt r v) (andb_r (cmp u v) (andb (alllt l v) (alllt r v)) plt))) (alllt_weaken r v w pvw (andb_r (alllt l v) (alllt r v) (andb_r (cmp u v) (andb (alllt l v) (alllt r v)) plt))))

merge : Tree -> Tree -> Tree
merge Leaf r = r
merge (Node ll lv lr) r = Node ll lv (merge lr r)

merge_allgt : (l : Tree) -> (r : Tree) -> (b : OKey) -> allgt l b = OT -> allgt r b = OT -> allgt (merge l r) b = OT
merge_allgt Leaf r b pl pr = pr
merge_allgt (Node ll lv lr) r b pl pr = andb_intro (cmp b lv) (andb (allgt ll b) (allgt (merge lr r) b)) (andb_l (cmp b lv) (andb (allgt ll b) (allgt lr b)) pl) (andb_intro (allgt ll b) (allgt (merge lr r) b) (andb_l (allgt ll b) (allgt lr b) (andb_r (cmp b lv) (andb (allgt ll b) (allgt lr b)) pl)) (merge_allgt lr r b (andb_r (allgt ll b) (allgt lr b) (andb_r (cmp b lv) (andb (allgt ll b) (allgt lr b)) pl)) pr))

merge_alllt : (l : Tree) -> (r : Tree) -> (b : OKey) -> alllt l b = OT -> alllt r b = OT -> alllt (merge l r) b = OT
merge_alllt Leaf r b pl pr = pr
merge_alllt (Node ll lv lr) r b pl pr = andb_intro (cmp lv b) (andb (alllt ll b) (alllt (merge lr r) b)) (andb_l (cmp lv b) (andb (alllt ll b) (alllt lr b)) pl) (andb_intro (alllt ll b) (alllt (merge lr r) b) (andb_l (alllt ll b) (alllt lr b) (andb_r (cmp lv b) (andb (alllt ll b) (alllt lr b)) pl)) (merge_alllt lr r b (andb_r (alllt ll b) (alllt lr b) (andb_r (cmp lv b) (andb (alllt ll b) (alllt lr b)) pl)) pr))

merge_bst : (l : Tree) -> (r : Tree) -> (m : OKey) -> isbst l = OT -> isbst r = OT -> alllt l m = OT -> allgt r m = OT -> isbst (merge l r) = OT
merge_bst Leaf r m bl br plt pgt = br
merge_bst (Node ll lv lr) r m bl br plt pgt =
  let bl_r = andb_r (isbst ll) (andb (isbst lr) (andb (alllt ll lv) (allgt lr lv))) bl
      bl_r2 = andb_r (isbst lr) (andb (alllt ll lv) (allgt lr lv)) bl_r
      plt_r = andb_r (cmp lv m) (andb (alllt ll m) (alllt lr m)) plt in
  andb_intro (isbst ll) (andb (isbst (merge lr r)) (andb (alllt ll lv) (allgt (merge lr r) lv))) (andb_l (isbst ll) (andb (isbst lr) (andb (alllt ll lv) (allgt lr lv))) bl) (andb_intro (isbst (merge lr r)) (andb (alllt ll lv) (allgt (merge lr r) lv)) (merge_bst lr r m (andb_l (isbst lr) (andb (alllt ll lv) (allgt lr lv)) bl_r) br (andb_r (alllt ll m) (alllt lr m) plt_r) pgt) (andb_intro (alllt ll lv) (allgt (merge lr r) lv) (andb_l (alllt ll lv) (allgt lr lv) bl_r2) (merge_allgt lr r lv (andb_r (alllt ll lv) (allgt lr lv) bl_r2) (allgt_weaken r m lv (andb_l (cmp lv m) (andb (alllt ll m) (alllt lr m)) plt) pgt))))

delete : OKey -> Tree -> Tree
delete k Leaf = Leaf
delete k (Node l v r) = case cmp k v of
  OT => Node (delete k l) v r
  OF => case keq k v of
    OT => merge l r
    OF => Node l v (delete k r)

delete_alllt : (k : OKey) -> (t : Tree) -> (b : OKey) -> alllt t b = OT -> alllt (delete k t) b = OT
delete_alllt k Leaf b plt = Refl
delete_alllt OA (Node l OB r) b plt = andb_intro (cmp OB b) (andb (alllt (delete OA l) b) (alllt r b)) (andb_l (cmp OB b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt (delete OA l) b) (alllt r b) (delete_alllt OA l b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt))) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt)))
delete_alllt OA (Node l OC r) b plt = andb_intro (cmp OC b) (andb (alllt (delete OA l) b) (alllt r b)) (andb_l (cmp OC b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt (delete OA l) b) (alllt r b) (delete_alllt OA l b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt))) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt)))
delete_alllt OB (Node l OC r) b plt = andb_intro (cmp OC b) (andb (alllt (delete OB l) b) (alllt r b)) (andb_l (cmp OC b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt (delete OB l) b) (alllt r b) (delete_alllt OB l b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt))) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt)))
delete_alllt OA (Node l OA r) b plt = merge_alllt l r b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt)) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt))
delete_alllt OB (Node l OB r) b plt = merge_alllt l r b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt)) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt))
delete_alllt OC (Node l OC r) b plt = merge_alllt l r b (andb_l (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt)) (andb_r (alllt l b) (alllt r b) (andb_r (cmp OC b) (andb (alllt l b) (alllt r b)) plt))
delete_alllt OB (Node l OA r) b plt = andb_intro (cmp OA b) (andb (alllt l b) (alllt (delete OB r) b)) (andb_l (cmp OA b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt l b) (alllt (delete OB r) b) (andb_l (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt)) (delete_alllt OB r b (andb_r (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt))))
delete_alllt OC (Node l OA r) b plt = andb_intro (cmp OA b) (andb (alllt l b) (alllt (delete OC r) b)) (andb_l (cmp OA b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt l b) (alllt (delete OC r) b) (andb_l (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt)) (delete_alllt OC r b (andb_r (alllt l b) (alllt r b) (andb_r (cmp OA b) (andb (alllt l b) (alllt r b)) plt))))
delete_alllt OC (Node l OB r) b plt = andb_intro (cmp OB b) (andb (alllt l b) (alllt (delete OC r) b)) (andb_l (cmp OB b) (andb (alllt l b) (alllt r b)) plt) (andb_intro (alllt l b) (alllt (delete OC r) b) (andb_l (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt)) (delete_alllt OC r b (andb_r (alllt l b) (alllt r b) (andb_r (cmp OB b) (andb (alllt l b) (alllt r b)) plt))))

delete_allgt : (k : OKey) -> (t : Tree) -> (b : OKey) -> allgt t b = OT -> allgt (delete k t) b = OT
delete_allgt k Leaf b pgt = Refl
delete_allgt OA (Node l OB r) b pgt = andb_intro (cmp b OB) (andb (allgt (delete OA l) b) (allgt r b)) (andb_l (cmp b OB) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt (delete OA l) b) (allgt r b) (delete_allgt OA l b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt))) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt)))
delete_allgt OA (Node l OC r) b pgt = andb_intro (cmp b OC) (andb (allgt (delete OA l) b) (allgt r b)) (andb_l (cmp b OC) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt (delete OA l) b) (allgt r b) (delete_allgt OA l b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt))) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt)))
delete_allgt OB (Node l OC r) b pgt = andb_intro (cmp b OC) (andb (allgt (delete OB l) b) (allgt r b)) (andb_l (cmp b OC) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt (delete OB l) b) (allgt r b) (delete_allgt OB l b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt))) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt)))
delete_allgt OA (Node l OA r) b pgt = merge_allgt l r b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt)) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt))
delete_allgt OB (Node l OB r) b pgt = merge_allgt l r b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt)) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt))
delete_allgt OC (Node l OC r) b pgt = merge_allgt l r b (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt)) (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OC) (andb (allgt l b) (allgt r b)) pgt))
delete_allgt OB (Node l OA r) b pgt = andb_intro (cmp b OA) (andb (allgt l b) (allgt (delete OB r) b)) (andb_l (cmp b OA) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt l b) (allgt (delete OB r) b) (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt)) (delete_allgt OB r b (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt))))
delete_allgt OC (Node l OA r) b pgt = andb_intro (cmp b OA) (andb (allgt l b) (allgt (delete OC r) b)) (andb_l (cmp b OA) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt l b) (allgt (delete OC r) b) (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt)) (delete_allgt OC r b (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OA) (andb (allgt l b) (allgt r b)) pgt))))
delete_allgt OC (Node l OB r) b pgt = andb_intro (cmp b OB) (andb (allgt l b) (allgt (delete OC r) b)) (andb_l (cmp b OB) (andb (allgt l b) (allgt r b)) pgt) (andb_intro (allgt l b) (allgt (delete OC r) b) (andb_l (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt)) (delete_allgt OC r b (andb_r (allgt l b) (allgt r b) (andb_r (cmp b OB) (andb (allgt l b) (allgt r b)) pgt))))

delete_bst : (k : OKey) -> (t : Tree) -> isbst t = OT -> isbst (delete k t) = OT
delete_bst k Leaf bst = Refl
delete_bst OA (Node l OB r) bst = andb_intro (isbst (delete OA l)) (andb (isbst r) (andb (alllt (delete OA l) OB) (allgt r OB))) (delete_bst OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)) (andb_intro (isbst r) (andb (alllt (delete OA l) OB) (allgt r OB)) (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)) (andb_intro (alllt (delete OA l) OB) (allgt r OB) (delete_alllt OA l OB (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)))) (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)))))
delete_bst OA (Node l OC r) bst = andb_intro (isbst (delete OA l)) (andb (isbst r) (andb (alllt (delete OA l) OC) (allgt r OC))) (delete_bst OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_intro (isbst r) (andb (alllt (delete OA l) OC) (allgt r OC)) (andb_l (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_intro (alllt (delete OA l) OC) (allgt r OC) (delete_alllt OA l OC (andb_l (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))) (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))))
delete_bst OB (Node l OC r) bst = andb_intro (isbst (delete OB l)) (andb (isbst r) (andb (alllt (delete OB l) OC) (allgt r OC))) (delete_bst OB l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_intro (isbst r) (andb (alllt (delete OB l) OC) (allgt r OC)) (andb_l (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_intro (alllt (delete OB l) OC) (allgt r OC) (delete_alllt OB l OC (andb_l (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))) (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))))
delete_bst OA (Node l OA r) bst = merge_bst l r OA (andb_l (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst) (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst)) (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (andb_r (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst)))
delete_bst OB (Node l OB r) bst = merge_bst l r OB (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst) (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)) (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)))
delete_bst OC (Node l OC r) bst = merge_bst l r OC (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst) (andb_l (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_l (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))) (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))
delete_bst OB (Node l OA r) bst = andb_intro (isbst l) (andb (isbst (delete OB r)) (andb (alllt l OA) (allgt (delete OB r) OA))) (andb_l (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst) (andb_intro (isbst (delete OB r)) (andb (alllt l OA) (allgt (delete OB r) OA)) (delete_bst OB r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (andb_intro (alllt l OA) (allgt (delete OB r) OA) (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (delete_allgt OB r OA (andb_r (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))))))
delete_bst OC (Node l OA r) bst = andb_intro (isbst l) (andb (isbst (delete OC r)) (andb (alllt l OA) (allgt (delete OC r) OA))) (andb_l (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst) (andb_intro (isbst (delete OC r)) (andb (alllt l OA) (allgt (delete OC r) OA)) (delete_bst OC r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (andb_intro (alllt l OA) (allgt (delete OC r) OA) (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (delete_allgt OC r OA (andb_r (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))))))
delete_bst OC (Node l OB r) bst = andb_intro (isbst l) (andb (isbst (delete OC r)) (andb (alllt l OB) (allgt (delete OC r) OB))) (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst) (andb_intro (isbst (delete OC r)) (andb (alllt l OB) (allgt (delete OC r) OB)) (delete_bst OC r (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) (andb_intro (alllt l OB) (allgt (delete OC r) OB) (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) (delete_allgt OC r OB (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))))))

orb_cong_r : (a : OBit) -> b = b2 -> orb a b = orb a b2
orb_cong_r a e = cong (\y => orb a y) e

orb_cong_l : (c : OBit) -> a = a2 -> orb a c = orb a2 c
orb_cong_l c e = cong (\y => orb y c) e

orb_ofl : (a : OBit) -> orb OF a = a
orb_ofl a = Refl

orb_assoc : (a : OBit) -> (b : OBit) -> (c : OBit) -> orb (orb a b) c = orb a (orb b c)
orb_assoc OF b c = Refl
orb_assoc OT b c = Refl

lmem_merge : (l : Tree) -> (r : Tree) -> (x : OKey) -> lmem x (merge l r) = orb (lmem x l) (lmem x r)
lmem_merge Leaf r x = Refl
lmem_merge (Node ll lv lr) r x = trans (orb_cong_r (keq x lv) (orb_cong_r (lmem x ll) (lmem_merge lr r x))) (sym (trans (orb_assoc (keq x lv) (orb (lmem x ll) (lmem x lr)) (lmem x r)) (orb_cong_r (keq x lv) (orb_assoc (lmem x ll) (lmem x lr) (lmem x r)))))

alllt_absent : (x : OKey) -> (t : Tree) -> alllt t x = OT -> lmem x t = OF
alllt_absent x Leaf plt = Refl
alllt_absent x (Node l v r) plt =
  rewrite strict_neq_r x v (andb_l (cmp v x) (andb (alllt l x) (alllt r x)) plt) in
  rewrite alllt_absent x l (andb_l (alllt l x) (alllt r x) (andb_r (cmp v x) (andb (alllt l x) (alllt r x)) plt)) in
  rewrite alllt_absent x r (andb_r (alllt l x) (alllt r x) (andb_r (cmp v x) (andb (alllt l x) (alllt r x)) plt)) in Refl

allgt_absent : (x : OKey) -> (t : Tree) -> allgt t x = OT -> lmem x t = OF
allgt_absent x Leaf pgt = Refl
allgt_absent x (Node l v r) pgt =
  rewrite strict_neq x v (andb_l (cmp x v) (andb (allgt l x) (allgt r x)) pgt) in
  rewrite allgt_absent x l (andb_l (allgt l x) (allgt r x) (andb_r (cmp x v) (andb (allgt l x) (allgt r x)) pgt)) in
  rewrite allgt_absent x r (andb_r (allgt l x) (allgt r x) (andb_r (cmp x v) (andb (allgt l x) (allgt r x)) pgt)) in Refl

mem_delete_eq : (k : OKey) -> (t : Tree) -> isbst t = OT -> mem k (delete k t) = OF
mem_delete_eq k Leaf bst = Refl
mem_delete_eq OA (Node l OB r) bst = mem_delete_eq OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)
mem_delete_eq OA (Node l OC r) bst = mem_delete_eq OA l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)
mem_delete_eq OB (Node l OC r) bst = mem_delete_eq OB l (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)
mem_delete_eq OB (Node l OA r) bst = mem_delete_eq OB r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))
mem_delete_eq OC (Node l OA r) bst = mem_delete_eq OC r (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))
mem_delete_eq OC (Node l OB r) bst = mem_delete_eq OC r (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))
mem_delete_eq OA (Node l OA r) bst = trans (mem_eq_lmem OA (merge l r) (merge_bst l r OA (andb_l (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst) (andb_l (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst)) (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))) (andb_r (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))))) (trans (lmem_merge l r OA) (trans (orb_cong_l (lmem OA r) (alllt_absent OA l (andb_l (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst))))) (trans (orb_ofl (lmem OA r)) (allgt_absent OA r (andb_r (alllt l OA) (allgt r OA) (andb_r (isbst r) (andb (alllt l OA) (allgt r OA)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OA) (allgt r OA))) bst)))))))
mem_delete_eq OB (Node l OB r) bst = trans (mem_eq_lmem OB (merge l r) (merge_bst l r OB (andb_l (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst) (andb_l (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)) (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))) (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))))) (trans (lmem_merge l r OB) (trans (orb_cong_l (lmem OB r) (alllt_absent OB l (andb_l (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst))))) (trans (orb_ofl (lmem OB r)) (allgt_absent OB r (andb_r (alllt l OB) (allgt r OB) (andb_r (isbst r) (andb (alllt l OB) (allgt r OB)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OB) (allgt r OB))) bst)))))))
mem_delete_eq OC (Node l OC r) bst = trans (mem_eq_lmem OC (merge l r) (merge_bst l r OC (andb_l (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst) (andb_l (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)) (andb_l (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))) (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))))) (trans (lmem_merge l r OC) (trans (orb_cong_l (lmem OC r) (alllt_absent OC l (andb_l (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst))))) (trans (orb_ofl (lmem OC r)) (allgt_absent OC r (andb_r (alllt l OC) (allgt r OC) (andb_r (isbst r) (andb (alllt l OC) (allgt r OC)) (andb_r (isbst l) (andb (isbst r) (andb (alllt l OC) (allgt r OC))) bst)))))))
