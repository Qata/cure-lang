%default total

data OKey = OA | OB | OC
data OBit = OF | OT

slt : OKey -> OKey -> OBit
slt OA OA = OF
slt OA OB = OT
slt OA OC = OT
slt OB OA = OF
slt OB OB = OF
slt OB OC = OT
slt OC OA = OF
slt OC OB = OF
slt OC OC = OF

data EKey = EBot | EFin OKey | ETop

elt : EKey -> EKey -> OBit
elt EBot EBot = OF
elt EBot (EFin y) = OT
elt EBot ETop = OT
elt (EFin x) EBot = OF
elt (EFin x) (EFin y) = slt x y
elt (EFin x) ETop = OT
elt ETop b = OF

data Tri : OKey -> OKey -> Type where
  TLt : slt x k = OT -> Tri x k
  TEq : x = k -> Tri x k
  TGt : slt k x = OT -> Tri x k

owoto : (x : OKey) -> (k : OKey) -> Tri x k
owoto OA OA = TEq Refl
owoto OA OB = TLt Refl
owoto OA OC = TLt Refl
owoto OB OA = TGt Refl
owoto OB OB = TEq Refl
owoto OB OC = TLt Refl
owoto OC OA = TGt Refl
owoto OC OB = TGt Refl
owoto OC OC = TEq Refl

data BST : EKey -> EKey -> Type where
  BLeaf : elt lo hi = OT -> BST lo hi
  BNode : (k : OKey) -> BST lo (EFin k) -> BST (EFin k) hi -> BST lo hi

mutual
  insert : (lo : EKey) -> (hi : EKey) -> (x : OKey) ->
           (elt lo (EFin x) = OT) -> (elt (EFin x) hi = OT) ->
           BST lo hi -> BST lo hi
  insert lo hi x plo phi (BLeaf pf) = BNode x (BLeaf plo) (BLeaf phi)
  insert lo hi x plo phi (BNode k l r) = insert_go lo hi x plo phi k l r (owoto x k)

  insert_go : (lo : EKey) -> (hi : EKey) -> (x : OKey) ->
              (elt lo (EFin x) = OT) -> (elt (EFin x) hi = OT) ->
              (k : OKey) -> BST lo (EFin k) -> BST (EFin k) hi ->
              Tri x k -> BST lo hi
  insert_go lo hi x plo phi k l r (TLt lt) = BNode k (insert lo (EFin k) x plo lt l) r
  insert_go lo hi x plo phi k l r (TEq eq) = BNode k l r
  insert_go lo hi x plo phi k l r (TGt gt) = BNode k l (insert (EFin k) hi x gt phi r)
