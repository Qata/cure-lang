%default total

data OKey = OA | OB | OC
data OBit = OF | OT

le : OKey -> OKey -> OBit
le OA b = OT
le OB OA = OF
le OB OB = OT
le OB OC = OT
le OC OA = OF
le OC OB = OF
le OC OC = OT

kmin : OKey -> OKey -> OKey
kmin a b = case le a b of
  OT => a
  OF => b

ofNeOt : OF = OT -> Void
ofNeOt Refl impossible

le_refl : (a : OKey) -> le a a = OT
le_refl OA = Refl
le_refl OB = Refl
le_refl OC = Refl

le_trans : (a : OKey) -> (b : OKey) -> (c : OKey) -> le a b = OT -> le b c = OT -> le a c = OT
le_trans OA OA OA p q = Refl
le_trans OA OA OB p q = Refl
le_trans OA OA OC p q = Refl
le_trans OA OB OA p q = Refl
le_trans OA OB OB p q = Refl
le_trans OA OB OC p q = Refl
le_trans OA OC OA p q = Refl
le_trans OA OC OB p q = Refl
le_trans OA OC OC p q = Refl
le_trans OB OA OA p q = void (ofNeOt p)
le_trans OB OA OB p q = Refl
le_trans OB OA OC p q = Refl
le_trans OB OB OA p q = void (ofNeOt q)
le_trans OB OB OB p q = Refl
le_trans OB OB OC p q = Refl
le_trans OB OC OA p q = void (ofNeOt q)
le_trans OB OC OB p q = Refl
le_trans OB OC OC p q = Refl
le_trans OC OA OA p q = void (ofNeOt p)
le_trans OC OA OB p q = void (ofNeOt p)
le_trans OC OA OC p q = Refl
le_trans OC OB OA p q = void (ofNeOt p)
le_trans OC OB OB p q = void (ofNeOt p)
le_trans OC OB OC p q = Refl
le_trans OC OC OA p q = void (ofNeOt q)
le_trans OC OC OB p q = void (ofNeOt q)
le_trans OC OC OC p q = Refl

kmin_lower_l : (a : OKey) -> (b : OKey) -> le (kmin a b) a = OT
kmin_lower_l OA OA = Refl
kmin_lower_l OA OB = Refl
kmin_lower_l OA OC = Refl
kmin_lower_l OB OA = Refl
kmin_lower_l OB OB = Refl
kmin_lower_l OB OC = Refl
kmin_lower_l OC OA = Refl
kmin_lower_l OC OB = Refl
kmin_lower_l OC OC = Refl

kmin_lower_r : (a : OKey) -> (b : OKey) -> le (kmin a b) b = OT
kmin_lower_r OA OA = Refl
kmin_lower_r OA OB = Refl
kmin_lower_r OA OC = Refl
kmin_lower_r OB OA = Refl
kmin_lower_r OB OB = Refl
kmin_lower_r OB OC = Refl
kmin_lower_r OC OA = Refl
kmin_lower_r OC OB = Refl
kmin_lower_r OC OC = Refl

data PQ = PNil | PCons OKey PQ

pq_min : OKey -> PQ -> OKey
pq_min seed PNil = seed
pq_min seed (PCons k rest) = kmin k (pq_min seed rest)

insert : OKey -> PQ -> PQ
insert k q = PCons k q

min_le_seed : (seed : OKey) -> (q : PQ) -> le (pq_min seed q) seed = OT
min_le_seed seed PNil = le_refl seed
min_le_seed seed (PCons k rest) = le_trans (kmin k (pq_min seed rest)) (pq_min seed rest) seed (kmin_lower_r k (pq_min seed rest)) (min_le_seed seed rest)

insert_min : (k : OKey) -> (seed : OKey) -> (q : PQ) -> le (pq_min seed (insert k q)) k = OT
insert_min k seed q = kmin_lower_l k (pq_min seed q)
