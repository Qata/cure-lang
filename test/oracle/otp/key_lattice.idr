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

kmax : OKey -> OKey -> OKey
kmax a b = case le a b of
  OT => b
  OF => a

kmax_assoc : (a : OKey) -> (b : OKey) -> (c : OKey) -> kmax (kmax a b) c = kmax a (kmax b c)
kmax_assoc OA OA OA = Refl
kmax_assoc OA OA OB = Refl
kmax_assoc OA OA OC = Refl
kmax_assoc OA OB OA = Refl
kmax_assoc OA OB OB = Refl
kmax_assoc OA OB OC = Refl
kmax_assoc OA OC OA = Refl
kmax_assoc OA OC OB = Refl
kmax_assoc OA OC OC = Refl
kmax_assoc OB OA OA = Refl
kmax_assoc OB OA OB = Refl
kmax_assoc OB OA OC = Refl
kmax_assoc OB OB OA = Refl
kmax_assoc OB OB OB = Refl
kmax_assoc OB OB OC = Refl
kmax_assoc OB OC OA = Refl
kmax_assoc OB OC OB = Refl
kmax_assoc OB OC OC = Refl
kmax_assoc OC OA OA = Refl
kmax_assoc OC OA OB = Refl
kmax_assoc OC OA OC = Refl
kmax_assoc OC OB OA = Refl
kmax_assoc OC OB OB = Refl
kmax_assoc OC OB OC = Refl
kmax_assoc OC OC OA = Refl
kmax_assoc OC OC OB = Refl
kmax_assoc OC OC OC = Refl

kmin_absorb : (a : OKey) -> (b : OKey) -> kmin a (kmax a b) = a
kmin_absorb OA OA = Refl
kmin_absorb OA OB = Refl
kmin_absorb OA OC = Refl
kmin_absorb OB OA = Refl
kmin_absorb OB OB = Refl
kmin_absorb OB OC = Refl
kmin_absorb OC OA = Refl
kmin_absorb OC OB = Refl
kmin_absorb OC OC = Refl

kmax_absorb : (a : OKey) -> (b : OKey) -> kmax a (kmin a b) = a
kmax_absorb OA OA = Refl
kmax_absorb OA OB = Refl
kmax_absorb OA OC = Refl
kmax_absorb OB OA = Refl
kmax_absorb OB OB = Refl
kmax_absorb OB OC = Refl
kmax_absorb OC OA = Refl
kmax_absorb OC OB = Refl
kmax_absorb OC OC = Refl

kmin_distrib_kmax : (a : OKey) -> (b : OKey) -> (c : OKey) -> kmin a (kmax b c) = kmax (kmin a b) (kmin a c)
kmin_distrib_kmax OA OA OA = Refl
kmin_distrib_kmax OA OA OB = Refl
kmin_distrib_kmax OA OA OC = Refl
kmin_distrib_kmax OA OB OA = Refl
kmin_distrib_kmax OA OB OB = Refl
kmin_distrib_kmax OA OB OC = Refl
kmin_distrib_kmax OA OC OA = Refl
kmin_distrib_kmax OA OC OB = Refl
kmin_distrib_kmax OA OC OC = Refl
kmin_distrib_kmax OB OA OA = Refl
kmin_distrib_kmax OB OA OB = Refl
kmin_distrib_kmax OB OA OC = Refl
kmin_distrib_kmax OB OB OA = Refl
kmin_distrib_kmax OB OB OB = Refl
kmin_distrib_kmax OB OB OC = Refl
kmin_distrib_kmax OB OC OA = Refl
kmin_distrib_kmax OB OC OB = Refl
kmin_distrib_kmax OB OC OC = Refl
kmin_distrib_kmax OC OA OA = Refl
kmin_distrib_kmax OC OA OB = Refl
kmin_distrib_kmax OC OA OC = Refl
kmin_distrib_kmax OC OB OA = Refl
kmin_distrib_kmax OC OB OB = Refl
kmin_distrib_kmax OC OB OC = Refl
kmin_distrib_kmax OC OC OA = Refl
kmin_distrib_kmax OC OC OB = Refl
kmin_distrib_kmax OC OC OC = Refl

kmax_distrib_kmin : (a : OKey) -> (b : OKey) -> (c : OKey) -> kmax a (kmin b c) = kmin (kmax a b) (kmax a c)
kmax_distrib_kmin OA OA OA = Refl
kmax_distrib_kmin OA OA OB = Refl
kmax_distrib_kmin OA OA OC = Refl
kmax_distrib_kmin OA OB OA = Refl
kmax_distrib_kmin OA OB OB = Refl
kmax_distrib_kmin OA OB OC = Refl
kmax_distrib_kmin OA OC OA = Refl
kmax_distrib_kmin OA OC OB = Refl
kmax_distrib_kmin OA OC OC = Refl
kmax_distrib_kmin OB OA OA = Refl
kmax_distrib_kmin OB OA OB = Refl
kmax_distrib_kmin OB OA OC = Refl
kmax_distrib_kmin OB OB OA = Refl
kmax_distrib_kmin OB OB OB = Refl
kmax_distrib_kmin OB OB OC = Refl
kmax_distrib_kmin OB OC OA = Refl
kmax_distrib_kmin OB OC OB = Refl
kmax_distrib_kmin OB OC OC = Refl
kmax_distrib_kmin OC OA OA = Refl
kmax_distrib_kmin OC OA OB = Refl
kmax_distrib_kmin OC OA OC = Refl
kmax_distrib_kmin OC OB OA = Refl
kmax_distrib_kmin OC OB OB = Refl
kmax_distrib_kmin OC OB OC = Refl
kmax_distrib_kmin OC OC OA = Refl
kmax_distrib_kmin OC OC OB = Refl
kmax_distrib_kmin OC OC OC = Refl
