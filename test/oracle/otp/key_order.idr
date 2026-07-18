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

orb : OBit -> OBit -> OBit
orb OF b = b
orb OT b = OT

ofNeOt : OF = OT -> Void
ofNeOt Refl impossible

le_refl : (a : OKey) -> le a a = OT
le_refl OA = Refl
le_refl OB = Refl
le_refl OC = Refl

le_total : (a : OKey) -> (b : OKey) -> orb (le a b) (le b a) = OT
le_total OA OA = Refl
le_total OA OB = Refl
le_total OA OC = Refl
le_total OB OA = Refl
le_total OB OB = Refl
le_total OB OC = Refl
le_total OC OA = Refl
le_total OC OB = Refl
le_total OC OC = Refl

le_antisym : (a : OKey) -> (b : OKey) -> le a b = OT -> le b a = OT -> a = b
le_antisym OA OA p q = Refl
le_antisym OA OB p q = void (ofNeOt q)
le_antisym OA OC p q = void (ofNeOt q)
le_antisym OB OA p q = void (ofNeOt p)
le_antisym OB OB p q = Refl
le_antisym OB OC p q = void (ofNeOt q)
le_antisym OC OA p q = void (ofNeOt p)
le_antisym OC OB p q = void (ofNeOt p)
le_antisym OC OC p q = Refl

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

kmin : OKey -> OKey -> OKey
kmin a b = case le a b of
  OT => a
  OF => b
kmax : OKey -> OKey -> OKey
kmax a b = case le a b of
  OT => b
  OF => a

kmin_comm : (a : OKey) -> (b : OKey) -> kmin a b = kmin b a
kmin_comm OA OA = Refl
kmin_comm OA OB = Refl
kmin_comm OA OC = Refl
kmin_comm OB OA = Refl
kmin_comm OB OB = Refl
kmin_comm OB OC = Refl
kmin_comm OC OA = Refl
kmin_comm OC OB = Refl
kmin_comm OC OC = Refl

kmax_comm : (a : OKey) -> (b : OKey) -> kmax a b = kmax b a
kmax_comm OA OA = Refl
kmax_comm OA OB = Refl
kmax_comm OA OC = Refl
kmax_comm OB OA = Refl
kmax_comm OB OB = Refl
kmax_comm OB OC = Refl
kmax_comm OC OA = Refl
kmax_comm OC OB = Refl
kmax_comm OC OC = Refl

kmin_idem : (a : OKey) -> kmin a a = a
kmin_idem OA = Refl
kmin_idem OB = Refl
kmin_idem OC = Refl

kmax_idem : (a : OKey) -> kmax a a = a
kmax_idem OA = Refl
kmax_idem OB = Refl
kmax_idem OC = Refl

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

kmax_upper_l : (a : OKey) -> (b : OKey) -> le a (kmax a b) = OT
kmax_upper_l OA OA = Refl
kmax_upper_l OA OB = Refl
kmax_upper_l OA OC = Refl
kmax_upper_l OB OA = Refl
kmax_upper_l OB OB = Refl
kmax_upper_l OB OC = Refl
kmax_upper_l OC OA = Refl
kmax_upper_l OC OB = Refl
kmax_upper_l OC OC = Refl

kmax_upper_r : (a : OKey) -> (b : OKey) -> le b (kmax a b) = OT
kmax_upper_r OA OA = Refl
kmax_upper_r OA OB = Refl
kmax_upper_r OA OC = Refl
kmax_upper_r OB OA = Refl
kmax_upper_r OB OB = Refl
kmax_upper_r OB OC = Refl
kmax_upper_r OC OA = Refl
kmax_upper_r OC OB = Refl
kmax_upper_r OC OC = Refl

kmin_assoc : (a : OKey) -> (b : OKey) -> (c : OKey) -> kmin (kmin a b) c = kmin a (kmin b c)
kmin_assoc OA OA OA = Refl
kmin_assoc OA OA OB = Refl
kmin_assoc OA OA OC = Refl
kmin_assoc OA OB OA = Refl
kmin_assoc OA OB OB = Refl
kmin_assoc OA OB OC = Refl
kmin_assoc OA OC OA = Refl
kmin_assoc OA OC OB = Refl
kmin_assoc OA OC OC = Refl
kmin_assoc OB OA OA = Refl
kmin_assoc OB OA OB = Refl
kmin_assoc OB OA OC = Refl
kmin_assoc OB OB OA = Refl
kmin_assoc OB OB OB = Refl
kmin_assoc OB OB OC = Refl
kmin_assoc OB OC OA = Refl
kmin_assoc OB OC OB = Refl
kmin_assoc OB OC OC = Refl
kmin_assoc OC OA OA = Refl
kmin_assoc OC OA OB = Refl
kmin_assoc OC OA OC = Refl
kmin_assoc OC OB OA = Refl
kmin_assoc OC OB OB = Refl
kmin_assoc OC OB OC = Refl
kmin_assoc OC OC OA = Refl
kmin_assoc OC OC OB = Refl
kmin_assoc OC OC OC = Refl
