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
