%default total

data B = F | T
data IF = MkIF B B B

data Imp : B -> B -> Type where
  ImpFF : Imp F F
  ImpFT : Imp F T
  ImpTT : Imp T T

data Sub : IF -> IF -> Type where
  MkSub : Imp a a2 -> Imp b b2 -> Imp c c2 -> Sub (MkIF a b c) (MkIF a2 b2 c2)

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList

data Handles : Tag -> TagList -> Type where
  HHere : Handles t (TCons t rest)
  HThere : Handles t rest -> Handles t (TCons y rest)

data AllHandled : TagList -> TagList -> Type where
  AHNil : AllHandled TNil iface
  AHCons : Handles t iface -> AllHandled rest iface -> AllHandled (TCons t rest) iface

Uninhabited (F = T) where
  uninhabited Refl impossible

denote : IF -> TagList
denote (MkIF F F F) = TNil
denote (MkIF F F T) = TCons TC TNil
denote (MkIF F T F) = TCons TB TNil
denote (MkIF F T T) = TCons TB (TCons TC TNil)
denote (MkIF T F F) = TCons TA TNil
denote (MkIF T F T) = TCons TA (TCons TC TNil)
denote (MkIF T T F) = TCons TA (TCons TB TNil)
denote (MkIF T T T) = TCons TA (TCons TB (TCons TC TNil))

getb : IF -> Tag -> B
getb (MkIF a b c) TA = a
getb (MkIF a b c) TB = b
getb (MkIF a b c) TC = c

handles_a : (b : B) -> (c : B) -> Handles TA (denote (MkIF T b c))
handles_a F F = HHere
handles_a F T = HHere
handles_a T F = HHere
handles_a T T = HHere

handles_b : (a : B) -> (c : B) -> Handles TB (denote (MkIF a T c))
handles_b F F = HHere
handles_b F T = HHere
handles_b T F = HThere HHere
handles_b T T = HThere HHere

handles_c : (a : B) -> (b : B) -> Handles TC (denote (MkIF a b T))
handles_c F F = HHere
handles_c F T = HThere HHere
handles_c T F = HThere HHere
handles_c T T = HThere (HThere HHere)

denote_complete : (x : IF) -> (t : Tag) -> (getb x t = T) -> Handles t (denote x)
denote_complete (MkIF F b c) TA e = absurd e
denote_complete (MkIF T b c) TA e = handles_a b c
denote_complete (MkIF a F c) TB e = absurd e
denote_complete (MkIF a T c) TB e = handles_b a c
denote_complete (MkIF a b F) TC e = absurd e
denote_complete (MkIF a b T) TC e = handles_c a b

getb_mono : (x : IF) -> (y : IF) -> Sub x y -> (t : Tag) -> (getb x t = T) -> (getb y t = T)
getb_mono (MkIF xa xb xc) (MkIF ya yb yc) (MkSub ia ib ic) TA e = case ia of
  ImpFF => absurd e
  ImpFT => absurd e
  ImpTT => Refl
getb_mono (MkIF xa xb xc) (MkIF ya yb yc) (MkSub ia ib ic) TB e = case ib of
  ImpFF => absurd e
  ImpFT => absurd e
  ImpTT => Refl
getb_mono (MkIF xa xb xc) (MkIF ya yb yc) (MkSub ia ib ic) TC e = case ic of
  ImpFF => absurd e
  ImpFT => absurd e
  ImpTT => Refl

sub_allhandled : (x : IF) -> (y : IF) -> Sub x y -> AllHandled (denote x) (denote y)
sub_allhandled (MkIF F F F) (MkIF F F F) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF F F T) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF F T F) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF F T T) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF T F F) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF T F T) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF T T F) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F F) (MkIF T T T) (MkSub _ _ _) = AHNil
sub_allhandled (MkIF F F T) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F F T) (MkIF F F T) (MkSub _ _ _) = AHCons (handles_c F F) AHNil
sub_allhandled (MkIF F F T) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F F T) (MkIF F T T) (MkSub _ _ _) = AHCons (handles_c F T) AHNil
sub_allhandled (MkIF F F T) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F F T) (MkIF T F T) (MkSub _ _ _) = AHCons (handles_c T F) AHNil
sub_allhandled (MkIF F F T) (MkIF T T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F F T) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_c T T) AHNil
sub_allhandled (MkIF F T F) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T F) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T F) (MkIF F T F) (MkSub _ _ _) = AHCons (handles_b F F) AHNil
sub_allhandled (MkIF F T F) (MkIF F T T) (MkSub _ _ _) = AHCons (handles_b F T) AHNil
sub_allhandled (MkIF F T F) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T F) (MkIF T F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T F) (MkIF T T F) (MkSub _ _ _) = AHCons (handles_b T F) AHNil
sub_allhandled (MkIF F T F) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_b T T) AHNil
sub_allhandled (MkIF F T T) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF F T T) (MkSub _ _ _) = AHCons (handles_b F T) (AHCons (handles_c F T) AHNil)
sub_allhandled (MkIF F T T) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF T F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF T T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF F T T) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_b T T) (AHCons (handles_c T T) AHNil)
sub_allhandled (MkIF T F F) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F F) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F F) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F F) (MkIF F T T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F F) (MkIF T F F) (MkSub _ _ _) = AHCons (handles_a F F) AHNil
sub_allhandled (MkIF T F F) (MkIF T F T) (MkSub _ _ _) = AHCons (handles_a F T) AHNil
sub_allhandled (MkIF T F F) (MkIF T T F) (MkSub _ _ _) = AHCons (handles_a T F) AHNil
sub_allhandled (MkIF T F F) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_a T T) AHNil
sub_allhandled (MkIF T F T) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF F T T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF T F T) (MkSub _ _ _) = AHCons (handles_a F T) (AHCons (handles_c T F) AHNil)
sub_allhandled (MkIF T F T) (MkIF T T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T F T) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_a T T) (AHCons (handles_c T T) AHNil)
sub_allhandled (MkIF T T F) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF F T T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF T F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T F) (MkIF T T F) (MkSub _ _ _) = AHCons (handles_a T F) (AHCons (handles_b T F) AHNil)
sub_allhandled (MkIF T T F) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_a T T) (AHCons (handles_b T T) AHNil)
sub_allhandled (MkIF T T T) (MkIF F F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF F F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF F T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF F T T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF T F F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF T F T) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF T T F) (MkSub _ _ _) impossible
sub_allhandled (MkIF T T T) (MkIF T T T) (MkSub _ _ _) = AHCons (handles_a T T) (AHCons (handles_b T T) (AHCons (handles_c T T) AHNil))

