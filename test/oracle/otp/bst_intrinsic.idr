%default total

data Key = Alpha | Beta | Gamma
data Bit = No | Yes

strictLess : Key -> Key -> Bit
strictLess Alpha Alpha = No
strictLess Alpha Beta = Yes
strictLess Alpha Gamma = Yes
strictLess Beta Alpha = No
strictLess Beta Beta = No
strictLess Beta Gamma = Yes
strictLess Gamma Alpha = No
strictLess Gamma Beta = No
strictLess Gamma Gamma = No

data Bound = BelowAll | Only Key | AboveAll

boundLess : Bound -> Bound -> Bit
boundLess BelowAll BelowAll = No
boundLess BelowAll (Only y) = Yes
boundLess BelowAll AboveAll = Yes
boundLess (Only x) BelowAll = No
boundLess (Only x) (Only y) = strictLess x y
boundLess (Only x) AboveAll = Yes
boundLess AboveAll hi = No

data Trichotomy : Key -> Key -> Type where
  TriLess : strictLess x k = Yes -> Trichotomy x k
  TriEqual : x = k -> Trichotomy x k
  TriGreater : strictLess k x = Yes -> Trichotomy x k

compareKeys : (x : Key) -> (k : Key) -> Trichotomy x k
compareKeys Alpha Alpha = TriEqual Refl
compareKeys Alpha Beta = TriLess Refl
compareKeys Alpha Gamma = TriLess Refl
compareKeys Beta Alpha = TriGreater Refl
compareKeys Beta Beta = TriEqual Refl
compareKeys Beta Gamma = TriLess Refl
compareKeys Gamma Alpha = TriGreater Refl
compareKeys Gamma Beta = TriGreater Refl
compareKeys Gamma Gamma = TriEqual Refl

data SearchTree : Bound -> Bound -> Type where
  Leaf : boundLess lo hi = Yes -> SearchTree lo hi
  Branch : (k : Key) -> SearchTree lo (Only k) -> SearchTree (Only k) hi -> SearchTree lo hi

insert : (lo : Bound) -> (hi : Bound) -> (x : Key) ->
         (boundLess lo (Only x) = Yes) -> (boundLess (Only x) hi = Yes) ->
         SearchTree lo hi -> SearchTree lo hi
insert lo hi x below above (Leaf pf) = Branch x (Leaf below) (Leaf above)
insert lo hi x below above (Branch k l r) = case compareKeys x k of
  TriLess less => Branch k (insert lo (Only k) x below less l) r
  TriEqual eq => Branch k l r
  TriGreater greater => Branch k l (insert (Only k) hi x greater above r)
