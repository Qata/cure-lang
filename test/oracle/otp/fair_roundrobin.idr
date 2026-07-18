%default total

data Nat' = Z | S Nat'
data Q = QNil | QCons Nat' Q
data Opt = ONone | OSome Nat'

snat_cong : {a : Nat'} -> {b : Nat'} -> a = b -> S a = S b
snat_cong e = rewrite e in Refl

snoc : Q -> Nat' -> Q
snoc QNil x = QCons x QNil
snoc (QCons y rest) x = QCons y (snoc rest x)

rotate : Q -> Q
rotate QNil = QNil
rotate (QCons x rest) = snoc rest x

head_of : Q -> Opt
head_of QNil = ONone
head_of (QCons x rest) = OSome x

length : Q -> Nat'
length QNil = Z
length (QCons x rest) = S (length rest)

rotate_advances : (x : Nat') -> (y : Nat') -> (rest : Q) -> head_of (rotate (QCons x (QCons y rest))) = OSome y
rotate_advances x y rest = Refl

len_snoc : (q : Q) -> (x : Nat') -> length (snoc q x) = S (length q)
len_snoc QNil x = Refl
len_snoc (QCons y rest) x = snat_cong (len_snoc rest x)

rotate_length : (q : Q) -> length (rotate q) = length q
rotate_length QNil = Refl
rotate_length (QCons x rest) = len_snoc rest x

data InQ : Nat' -> Q -> Type where
  InHead : (rest : Q) -> InQ x (QCons x rest)
  InTail : (y : Nat') -> (rest : Q) -> InQ x rest -> InQ x (QCons y rest)

in_snoc : (x : Nat') -> (y : Nat') -> InQ x q -> InQ x (snoc q y)
in_snoc x y (InHead rest) = InHead (snoc rest y)
in_snoc x y (InTail z rest m2) = InTail z (snoc rest y) (in_snoc x y m2)

in_snoc_last : (q : Q) -> (x : Nat') -> InQ x (snoc q x)
in_snoc_last QNil x = InHead QNil
in_snoc_last (QCons y rest) x = InTail y (snoc rest x) (in_snoc_last rest x)

rotate_mem : (x : Nat') -> InQ x q -> InQ x (rotate q)
rotate_mem x (InHead rest) = in_snoc_last rest x
rotate_mem x (InTail z rest m2) = in_snoc x z m2
