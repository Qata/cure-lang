%default total

-- VECTOR CLOCKS FORM A JOIN-SEMILATTICE. The receive-merge of two vector clocks is the componentwise max;
-- this proves it is the LEAST UPPER BOUND of the causal order (vmaxUbL / vmaxUbR / vmaxLub), so vmax is
-- exactly the JOIN. Merge is also commutative, idempotent, and associative (a semilattice) — the algebraic
-- core of CRDT convergence / strong eventual consistency: replicas merging the same updates converge
-- regardless of message order, duplication, or grouping. A local tick advances the clock (tickMono).

data Bool2 = F | T
data Natt = Z | S Natt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

leSucc : (a : Natt) -> leq a (S a) = T
leSucc Z = Refl
leSucc (S k) = leSucc k

max2 : Natt -> Natt -> Natt
max2 Z b = b
max2 (S k) Z = S k
max2 (S k) (S j) = S (max2 k j)

leMaxL : (a : Natt) -> (b : Natt) -> leq a (max2 a b) = T
leMaxL Z b = Refl
leMaxL (S k) Z = leqRefl (S k)
leMaxL (S k) (S j) = leMaxL k j

leMaxR : (a : Natt) -> (b : Natt) -> leq b (max2 a b) = T
leMaxR Z b = leqRefl b
leMaxR (S k) Z = Refl
leMaxR (S k) (S j) = leMaxR k j

maxLub : (a : Natt) -> (b : Natt) -> (c : Natt) -> leq a c = T -> leq b c = T -> leq (max2 a b) c = T
maxLub Z b c ha hb = hb
maxLub (S k) Z c ha hb = ha
maxLub (S k) (S j) Z ha hb = case ha of Refl impossible
maxLub (S k) (S j) (S m) ha hb = maxLub k j m ha hb

maxComm : (a : Natt) -> (b : Natt) -> max2 a b = max2 b a
maxComm Z Z = Refl
maxComm Z (S j) = Refl
maxComm (S k) Z = Refl
maxComm (S k) (S j) = cong S (maxComm k j)

maxIdem : (a : Natt) -> max2 a a = a
maxIdem Z = Refl
maxIdem (S k) = cong S (maxIdem k)

maxAssoc : (a : Natt) -> (b : Natt) -> (c : Natt) -> max2 (max2 a b) c = max2 a (max2 b c)
maxAssoc Z b c = Refl
maxAssoc (S k) Z c = Refl
maxAssoc (S k) (S j) Z = Refl
maxAssoc (S k) (S j) (S m) = cong S (maxAssoc k j m)

andb : Bool2 -> Bool2 -> Bool2
andb T b = b
andb F b = F

andbTrueL : (a : Bool2) -> (b : Bool2) -> andb a b = T -> a = T
andbTrueL T b e = Refl
andbTrueL F b e = case e of Refl impossible

andbTrueR : (a : Bool2) -> (b : Bool2) -> andb a b = T -> b = T
andbTrueR T b e = e
andbTrueR F b e = case e of Refl impossible

andbIntro : (a : Bool2) -> (b : Bool2) -> a = T -> b = T -> andb a b = T
andbIntro T b ea eb = eb
andbIntro F b ea eb = case ea of Refl impossible

data VC = VNil | VCons Natt VC

vcLe : VC -> VC -> Bool2
vcLe VNil v = T
vcLe (VCons x u2) VNil = F
vcLe (VCons x u2) (VCons y v2) = andb (leq x y) (vcLe u2 v2)

vcLeRefl : (u : VC) -> vcLe u u = T
vcLeRefl VNil = Refl
vcLeRefl (VCons x u2) = andbIntro (leq x x) (vcLe u2 u2) (leqRefl x) (vcLeRefl u2)

vconsCong : (x : Natt) -> (y : Natt) -> (u2 : VC) -> (v2 : VC) -> (x = y) -> (u2 = v2) -> VCons x u2 = VCons y v2
vconsCong x y u2 v2 exy euv = trans (cong (\hh => VCons hh u2) exy) (cong (\tt => VCons y tt) euv)

vmax : VC -> VC -> VC
vmax VNil v = v
vmax (VCons x u2) VNil = VCons x u2
vmax (VCons x u2) (VCons y v2) = VCons (max2 x y) (vmax u2 v2)

vmaxUbL : (u : VC) -> (v : VC) -> vcLe u (vmax u v) = T
vmaxUbL VNil v = Refl
vmaxUbL (VCons x u2) VNil = vcLeRefl (VCons x u2)
vmaxUbL (VCons x u2) (VCons y v2) = andbIntro (leq x (max2 x y)) (vcLe u2 (vmax u2 v2)) (leMaxL x y) (vmaxUbL u2 v2)

vmaxUbR : (u : VC) -> (v : VC) -> vcLe v (vmax u v) = T
vmaxUbR VNil v = vcLeRefl v
vmaxUbR (VCons x u2) VNil = Refl
vmaxUbR (VCons x u2) (VCons y v2) = andbIntro (leq y (max2 x y)) (vcLe v2 (vmax u2 v2)) (leMaxR x y) (vmaxUbR u2 v2)

vmaxLub : (u : VC) -> (v : VC) -> (w : VC) -> vcLe u w = T -> vcLe v w = T -> vcLe (vmax u v) w = T
vmaxLub VNil v w hu hv = hv
vmaxLub (VCons x u2) VNil w hu hv = hu
vmaxLub (VCons x u2) (VCons y v2) VNil hu hv = case hu of Refl impossible
vmaxLub (VCons x u2) (VCons y v2) (VCons z w2) hu hv =
  andbIntro (leq (max2 x y) z) (vcLe (vmax u2 v2) w2)
    (maxLub x y z (andbTrueL (leq x z) (vcLe u2 w2) hu) (andbTrueL (leq y z) (vcLe v2 w2) hv))
    (vmaxLub u2 v2 w2 (andbTrueR (leq x z) (vcLe u2 w2) hu) (andbTrueR (leq y z) (vcLe v2 w2) hv))

vmaxComm : (u : VC) -> (v : VC) -> vmax u v = vmax v u
vmaxComm VNil VNil = Refl
vmaxComm VNil (VCons y v2) = Refl
vmaxComm (VCons x u2) VNil = Refl
vmaxComm (VCons x u2) (VCons y v2) = vconsCong (max2 x y) (max2 y x) (vmax u2 v2) (vmax v2 u2) (maxComm x y) (vmaxComm u2 v2)

vmaxIdem : (u : VC) -> vmax u u = u
vmaxIdem VNil = Refl
vmaxIdem (VCons x u2) = vconsCong (max2 x x) x (vmax u2 u2) u2 (maxIdem x) (vmaxIdem u2)

vmaxAssoc : (u : VC) -> (v : VC) -> (w : VC) -> vmax (vmax u v) w = vmax u (vmax v w)
vmaxAssoc VNil v w = Refl
vmaxAssoc (VCons x u2) VNil w = Refl
vmaxAssoc (VCons x u2) (VCons y v2) VNil = Refl
vmaxAssoc (VCons x u2) (VCons y v2) (VCons z w2) =
  vconsCong (max2 (max2 x y) z) (max2 x (max2 y z)) (vmax (vmax u2 v2) w2) (vmax u2 (vmax v2 w2)) (maxAssoc x y z) (vmaxAssoc u2 v2 w2)

tick : Natt -> VC -> VC
tick i VNil = VNil
tick Z (VCons x r) = VCons (S x) r
tick (S k) (VCons x r) = VCons x (tick k r)

tickMono : (i : Natt) -> (v : VC) -> vcLe v (tick i v) = T
tickMono i VNil = Refl
tickMono Z (VCons x r) = andbIntro (leq x (S x)) (vcLe r r) (leSucc x) (vcLeRefl r)
tickMono (S k) (VCons x r) = andbIntro (leq x x) (vcLe r (tick k r)) (leqRefl x) (tickMono k r)
