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

Uninhabited (F = T) where
  uninhabited Refl impossible

bot : IF
bot = MkIF F F F

orb : B -> B -> B
orb F q = q
orb T q = T

join : IF -> IF -> IF
join (MkIF a b c) (MkIF a2 b2 c2) = MkIF (orb a a2) (orb b b2) (orb c c2)

setbit : Tag -> IF -> IF
setbit TA (MkIF a b c) = MkIF T b c
setbit TB (MkIF a b c) = MkIF a T c
setbit TC (MkIF a b c) = MkIF a b T

getb : IF -> Tag -> B
getb (MkIF a b c) TA = a
getb (MkIF a b c) TB = b
getb (MkIF a b c) TC = c

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

getb_setbit_here : (t : Tag) -> (x : IF) -> getb (setbit t x) t = T
getb_setbit_here TA (MkIF a b c) = Refl
getb_setbit_here TB (MkIF a b c) = Refl
getb_setbit_here TC (MkIF a b c) = Refl

getb_setbit_preserve : (s : Tag) -> (t : Tag) -> (x : IF) -> (getb x t = T) -> getb (setbit s x) t = T
getb_setbit_preserve TA TA (MkIF a b c) e = Refl
getb_setbit_preserve TA TB (MkIF a b c) e = e
getb_setbit_preserve TA TC (MkIF a b c) e = e
getb_setbit_preserve TB TA (MkIF a b c) e = e
getb_setbit_preserve TB TB (MkIF a b c) e = Refl
getb_setbit_preserve TB TC (MkIF a b c) e = e
getb_setbit_preserve TC TA (MkIF a b c) e = e
getb_setbit_preserve TC TB (MkIF a b c) e = e
getb_setbit_preserve TC TC (MkIF a b c) e = Refl

getb_join_left : (x : IF) -> (y : IF) -> (t : Tag) -> (getb x t = T) -> getb (join x y) t = T
getb_join_left (MkIF F b c) (MkIF a2 b2 c2) TA e = absurd e
getb_join_left (MkIF T b c) (MkIF a2 b2 c2) TA e = Refl
getb_join_left (MkIF a F c) (MkIF a2 b2 c2) TB e = absurd e
getb_join_left (MkIF a T c) (MkIF a2 b2 c2) TB e = Refl
getb_join_left (MkIF a b F) (MkIF a2 b2 c2) TC e = absurd e
getb_join_left (MkIF a b T) (MkIF a2 b2 c2) TC e = Refl

getb_join_right : (x : IF) -> (y : IF) -> (t : Tag) -> (getb y t = T) -> getb (join x y) t = T
getb_join_right (MkIF T b c) (MkIF a2 b2 c2) TA e = Refl
getb_join_right (MkIF F b c) (MkIF F b2 c2) TA e = absurd e
getb_join_right (MkIF F b c) (MkIF T b2 c2) TA e = Refl
getb_join_right (MkIF a T c) (MkIF a2 b2 c2) TB e = Refl
getb_join_right (MkIF a F c) (MkIF a2 F c2) TB e = absurd e
getb_join_right (MkIF a F c) (MkIF a2 T c2) TB e = Refl
getb_join_right (MkIF a b T) (MkIF a2 b2 c2) TC e = Refl
getb_join_right (MkIF a b F) (MkIF a2 b2 F) TC e = absurd e
getb_join_right (MkIF a b F) (MkIF a2 b2 T) TC e = Refl

data RBody = RNil | RVar | RSend Tag RBody | RRecv Tag RBody | RSeq RBody RBody

tset : RBody -> IF -> IF
tset RNil        i = bot
tset RVar        i = i
tset (RSend t k) i = setbit t (tset k i)
tset (RRecv t k) i = setbit t (tset k i)
tset (RSeq l r)  i = join (tset l i) (tset r i)

data RSendsIn : RBody -> Tag -> Type where
  RSHere  : RSendsIn (RSend t k) t
  RSSendK : RSendsIn k t -> RSendsIn (RSend y k) t
  RSRecvK : RSendsIn k t -> RSendsIn (RRecv y k) t
  RSSeqL  : RSendsIn l t -> RSendsIn (RSeq l r) t
  RSSeqR  : RSendsIn r t -> RSendsIn (RSeq l r) t

tset_covers : (body : RBody) -> (i : IF) -> (t : Tag) -> RSendsIn body t -> getb (tset body i) t = T
tset_covers (RSend t k) i t RSHere        = getb_setbit_here t (tset k i)
tset_covers (RSend y k) i t (RSSendK s2)  = getb_setbit_preserve y t (tset k i) (tset_covers k i t s2)
tset_covers (RRecv y k) i t (RSRecvK s2)  = getb_setbit_preserve y t (tset k i) (tset_covers k i t s2)
tset_covers (RSeq l r)  i t (RSSeqL s2)   = getb_join_left (tset l i) (tset r i) t (tset_covers l i t s2)
tset_covers (RSeq l r)  i t (RSSeqR s2)   = getb_join_right (tset l i) (tset r i) t (tset_covers r i t s2)
