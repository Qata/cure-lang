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

bot : IF
bot = MkIF F F F

imp_refl : (a : B) -> Imp a a
imp_refl F = ImpFF
imp_refl T = ImpTT

sub_refl : (x : IF) -> Sub x x
sub_refl (MkIF a b c) = MkSub (imp_refl a) (imp_refl b) (imp_refl c)

orb : B -> B -> B
orb F q = q
orb T q = T

orb_mono : Imp p p2 -> Imp q q2 -> Imp (orb p q) (orb p2 q2)
orb_mono ImpFF iq = iq
orb_mono ImpFT iq = case iq of
  ImpFF => ImpFT
  ImpFT => ImpFT
  ImpTT => ImpTT
orb_mono ImpTT iq = ImpTT

join : IF -> IF -> IF
join (MkIF a b c) (MkIF a2 b2 c2) = MkIF (orb a a2) (orb b b2) (orb c c2)

join_mono : (x : IF) -> (y : IF) -> (x2 : IF) -> (y2 : IF) -> Sub x x2 -> Sub y y2 -> Sub (join x y) (join x2 y2)
join_mono (MkIF a b c) (MkIF ay by cy) (MkIF a2 b2 c2) (MkIF ay2 by2 cy2) (MkSub ia ib ic) (MkSub ja jb jc) =
  MkSub (orb_mono ia ja) (orb_mono ib jb) (orb_mono ic jc)

setbit : Tag -> IF -> IF
setbit TA (MkIF a b c) = MkIF T b c
setbit TB (MkIF a b c) = MkIF a T c
setbit TC (MkIF a b c) = MkIF a b T

setbit_mono : (t : Tag) -> (x : IF) -> (y : IF) -> Sub x y -> Sub (setbit t x) (setbit t y)
setbit_mono TA (MkIF a b c) (MkIF a2 b2 c2) (MkSub ia ib ic) = MkSub ImpTT ib ic
setbit_mono TB (MkIF a b c) (MkIF a2 b2 c2) (MkSub ia ib ic) = MkSub ia ImpTT ic
setbit_mono TC (MkIF a b c) (MkIF a2 b2 c2) (MkSub ia ib ic) = MkSub ia ib ImpTT

data RBody = RNil | RVar | RSend Tag RBody | RRecv Tag RBody | RSeq RBody RBody

tset : RBody -> IF -> IF
tset RNil        i = bot
tset RVar        i = i
tset (RSend t k) i = setbit t (tset k i)
tset (RRecv t k) i = setbit t (tset k i)
tset (RSeq l r)  i = join (tset l i) (tset r i)

tset_mono : (body : RBody) -> (x : IF) -> (y : IF) -> Sub x y -> Sub (tset body x) (tset body y)
tset_mono RNil        x y s = sub_refl bot
tset_mono RVar        x y s = s
tset_mono (RSend t k) x y s = setbit_mono t (tset k x) (tset k y) (tset_mono k x y s)
tset_mono (RRecv t k) x y s = setbit_mono t (tset k x) (tset k y) (tset_mono k x y s)
tset_mono (RSeq l r)  x y s = join_mono (tset l x) (tset r x) (tset l y) (tset r y) (tset_mono l x y s) (tset_mono r x y s)


imp_trans : Imp a b -> Imp b c -> Imp a c
imp_trans ImpFF ImpFF = ImpFF
imp_trans ImpFF ImpFT = ImpFT
imp_trans ImpFT ImpTT = ImpFT
imp_trans ImpTT ImpTT = ImpTT

sub_trans : Sub x y -> Sub y z -> Sub x z
sub_trans (MkSub a b c) (MkSub a2 b2 c2) = MkSub (imp_trans a a2) (imp_trans b b2) (imp_trans c c2)

bot_imp : (a : B) -> Imp F a
bot_imp F = ImpFF
bot_imp T = ImpFT

bot_sub : (x : IF) -> Sub (MkIF F F F) x
bot_sub (MkIF a b c) = MkSub (bot_imp a) (bot_imp b) (bot_imp c)

iter : (IF -> IF) -> Nat -> IF
iter f Z = bot
iter f (S k) = f (iter f k)

lfp_le : (f : IF -> IF) -> (mono : (x : IF) -> (y : IF) -> Sub x y -> Sub (f x) (f y)) -> (z : IF) -> Sub (f z) z -> (n : Nat) -> Sub (iter f n) z
lfp_le f mono z hz Z = bot_sub z
lfp_le f mono z hz (S k) = sub_trans (mono (iter f k) z (lfp_le f mono z hz k)) hz
