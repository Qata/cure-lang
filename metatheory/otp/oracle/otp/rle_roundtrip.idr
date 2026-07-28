%default total

-- RUN-LENGTH ENCODING ROUND-TRIPS: decode (encode l) = l for every list -- the encoder is lossless. encode
-- groups consecutive equal elements into (value, count) runs (extending the leading run when the new head
-- matches its value, via an evidence-carrying equality decision); decode expands them with replicate + append.
-- The crux decodePushPick relates decoding a pushed element to consing it on, using the equality witness to
-- rewrite replicate x n to replicate y n; rleRoundtrip then follows by induction.

data Natt = Z | S Natt
data List = LNil | LCons Natt List

snatCong : (a : Natt) -> (b : Natt) -> a = b -> S a = S b
snatCong a b e = cong S e

data EqDec : (x : Natt) -> (y : Natt) -> Type where
  EqYes : (x2 : Natt) -> (y2 : Natt) -> (x2 = y2) -> EqDec x2 y2
  EqNo  : (x2 : Natt) -> (y2 : Natt) -> EqDec x2 y2

eqDec : (x : Natt) -> (y : Natt) -> EqDec x y
eqDec Z Z = EqYes Z Z Refl
eqDec Z (S k) = EqNo Z (S k)
eqDec (S j) Z = EqNo (S j) Z
eqDec (S j) (S k) = case eqDec j k of
  EqYes _ _ e => EqYes (S j) (S k) (snatCong j k e)
  EqNo _ _    => EqNo (S j) (S k)

app : List -> List -> List
app LNil l2 = l2
app (LCons x xs) l2 = LCons x (app xs l2)

appCongL : (a : List) -> (b : List) -> (c : List) -> a = b -> app a c = app b c
appCongL a b c e = cong (\w => app w c) e

lconsSndCong : (x : Natt) -> (l1 : List) -> (l2 : List) -> l1 = l2 -> LCons x l1 = LCons x l2
lconsSndCong x l1 l2 e = cong (LCons x) e

replicate : Natt -> Natt -> List
replicate x Z = LNil
replicate x (S k) = LCons x (replicate x k)

replicateCong : (x : Natt) -> (y : Natt) -> (n : Natt) -> x = y -> replicate x n = replicate y n
replicateCong x y n e = cong (\w => replicate w n) e

data RLE = RNil | RCons Natt Natt RLE

pushPick : (x : Natt) -> (y : Natt) -> (n : Natt) -> (gs : RLE) -> EqDec x y -> RLE
pushPick x y n gs (EqYes _ _ e) = RCons x (S n) gs
pushPick x y n gs (EqNo _ _)    = RCons x (S Z) (RCons y n gs)

push : Natt -> RLE -> RLE
push x RNil = RCons x (S Z) RNil
push x (RCons y n gs) = pushPick x y n gs (eqDec x y)

encode : List -> RLE
encode LNil = RNil
encode (LCons x xs) = push x (encode xs)

decode : RLE -> List
decode RNil = LNil
decode (RCons y n gs) = app (replicate y n) (decode gs)

decodePushPick : (x : Natt) -> (y : Natt) -> (n : Natt) -> (gs : RLE) -> (d : EqDec x y) -> decode (pushPick x y n gs d) = LCons x (decode (RCons y n gs))
decodePushPick x y n gs (EqYes _ _ e) = lconsSndCong x (app (replicate x n) (decode gs)) (app (replicate y n) (decode gs)) (appCongL (replicate x n) (replicate y n) (decode gs) (replicateCong x y n e))
decodePushPick x y n gs (EqNo _ _) = Refl

decodePush : (x : Natt) -> (g : RLE) -> decode (push x g) = LCons x (decode g)
decodePush x RNil = Refl
decodePush x (RCons y n gs) = decodePushPick x y n gs (eqDec x y)

rleRoundtrip : (l : List) -> decode (encode l) = l
rleRoundtrip LNil = Refl
rleRoundtrip (LCons x xs) = trans (decodePush x (encode xs)) (lconsSndCong x (decode (encode xs)) xs (rleRoundtrip xs))
