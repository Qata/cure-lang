%default total

-- SORTING IS UNIQUELY SPECIFIED: two lists that are both sorted and have the same multiset (equal element
-- counts everywhere) are EQUAL. The uniqueness half of sorting correctness. Heads must be equal (each bounds
-- the other's head as a present element, so leq both ways gives equal by antisymmetry); the tails then have
-- equal counts and are sorted, so equal by induction. Membership is encoded as count > 0; the eq-test is
-- evidence-carrying (EqDec) and routed through countPick so the count refines in the hypothesis.

data Bool2 = F | T
data Natt = Z | S Natt
data Listt = LNil | LCons Natt Listt

leq : Natt -> Natt -> Bool2
leq Z _ = T
leq (S k) Z = F
leq (S k) (S j) = leq k j

leqRefl : (a : Natt) -> leq a a = T
leqRefl Z = Refl
leqRefl (S k) = leqRefl k

eqn : Natt -> Natt -> Bool2
eqn Z Z = T
eqn Z (S k) = F
eqn (S j) Z = F
eqn (S j) (S k) = eqn j k

eqnRefl : (a : Natt) -> eqn a a = T
eqnRefl Z = Refl
eqnRefl (S k) = eqnRefl k

sInj : (a : Natt) -> (b : Natt) -> S a = S b -> a = b
sInj a b e = cong pred e
  where
    pred : Natt -> Natt
    pred Z = Z
    pred (S k) = k

leqAntisym : (a : Natt) -> (b : Natt) -> leq a b = T -> leq b a = T -> a = b
leqAntisym Z Z h1 h2 = Refl
leqAntisym Z (S k) h1 h2 = case h2 of Refl impossible
leqAntisym (S j) Z h1 h2 = case h1 of Refl impossible
leqAntisym (S j) (S k) h1 h2 = cong S (leqAntisym j k h1 h2)

data EqDec : (x : Natt) -> (y : Natt) -> Type where
  EqYes : (x2 : Natt) -> (y2 : Natt) -> (x2 = y2) -> EqDec x2 y2
  EqNo  : (x2 : Natt) -> (y2 : Natt) -> (eqn x2 y2 = F) -> EqDec x2 y2

eqDec : (x : Natt) -> (y : Natt) -> EqDec x y
eqDec Z Z = EqYes Z Z Refl
eqDec Z (S k) = EqNo Z (S k) Refl
eqDec (S j) Z = EqNo (S j) Z Refl
eqDec (S j) (S k) = case eqDec j k of
  EqYes _ _ e => EqYes (S j) (S k) (cong S e)
  EqNo _ _ ne => EqNo (S j) (S k) ne

countPick : Natt -> Natt -> Listt -> Bool2 -> Natt
count : Natt -> Listt -> Natt
countPickD : (z : Natt) -> (w : Natt) -> (r : Listt) -> EqDec z w -> Natt
countPickD z w r (EqYes _ _ e) = S (count z r)
countPickD z w r (EqNo _ _ ne) = count z r
count z LNil = Z
count z (LCons w r) = countPickD z w r (eqDec z w)

countConsSelfPick : (y : Natt) -> (r : Listt) -> (d : EqDec y y) -> countPickD y y r d = S (count y r)
countConsSelfPick y r (EqYes _ _ e) = Refl
countConsSelfPick y r (EqNo _ _ ne) = case trans (sym (eqnRefl y)) ne of Refl impossible

countConsSelf : (y : Natt) -> (r : Listt) -> count y (LCons y r) = S (count y r)
countConsSelf y r = countConsSelfPick y r (eqDec y y)

data LeAll : (x : Natt) -> (l : Listt) -> Type where
  LANil  : LeAll x LNil
  LACons : (y : Natt) -> (rest : Listt) -> (leq x y = T) -> LeAll x rest -> LeAll x (LCons y rest)

data Sorted : (l : Listt) -> Type where
  SNil  : Sorted LNil
  SCons : (x : Natt) -> (rest : Listt) -> LeAll x rest -> Sorted rest -> Sorted (LCons x rest)

leallCountLe : (w : Natt) -> (x : Natt) -> (l : Listt) -> (k : Natt) -> (count x l = S k) -> LeAll w l -> leq w x = T
leallCountLePick : (w : Natt) -> (x : Natt) -> (v : Natt) -> (rest : Listt) -> (k : Natt) -> LeAll w rest -> (leq w v = T) -> (d : EqDec x v) -> (countPickD x v rest d = S k) -> leq w x = T
leallCountLePick w x v rest k hla2 hwv (EqYes _ _ e) hpos = rewrite e in hwv
leallCountLePick w x v rest k hla2 hwv (EqNo _ _ ne) hpos = leallCountLe w x rest k hpos hla2
leallCountLe w x LNil k hpos LANil = case hpos of Refl impossible
leallCountLe w x (LCons v rest) k hpos (LACons v rest hwv hla2) = leallCountLePick w x v rest k hla2 hwv (eqDec x v) hpos

headLe : (x : Natt) -> (xs2 : Listt) -> (y : Natt) -> (k : Natt) -> LeAll x xs2 -> (d : EqDec y x) -> (countPickD y x xs2 d = S k) -> leq x y = T
headLe x xs2 y k la (EqYes _ _ e) hc = rewrite e in leqRefl x
headLe x xs2 y k la (EqNo _ _ ne) hc = leallCountLe x y xs2 k hc la

countHeadCong : (z : Natt) -> (x : Natt) -> (y : Natt) -> (xs2 : Listt) -> (x = y) -> count z (LCons x xs2) = count z (LCons y xs2)
countHeadCong z x y xs2 exy = cong (\hh => count z (LCons hh xs2)) exy

tailCountPick : (z : Natt) -> (hh : Natt) -> (xs2 : Listt) -> (ys2 : Listt) -> (d : EqDec z hh) -> (countPickD z hh xs2 d = countPickD z hh ys2 d) -> count z xs2 = count z ys2
tailCountPick z hh xs2 ys2 (EqYes _ _ e) hz = sInj (count z xs2) (count z ys2) hz
tailCountPick z hh xs2 ys2 (EqNo _ _ ne) hz = hz

tailCount : (z : Natt) -> (x : Natt) -> (y : Natt) -> (xs2 : Listt) -> (ys2 : Listt) -> (x = y) -> (count z (LCons x xs2) = count z (LCons y ys2)) -> count z xs2 = count z ys2
tailCount z x y xs2 ys2 exy hz = tailCountPick z y xs2 ys2 (eqDec z y) (trans (sym (countHeadCong z x y xs2 exy)) hz)

lconsCong2 : (x : Natt) -> (y : Natt) -> (xs2 : Listt) -> (ys2 : Listt) -> (x = y) -> (xs2 = ys2) -> LCons x xs2 = LCons y ys2
lconsCong2 x y xs2 ys2 exy exs = trans (cong (\hh => LCons hh xs2) exy) (cong (\tt => LCons y tt) exs)

sortedPermUnique : (xs : Listt) -> (ys : Listt) -> Sorted xs -> Sorted ys -> ((z : Natt) -> count z xs = count z ys) -> xs = ys
sortedPermUnique LNil LNil SNil SNil h = Refl
sortedPermUnique LNil (LCons y ys2) SNil (SCons y ys2 lay syy) h =
  case trans (h y) (countConsSelf y ys2) of Refl impossible
sortedPermUnique (LCons x xs2) LNil (SCons x xs2 lax sxx) SNil h =
  case trans (sym (countConsSelf x xs2)) (h x) of Refl impossible
sortedPermUnique (LCons x xs2) (LCons y ys2) (SCons x xs2 lax sxx) (SCons y ys2 lay syy) h =
  let exy = leqAntisym x y
              (headLe x xs2 y (count y ys2) lax (eqDec y x) (trans (h y) (countConsSelf y ys2)))
              (headLe y ys2 x (count x xs2) lay (eqDec x y) (trans (sym (h x)) (countConsSelf x xs2))) in
  lconsCong2 x y xs2 ys2 exy
    (sortedPermUnique xs2 ys2 sxx syy (\z => tailCount z x y xs2 ys2 exy (h z)))
