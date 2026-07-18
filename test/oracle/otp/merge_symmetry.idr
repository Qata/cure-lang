%default total

data TB2 = F | T
data Tag = TA | TB | TC
data Local = LEnd | LSend Tag Local | LRecv Tag Local | LSel Tag Local Tag Local | LBra Tag Local Tag Local | LErr

tag_eq : Tag -> Tag -> TB2
tag_eq TA TA = T
tag_eq TA TB = F
tag_eq TA TC = F
tag_eq TB TA = F
tag_eq TB TB = T
tag_eq TB TC = F
tag_eq TC TA = F
tag_eq TC TB = F
tag_eq TC TC = T

tag_eq_sym : (a : Tag) -> (b : Tag) -> tag_eq a b = tag_eq b a
tag_eq_sym TA TA = Refl
tag_eq_sym TA TB = Refl
tag_eq_sym TA TC = Refl
tag_eq_sym TB TA = Refl
tag_eq_sym TB TB = Refl
tag_eq_sym TB TC = Refl
tag_eq_sym TC TA = Refl
tag_eq_sym TC TB = Refl
tag_eq_sym TC TC = Refl

tag_eq_refl : (t : Tag) -> tag_eq t t = T
tag_eq_refl TA = Refl
tag_eq_refl TB = Refl
tag_eq_refl TC = Refl

is_err : Local -> TB2
is_err LEnd = F
is_err (LSend t k) = F
is_err (LRecv t k) = F
is_err (LSel a aA b bB) = F
is_err (LBra a aA b bB) = F
is_err LErr = T

merge : Local -> Local -> Local
merge LEnd LEnd = LEnd
merge LEnd (LSend t2 k2) = LErr
merge LEnd (LRecv t2 k2) = LErr
merge LEnd (LSel a2 aA2 b2 bB2) = LErr
merge LEnd (LBra a2 aA2 b2 bB2) = LErr
merge LEnd LErr = LErr
merge (LSend t1 k1) LEnd = LErr
merge (LSend t1 k1) (LSend t2 k2) = case tag_eq t1 t2 of
  T => LSend t1 (merge k1 k2)
  F => LErr
merge (LSend t1 k1) (LRecv t2 k2) = LErr
merge (LSend t1 k1) (LSel a2 aA2 b2 bB2) = LErr
merge (LSend t1 k1) (LBra a2 aA2 b2 bB2) = LErr
merge (LSend t1 k1) LErr = LErr
merge (LRecv t1 k1) LEnd = LErr
merge (LRecv t1 k1) (LSend t2 k2) = LErr
merge (LRecv t1 k1) (LRecv t2 k2) = case tag_eq t1 t2 of
  T => LRecv t1 (merge k1 k2)
  F => LBra t1 k1 t2 k2
merge (LRecv t1 k1) (LSel a2 aA2 b2 bB2) = LErr
merge (LRecv t1 k1) (LBra a2 aA2 b2 bB2) = LErr
merge (LRecv t1 k1) LErr = LErr
merge (LSel a1 aA1 b1 bB1) LEnd = LErr
merge (LSel a1 aA1 b1 bB1) (LSend t2 k2) = LErr
merge (LSel a1 aA1 b1 bB1) (LRecv t2 k2) = LErr
merge (LSel a1 aA1 b1 bB1) (LSel a2 aA2 b2 bB2) = case tag_eq a1 a2 of
  T => case tag_eq b1 b2 of
    T => LSel a1 (merge aA1 aA2) b1 (merge bB1 bB2)
    F => LErr
  F => LErr
merge (LSel a1 aA1 b1 bB1) (LBra a2 aA2 b2 bB2) = LErr
merge (LSel a1 aA1 b1 bB1) LErr = LErr
merge (LBra a1 aA1 b1 bB1) LEnd = LErr
merge (LBra a1 aA1 b1 bB1) (LSend t2 k2) = LErr
merge (LBra a1 aA1 b1 bB1) (LRecv t2 k2) = LErr
merge (LBra a1 aA1 b1 bB1) (LSel a2 aA2 b2 bB2) = LErr
merge (LBra a1 aA1 b1 bB1) (LBra a2 aA2 b2 bB2) = case tag_eq a1 a2 of
  T => case tag_eq b1 b2 of
    T => LBra a1 (merge aA1 aA2) b1 (merge bB1 bB2)
    F => LErr
  F => LErr
merge (LBra a1 aA1 b1 bB1) LErr = LErr
merge LErr y = LErr

data Mergeable : Local -> Local -> Type where
  MgEnd    : Mergeable LEnd LEnd
  MgSend   : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LSend t k1) (LSend t k2)
  MgRecvEq : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LRecv t k1) (LRecv t k2)
  MgRecvNe : (a : Tag) -> (b : Tag) -> tag_eq a b = F -> Mergeable (LRecv a k1) (LRecv b k2)
  MgSel    : (a : Tag) -> (b : Tag) -> Mergeable aA1 aA2 -> Mergeable bB1 bB2 -> Mergeable (LSel a aA1 b bB1) (LSel a aA2 b bB2)
  MgBra    : (a : Tag) -> (b : Tag) -> Mergeable aA1 aA2 -> Mergeable bB1 bB2 -> Mergeable (LBra a aA1 b bB1) (LBra a aA2 b bB2)

merge_ok : Mergeable x y -> is_err (merge x y) = F
merge_ok MgEnd = Refl
merge_ok (MgSend t w2) = rewrite tag_eq_refl t in Refl
merge_ok (MgRecvEq t w2) = rewrite tag_eq_refl t in Refl
merge_ok (MgRecvNe a b pne) = rewrite pne in Refl
merge_ok (MgSel a b wA wB) = rewrite tag_eq_refl a in rewrite tag_eq_refl b in Refl
merge_ok (MgBra a b wA wB) = rewrite tag_eq_refl a in rewrite tag_eq_refl b in Refl

mergeable_sym : Mergeable x y -> Mergeable y x
mergeable_sym MgEnd = MgEnd
mergeable_sym (MgSend t w2) = MgSend t (mergeable_sym w2)
mergeable_sym (MgRecvEq t w2) = MgRecvEq t (mergeable_sym w2)
mergeable_sym (MgRecvNe a b pne) = MgRecvNe b a (trans (tag_eq_sym b a) pne)
mergeable_sym (MgSel a b wA wB) = MgSel a b (mergeable_sym wA) (mergeable_sym wB)
mergeable_sym (MgBra a b wA wB) = MgBra a b (mergeable_sym wA) (mergeable_sym wB)

merge_defined_sym : Mergeable x y -> is_err (merge y x) = F
merge_defined_sym w = merge_ok (mergeable_sym w)
