%default total

data B = F | T
data BLe : B -> B -> Type where
  BLeF : BLe F y
  BLeT : BLe T T

ble_refl : (x : B) -> BLe x x
ble_refl F = BLeF
ble_refl T = BLeT

ble_trans : BLe x y -> BLe y z -> BLe x z
ble_trans BLeF q = BLeF
ble_trans BLeT BLeT = BLeT

data LSet = MkLSet B B B
data LSub : LSet -> LSet -> Type where
  MkLSub : BLe a1 a2 -> BLe b1 b2 -> BLe c1 c2 -> LSub (MkLSet a1 b1 c1) (MkLSet a2 b2 c2)

lsub_refl : (s : LSet) -> LSub s s
lsub_refl (MkLSet a b c) = MkLSub (ble_refl a) (ble_refl b) (ble_refl c)

lsub_trans : LSub s u -> LSub u v -> LSub s v
lsub_trans (MkLSub pa pb pc) (MkLSub qa qb qc) = MkLSub (ble_trans pa qa) (ble_trans pb qb) (ble_trans pc qc)

data Tag = TA | TB | TC
data SType = SEnd | SSend Tag SType | SRecv Tag SType | SSelect LSet SType | SBranch LSet SType

data Sub : SType -> SType -> Type where
  SubEnd : Sub SEnd SEnd
  SubSend : (tg : Tag) -> Sub k1 k2 -> Sub (SSend tg k1) (SSend tg k2)
  SubRecv : (tg : Tag) -> Sub k1 k2 -> Sub (SRecv tg k1) (SRecv tg k2)
  SubSel : LSub s1 s2 -> Sub k1 k2 -> Sub (SSelect s1 k1) (SSelect s2 k2)
  SubBra : LSub s2 s1 -> Sub k1 k2 -> Sub (SBranch s1 k1) (SBranch s2 k2)

sub_refl : (s : SType) -> Sub s s
sub_refl SEnd = SubEnd
sub_refl (SSend tg k) = SubSend tg (sub_refl k)
sub_refl (SRecv tg k) = SubRecv tg (sub_refl k)
sub_refl (SSelect ls k) = SubSel (lsub_refl ls) (sub_refl k)
sub_refl (SBranch ls k) = SubBra (lsub_refl ls) (sub_refl k)

sub_trans : Sub a b -> Sub b c -> Sub a c
sub_trans SubEnd SubEnd = SubEnd
sub_trans (SubSend tg p2) (SubSend tg q2) = SubSend tg (sub_trans p2 q2)
sub_trans (SubRecv tg p2) (SubRecv tg q2) = SubRecv tg (sub_trans p2 q2)
sub_trans (SubSel pl p2) (SubSel ql q2) = SubSel (lsub_trans pl ql) (sub_trans p2 q2)
sub_trans (SubBra pl p2) (SubBra ql q2) = SubBra (lsub_trans ql pl) (sub_trans p2 q2)

dual : SType -> SType
dual SEnd = SEnd
dual (SSend tg k) = SRecv tg (dual k)
dual (SRecv tg k) = SSend tg (dual k)
dual (SSelect ls k) = SBranch ls (dual k)
dual (SBranch ls k) = SSelect ls (dual k)

sub_dual_antitone : Sub s t -> Sub (dual t) (dual s)
sub_dual_antitone SubEnd = SubEnd
sub_dual_antitone (SubSend tg p2) = SubRecv tg (sub_dual_antitone p2)
sub_dual_antitone (SubRecv tg p2) = SubSend tg (sub_dual_antitone p2)
sub_dual_antitone (SubSel pl p2) = SubBra pl (sub_dual_antitone p2)
sub_dual_antitone (SubBra pl p2) = SubSel pl (sub_dual_antitone p2)

data Compat : SType -> SType -> Type where
  CEnd : Compat SEnd SEnd
  CSR : (tg : Tag) -> Compat l r -> Compat (SSend tg l) (SRecv tg r)
  CRS : (tg : Tag) -> Compat l r -> Compat (SRecv tg l) (SSend tg r)
  CSelBra : LSub sl sr -> Compat kl kr -> Compat (SSelect sl kl) (SBranch sr kr)
  CBraSel : LSub sr sl -> Compat kl kr -> Compat (SBranch sl kl) (SSelect sr kr)

narrow : Sub s s2 -> Compat s2 t -> Compat s t
narrow SubEnd c = c
narrow (SubSend tg sub2) (CSR tg c2) = CSR tg (narrow sub2 c2)
narrow (SubRecv tg sub2) (CRS tg c2) = CRS tg (narrow sub2 c2)
narrow (SubSel sl sub2) (CSelBra cl c2) = CSelBra (lsub_trans sl cl) (narrow sub2 c2)
narrow (SubBra sl sub2) (CBraSel cl c2) = CBraSel (lsub_trans cl sl) (narrow sub2 c2)

ble_antisym : BLe x y -> BLe y x -> x = y
ble_antisym BLeF BLeF = Refl
ble_antisym BLeT q = Refl

mklset_cong : a1 = a2 -> b1 = b2 -> c1 = c2 -> MkLSet a1 b1 c1 = MkLSet a2 b2 c2
mklset_cong Refl Refl Refl = Refl

lsub_antisym : LSub s t -> LSub t s -> s = t
lsub_antisym (MkLSub pa pb pc) (MkLSub qa qb qc) = mklset_cong (ble_antisym pa qa) (ble_antisym pb qb) (ble_antisym pc qc)

ssend_cong : (tg : Tag) -> x = y -> SSend tg x = SSend tg y
ssend_cong tg prf = cong (SSend tg) prf

srecv_cong : (tg : Tag) -> x = y -> SRecv tg x = SRecv tg y
srecv_cong tg prf = cong (SRecv tg) prf

sselect_cong2 : s1 = s2 -> x = y -> SSelect s1 x = SSelect s2 y
sselect_cong2 Refl Refl = Refl

sbranch_cong2 : s1 = s2 -> x = y -> SBranch s1 x = SBranch s2 y
sbranch_cong2 Refl Refl = Refl

sub_antisym : Sub s t -> Sub t s -> s = t
sub_antisym SubEnd SubEnd = Refl
sub_antisym (SubSend tg p2) (SubSend tg q2) = ssend_cong tg (sub_antisym p2 q2)
sub_antisym (SubRecv tg p2) (SubRecv tg q2) = srecv_cong tg (sub_antisym p2 q2)
sub_antisym (SubSel pl p2) (SubSel ql q2) = sselect_cong2 (lsub_antisym pl ql) (sub_antisym p2 q2)
sub_antisym (SubBra pl p2) (SubBra ql q2) = sbranch_cong2 (lsub_antisym ql pl) (sub_antisym p2 q2)
