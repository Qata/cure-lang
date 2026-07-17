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
