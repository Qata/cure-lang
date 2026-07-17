%default total

data Tag = TA | TB | TC
data Op = OSend Tag | ORecv Tag | OSpawn
data Eff = ENil | ECons Op Eff

eseq : Eff -> Eff -> Eff
eseq ENil n = n
eseq (ECons op k) n = ECons op (eseq k n)

seq_nil_l : (n : Eff) -> eseq ENil n = n
seq_nil_l n = Refl

seq_nil_r : (m : Eff) -> eseq m ENil = m
seq_nil_r ENil = Refl
seq_nil_r (ECons op k) = rewrite seq_nil_r k in Refl

seq_assoc : (a : Eff) -> (b : Eff) -> (c : Eff) -> eseq (eseq a b) c = eseq a (eseq b c)
seq_assoc ENil b c = Refl
seq_assoc (ECons op k) b c = rewrite seq_assoc k b c in Refl
