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

count_sends : Eff -> Nat
count_sends ENil = 0
count_sends (ECons (OSend t) k) = S (count_sends k)
count_sends (ECons (ORecv t) k) = count_sends k
count_sends (ECons OSpawn k) = count_sends k

count_hom : (a : Eff) -> (b : Eff) -> count_sends (eseq a b) = count_sends a + count_sends b
count_hom ENil b = Refl
count_hom (ECons (OSend t) k) b = rewrite count_hom k b in Refl
count_hom (ECons (ORecv t) k) b = count_hom k b
count_hom (ECons OSpawn k) b = count_hom k b
