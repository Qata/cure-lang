%default total

-- MODULAR CONGRUENCE. a ~= b (mod n) is witnessed by p, q with a + p*n = b + q*n (a and b differ by a
-- multiple of n). Proved an EQUIVALENCE RELATION (reflexive, symmetric, transitive) that RESPECTS ADDITION
-- (a~=a' and b~=b' imply a+b ~= a'+b') -- so addition is well-defined on residue classes, the foundation that
-- Z/n is a well-defined additive structure. The transitivity/addition proofs combine the witnesses and
-- re-associate the offsets via plus/times algebra (right-distributivity, commutativity, rearrange4).

data Natt = Z | S Natt

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

times : Natt -> Natt -> Natt
times Z b = Z
times (S k) b = plus b (times k b)

plusZero : (n : Natt) -> plus n Z = n
plusZero Z = Refl
plusZero (S k) = cong S (plusZero k)

plusSuccR : (a : Natt) -> (b : Natt) -> plus a (S b) = S (plus a b)
plusSuccR Z b = Refl
plusSuccR (S k) b = cong S (plusSuccR k b)

plusAssoc : (a : Natt) -> (b : Natt) -> (c : Natt) -> plus (plus a b) c = plus a (plus b c)
plusAssoc Z b c = Refl
plusAssoc (S k) b c = cong S (plusAssoc k b c)

plusComm : (a : Natt) -> (b : Natt) -> plus a b = plus b a
plusComm Z b = sym (plusZero b)
plusComm (S k) b = trans (cong S (plusComm k b)) (sym (plusSuccR b k))

plusCongR : (a : Natt) -> (b : Natt) -> (c : Natt) -> b = c -> plus a b = plus a c
plusCongR a b c e = cong (plus a) e

plusCongL : (a : Natt) -> (b : Natt) -> (c : Natt) -> a = b -> plus a c = plus b c
plusCongL a b c e = cong (\w => plus w c) e

plusCong2 : (a : Natt) -> (ap : Natt) -> (b : Natt) -> (bp : Natt) -> a = ap -> b = bp -> plus a b = plus ap bp
plusCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

rearrange4 : (w : Natt) -> (x : Natt) -> (y : Natt) -> (z : Natt) -> plus (plus w x) (plus y z) = plus (plus w y) (plus x z)
rearrange4 w x y z =
  trans (plusAssoc w x (plus y z))
    (trans (plusCongR w (plus x (plus y z)) (plus (plus x y) z) (sym (plusAssoc x y z)))
      (trans (plusCongR w (plus (plus x y) z) (plus (plus y x) z) (plusCongL (plus x y) (plus y x) z (plusComm x y)))
        (trans (plusCongR w (plus (plus y x) z) (plus y (plus x z)) (plusAssoc y x z))
          (sym (plusAssoc w y (plus x z))))))

timesPlusL : (a : Natt) -> (b : Natt) -> (c : Natt) -> times (plus a b) c = plus (times a c) (times b c)
timesPlusL Z b c = Refl
timesPlusL (S k) b c = trans (plusCongR c (times (plus k b) c) (plus (times k c) (times b c)) (timesPlusL k b c)) (sym (plusAssoc c (times k c) (times b c)))

data Cong : (n : Natt) -> (a : Natt) -> (b : Natt) -> Type where
  MkCong : (n2 : Natt) -> (a2 : Natt) -> (b2 : Natt) -> (p : Natt) -> (q : Natt) -> (plus a2 (times p n2) = plus b2 (times q n2)) -> Cong n2 a2 b2

congRefl : (n : Natt) -> (a : Natt) -> Cong n a a
congRefl n a = MkCong n a a Z Z Refl

congSym : (n : Natt) -> (a : Natt) -> (b : Natt) -> Cong n a b -> Cong n b a
congSym n a b (MkCong n a b p q e) = MkCong n b a q p (sym e)

congTrans : (n : Natt) -> (a : Natt) -> (b : Natt) -> (c : Natt) -> Cong n a b -> Cong n b c -> Cong n a c
congTrans n a b c (MkCong n a b p1 q1 e1) (MkCong n b c p2 q2 e2) =
  MkCong n a c (plus p1 p2) (plus q1 q2) (trans (plusCongR a (times (plus p1 p2) n) (plus (times p1 n) (times p2 n)) (timesPlusL p1 p2 n)) (trans (sym (plusAssoc a (times p1 n) (times p2 n))) (trans (plusCongL (plus a (times p1 n)) (plus b (times q1 n)) (times p2 n) e1) (trans (plusAssoc b (times q1 n) (times p2 n)) (trans (plusCongR b (plus (times q1 n) (times p2 n)) (plus (times p2 n) (times q1 n)) (plusComm (times q1 n) (times p2 n))) (trans (sym (plusAssoc b (times p2 n) (times q1 n))) (trans (plusCongL (plus b (times p2 n)) (plus c (times q2 n)) (times q1 n) e2) (trans (plusAssoc c (times q2 n) (times q1 n)) (trans (plusCongR c (plus (times q2 n) (times q1 n)) (plus (times q1 n) (times q2 n)) (plusComm (times q2 n) (times q1 n))) (plusCongR c (plus (times q1 n) (times q2 n)) (times (plus q1 q2) n) (sym (timesPlusL q1 q2 n))))))))))))

congAdd : (n : Natt) -> (a : Natt) -> (ap : Natt) -> (b : Natt) -> (bp : Natt) -> Cong n a ap -> Cong n b bp -> Cong n (plus a b) (plus ap bp)
congAdd n a ap b bp (MkCong n a ap p1 q1 e1) (MkCong n b bp p2 q2 e2) =
  MkCong n (plus a b) (plus ap bp) (plus p1 p2) (plus q1 q2) (trans (plusCongR (plus a b) (times (plus p1 p2) n) (plus (times p1 n) (times p2 n)) (timesPlusL p1 p2 n)) (trans (rearrange4 a b (times p1 n) (times p2 n)) (trans (plusCong2 (plus a (times p1 n)) (plus ap (times q1 n)) (plus b (times p2 n)) (plus bp (times q2 n)) e1 e2) (trans (sym (rearrange4 ap bp (times q1 n) (times q2 n))) (plusCongR (plus ap bp) (plus (times q1 n) (times q2 n)) (times (plus q1 q2) n) (sym (timesPlusL q1 q2 n)))))))
