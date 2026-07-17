%default total

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList

data Member : Tag -> TagList -> Type where
  MemHere : Member t (TCons t rest)
  MemThere : Member t rest -> Member t (TCons y rest)

data AllMember : TagList -> TagList -> Type where
  AMNil : AllMember TNil iface
  AMCons : Member t iface -> AllMember rest iface -> AllMember (TCons t rest) iface

data Config = MkConfig TagList TagList

data WTat : Config -> TagList -> Type where
  MkWTat : AllMember e iface -> AllMember m iface -> WTat (MkConfig e m) iface

data StepAt : TagList -> Config -> Config -> Type where
  SSendAt : Member t i -> StepAt i (MkConfig e m) (MkConfig (TCons t e) m)
  SArriveAt : StepAt i (MkConfig (TCons t e) m) (MkConfig e (TCons t m))
  SRecvAt : StepAt i (MkConfig e (TCons t m)) (MkConfig e m)

preservation_at : WTat b i -> StepAt i b a -> WTat a i
preservation_at (MkWTat ae am) (SSendAt mem) = MkWTat (AMCons mem ae) am
preservation_at (MkWTat (AMCons at ae2) am) SArriveAt = MkWTat ae2 (AMCons at am)
preservation_at (MkWTat ae (AMCons rat am2)) SRecvAt = MkWTat ae am2

data Behaviour = BNil | BRecv Tag Behaviour | BSend Tag Behaviour | BSeq Behaviour Behaviour

append : TagList -> TagList -> TagList
append TNil b = b
append (TCons t rest) b = TCons t (append rest b)

infer : Behaviour -> TagList
infer BNil = TNil
infer (BRecv t k) = TCons t (infer k)
infer (BSend t k) = TCons t (infer k)
infer (BSeq l r) = append (infer l) (infer r)

member_append_left : Member t xs -> Member t (append xs ys)
member_append_left MemHere = MemHere
member_append_left (MemThere m2) = MemThere (member_append_left m2)

member_append_right : (xs : TagList) -> Member t ys -> Member t (append xs ys)
member_append_right TNil m = m
member_append_right (TCons y rest) m = MemThere (member_append_right rest m)

data SendsIn : Behaviour -> Tag -> Type where
  SendHere : SendsIn (BSend t k) t
  SendRecvK : SendsIn k t -> SendsIn (BRecv y k) t
  SendSendK : SendsIn k t -> SendsIn (BSend y k) t
  SendSeqL : SendsIn l t -> SendsIn (BSeq l r) t
  SendSeqR : SendsIn r t -> SendsIn (BSeq l r) t

coverage : (b : Behaviour) -> SendsIn b t -> Member t (infer b)
coverage BNil s = case s of _ impossible
coverage (BRecv y k) (SendRecvK s2) = MemThere (coverage k s2)
coverage (BSend y k) SendHere = MemHere
coverage (BSend y k) (SendSendK s2) = MemThere (coverage k s2)
coverage (BSeq l r) (SendSeqL s2) = member_append_left (coverage l s2)
coverage (BSeq l r) (SendSeqR s2) = member_append_right (infer l) (coverage r s2)

data Runs : Behaviour -> Config -> Type where
  RStart : Runs b (MkConfig TNil TNil)
  RStep : Runs b before -> StepAt (infer b) before after -> Runs b after

adequacy : (b : Behaviour) -> Runs b c -> WTat c (infer b)
adequacy b RStart = MkWTat AMNil AMNil
adequacy b (RStep prev step) = preservation_at (adequacy b prev) step
