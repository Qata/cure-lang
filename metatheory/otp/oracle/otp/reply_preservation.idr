%default total

data Req = GetCount | Ping
data Val = VInt | VAtom

data HasReply : Req -> Val -> Type where
  HRGet : HasReply GetCount VInt
  HRPing : HasReply Ping VAtom

data Reply = MkReply Req Val
data Replies = RNil | RCons Reply Replies

data AllReplied : Replies -> Type where
  ARNil : AllReplied RNil
  ARCons : HasReply r v -> AllReplied rest -> AllReplied (RCons (MkReply r v) rest)

data Config = MkConfig Replies Replies

data WT : Config -> Type where
  MkWT : AllReplied e -> AllReplied m -> WT (MkConfig e m)

data Step : Config -> Config -> Type where
  SReply : HasReply r v -> Step (MkConfig e m) (MkConfig (RCons (MkReply r v) e) m)
  SArrive : Step (MkConfig (RCons (MkReply r v) e) m) (MkConfig e (RCons (MkReply r v) m))
  SRecv : Step (MkConfig e (RCons (MkReply r v) m)) (MkConfig e m)

preservation : WT b -> Step b a -> WT a
preservation (MkWT ae am) (SReply hr) = MkWT (ARCons hr ae) am
preservation (MkWT (ARCons hr ae2) am) SArrive = MkWT ae2 (ARCons hr am)
preservation (MkWT ae (ARCons hr am2)) SRecv = MkWT ae am2

data RInt = RI
data RAtom = RA

ReplyOf : Req -> Type
ReplyOf GetCount = RInt
ReplyOf Ping = RAtom

reify : HasReply r v -> ReplyOf r
reify HRGet = RI
reify HRPing = RA
