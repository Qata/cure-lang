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

bad : WT (MkConfig (RCons (MkReply GetCount VAtom) RNil) RNil)
bad = MkWT (ARCons HRGet ARNil) ARNil
