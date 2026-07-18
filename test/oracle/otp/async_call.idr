%default total

data Msg = MGet | MPut | MVal | MAck

reply_for : Msg -> Msg
reply_for MGet = MVal
reply_for MPut = MAck
reply_for MVal = MVal
reply_for MAck = MAck

data Local = LEnd | LSend Msg Local | LRecv Msg Local
data Buf = BEmpty | BFull Msg
data Config = MkConfig Local Local Buf Buf

data AStep : Config -> Config -> Type where
  ASendA : AStep (MkConfig (LSend t ka) b BEmpty ba) (MkConfig ka b (BFull t) ba)
  ARecvB : AStep (MkConfig a (LRecv t kb) (BFull t) ba) (MkConfig a kb BEmpty ba)
  ASendB : AStep (MkConfig a (LSend t kb) ab BEmpty) (MkConfig a kb ab (BFull t))
  ARecvA : AStep (MkConfig (LRecv t ka) b ab (BFull t)) (MkConfig ka b ab BEmpty)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

async_call : (req : Msg) ->
  ARun (MkConfig (LSend req (LRecv (reply_for req) LEnd)) (LRecv req (LSend (reply_for req) LEnd)) BEmpty BEmpty)
       (MkConfig LEnd LEnd BEmpty BEmpty)
async_call req = ARStep ASendA (ARStep ARecvB (ARStep ASendB (ARStep ARecvA ARDone)))
