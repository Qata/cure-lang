%default total

data Msg = MGet | MPut | MVal | MAck

reply_for : Msg -> Msg
reply_for MGet = MVal
reply_for MPut = MAck
reply_for MVal = MVal
reply_for MAck = MAck

data Local = LEnd | LSend Msg Local | LRecv Msg Local
data Reqs = RNil | RCons Msg Reqs

client_local : Reqs -> Local
client_local RNil = LEnd
client_local (RCons req rest) = LSend req (LRecv (reply_for req) (client_local rest))

server_local : Reqs -> Local
server_local RNil = LEnd
server_local (RCons req rest) = LRecv req (LSend (reply_for req) (server_local rest))

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

batch_serves : (rs : Reqs) -> ARun (MkConfig (client_local rs) (server_local rs) BEmpty BEmpty) (MkConfig LEnd LEnd BEmpty BEmpty)
batch_serves RNil = ARDone
batch_serves (RCons req rest) = ARStep ASendA (ARStep ARecvB (ARStep ASendB (ARStep ARecvA (batch_serves rest))))
