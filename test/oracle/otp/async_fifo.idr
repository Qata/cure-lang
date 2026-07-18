%default total

data Tag = TA | TB
data Local = LEnd | LSend Tag Local | LRecv Tag Local
data Buf = BNil | BCons Tag Buf

snoc : Buf -> Tag -> Buf
snoc BNil t = BCons t BNil
snoc (BCons t2 rest) t = BCons t2 (snoc rest t)

data Config = MkConfig Local Local Buf Buf

data AStep : Config -> Config -> Type where
  ASendA : AStep (MkConfig (LSend t ka) b ab ba) (MkConfig ka b (snoc ab t) ba)
  ARecvB : AStep (MkConfig a (LRecv t kb) (BCons t ab) ba) (MkConfig a kb ab ba)
  ASendB : AStep (MkConfig a (LSend t kb) ab ba) (MkConfig a kb ab (snoc ba t))
  ARecvA : AStep (MkConfig (LRecv t ka) b ab (BCons t ba)) (MkConfig ka b ab ba)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

pipelined : (t1 : Tag) -> (t2 : Tag) ->
  ARun (MkConfig (LSend t1 (LSend t2 LEnd)) (LRecv t1 (LRecv t2 LEnd)) BNil BNil) (MkConfig LEnd LEnd BNil BNil)
pipelined t1 t2 = ARStep ASendA (ARStep ASendA (ARStep ARecvB (ARStep ARecvB ARDone)))
