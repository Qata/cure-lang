%default total

data Tag = TA | TB
data Local = LEnd | LSend Tag Local | LRecv Tag Local | LSel Tag Local Tag Local | LBra Tag Local Tag Local
data Buf = BEmpty | BFull Tag
data Config = MkConfig Local Local Buf Buf

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)
dual (LSel tL kL tR kR) = LBra tL (dual kL) tR (dual kR)
dual (LBra tL kL tR kR) = LSel tL (dual kL) tR (dual kR)

data AStep : Config -> Config -> Type where
  ASendA : AStep (MkConfig (LSend t ka) b BEmpty ba) (MkConfig ka b (BFull t) ba)
  ARecvB : AStep (MkConfig a (LRecv t kb) (BFull t) ba) (MkConfig a kb BEmpty ba)
  ASendB : AStep (MkConfig a (LSend t kb) ab BEmpty) (MkConfig a kb ab (BFull t))
  ARecvA : AStep (MkConfig (LRecv t ka) b ab (BFull t)) (MkConfig ka b ab BEmpty)
  ASelA : AStep (MkConfig (LSel tL kaL tR kaR) b BEmpty ba) (MkConfig kaL b (BFull tL) ba)
  ABraB : AStep (MkConfig a (LBra tL kbL tR kbR) (BFull tL) ba) (MkConfig a kbL BEmpty ba)
  ASelB : AStep (MkConfig a (LSel tL kbL tR kbR) ab BEmpty) (MkConfig a kbL ab (BFull tL))
  ABraA : AStep (MkConfig (LBra tL kaL tR kaR) b ab (BFull tL)) (MkConfig kaL b ab BEmpty)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

async_terminates : (l : Local) -> ARun (MkConfig l (dual l) BEmpty BEmpty) (MkConfig LEnd LEnd BEmpty BEmpty)
async_terminates LEnd = ARDone
async_terminates (LSend t ka) = ARStep ASendA (ARStep ARecvB (async_terminates ka))
async_terminates (LRecv t ka) = ARStep ASendB (ARStep ARecvA (async_terminates ka))
async_terminates (LSel tL kaL tR kaR) = ARStep ASelA (ARStep ABraB (async_terminates kaL))
async_terminates (LBra tL kaL tR kaR) = ARStep ASelB (ARStep ABraA (async_terminates kaL))
