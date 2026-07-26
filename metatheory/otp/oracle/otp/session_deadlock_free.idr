%default total

data Msg = MA | MB
data Local = LEnd | LSend Msg Local | LRecv Msg Local

dual : Local -> Local
dual LEnd = LEnd
dual (LSend m k) = LRecv m (dual k)
dual (LRecv m k) = LSend m (dual k)

data Dual : Local -> Local -> Type where
  DEnd : Dual LEnd LEnd
  DSR  : (m : Msg) -> Dual k1 k2 -> Dual (LSend m k1) (LRecv m k2)
  DRS  : (m : Msg) -> Dual k1 k2 -> Dual (LRecv m k1) (LSend m k2)

dual_sound : (l : Local) -> Dual l (dual l)
dual_sound LEnd = DEnd
dual_sound (LSend m k) = DSR m (dual_sound k)
dual_sound (LRecv m k) = DRS m (dual_sound k)

data Progress : Local -> Local -> Type where
  Terminated : Progress LEnd LEnd
  CommSR     : (m : Msg) -> Progress (LSend m k1) (LRecv m k2)
  CommRS     : (m : Msg) -> Progress (LRecv m k1) (LSend m k2)

progress : Dual p1 p2 -> Progress p1 p2
progress DEnd = Terminated
progress (DSR m d2) = CommSR m
progress (DRS m d2) = CommRS m

data CReach : Local -> Local -> Type where
  CRDone : CReach LEnd LEnd
  CRSR   : (m : Msg) -> CReach k1 k2 -> CReach (LSend m k1) (LRecv m k2)
  CRRS   : (m : Msg) -> CReach k1 k2 -> CReach (LRecv m k1) (LSend m k2)

no_deadlock : Dual p1 p2 -> CReach p1 p2
no_deadlock DEnd = CRDone
no_deadlock (DSR m d2) = CRSR m (no_deadlock d2)
no_deadlock (DRS m d2) = CRRS m (no_deadlock d2)
