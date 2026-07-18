%default total

data Bool' = False | True
data Msg = MReq | MAns
data Local = LSend Msg Local | LRecv Msg Local | LEnd

andb : Bool' -> Bool' -> Bool'
andb True b = b
andb False b = False

meq : Msg -> Msg -> Bool'
meq MReq MReq = True
meq MReq MAns = False
meq MAns MReq = False
meq MAns MAns = True

dual : Local -> Local
dual LEnd = LEnd
dual (LSend m k) = LRecv m (dual k)
dual (LRecv m k) = LSend m (dual k)

compatible : Local -> Local -> Bool'
compatible LEnd LEnd = True
compatible LEnd (LSend m2 k2) = False
compatible LEnd (LRecv m2 k2) = False
compatible (LSend m k) LEnd = False
compatible (LSend m k) (LSend m2 k2) = False
compatible (LSend m k) (LRecv m2 k2) = andb (meq m m2) (compatible k k2)
compatible (LRecv m k) LEnd = False
compatible (LRecv m k) (LSend m2 k2) = andb (meq m m2) (compatible k k2)
compatible (LRecv m k) (LRecv m2 k2) = False

meq_refl : (m : Msg) -> meq m m = True
meq_refl MReq = Refl
meq_refl MAns = Refl

-- one_for_all restores duality for every protocol.
one_for_all_restores : (pr : Local) -> compatible pr (dual pr) = True
one_for_all_restores LEnd = Refl
one_for_all_restores (LSend MReq k) = one_for_all_restores k
one_for_all_restores (LSend MAns k) = one_for_all_restores k
one_for_all_restores (LRecv MReq k) = one_for_all_restores k
one_for_all_restores (LRecv MAns k) = one_for_all_restores k

-- one_for_all on the running protocol: well-typed.
both_restart_ok : compatible (LSend MReq (LRecv MAns LEnd)) (dual (LSend MReq (LRecv MAns LEnd))) = True
both_restart_ok = one_for_all_restores (LSend MReq (LRecv MAns LEnd))

-- one_for_one mid-session: worker resets to init, peer still mid-protocol -> both want to SEND -> broken.
worker_only_breaks : compatible (LSend MReq (LRecv MAns LEnd)) (LSend MAns LEnd) = False
worker_only_breaks = Refl
