%default total

data Bool' = False | True
data Msg = MReq | MAns
data Local = LSend Msg Local | LRecv Msg Local | LEnd
data Buffer = BEmpty | BFull Msg
data Config = MkCfg Local Local Buffer

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

is_empty : Buffer -> Bool'
is_empty BEmpty = True
is_empty (BFull m) = False

well_formed_fresh : Config -> Bool'
well_formed_fresh (MkCfg w p b) = andb (compatible w p) (is_empty b)

one_for_all_restores : (pr : Local) -> compatible pr (dual pr) = True
one_for_all_restores LEnd = Refl
one_for_all_restores (LSend MReq k) = one_for_all_restores k
one_for_all_restores (LSend MAns k) = one_for_all_restores k
one_for_all_restores (LRecv MReq k) = one_for_all_restores k
one_for_all_restores (LRecv MAns k) = one_for_all_restores k

-- restart-with-flush is fresh, for every protocol.
flush_is_fresh : (pr : Local) -> well_formed_fresh (MkCfg pr (dual pr) BEmpty) = True
flush_is_fresh LEnd = Refl
flush_is_fresh (LSend MReq k) = flush_is_fresh k
flush_is_fresh (LSend MAns k) = flush_is_fresh k
flush_is_fresh (LRecv MReq k) = flush_is_fresh k
flush_is_fresh (LRecv MAns k) = flush_is_fresh k

-- helper: andb x False = False, casing the stuck compatible.
noflush_orphans_tail : (pr : Local) -> (m : Msg) -> andb (compatible pr (dual pr)) False = False
noflush_orphans_tail pr m with (compatible pr (dual pr))
  noflush_orphans_tail pr m | True = Refl
  noflush_orphans_tail pr m | False = Refl

-- restart-without-flush orphans a message: not fresh, for every protocol.
noflush_orphans : (pr : Local) -> (m : Msg) -> well_formed_fresh (MkCfg pr (dual pr) (BFull m)) = False
noflush_orphans LEnd m = Refl
noflush_orphans (LSend MReq k) m = noflush_orphans_tail k m
noflush_orphans (LSend MAns k) m = noflush_orphans_tail k m
noflush_orphans (LRecv MReq k) m = noflush_orphans_tail k m
noflush_orphans (LRecv MAns k) m = noflush_orphans_tail k m
