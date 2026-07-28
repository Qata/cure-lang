%default total

data Eff : Type -> Type where
  Pure : a -> Eff a
  Bind : Eff a -> (a -> Eff b) -> Eff b

data Reply0 = R0
data Msg = Inc | Dec | Query Reply0
data Response = Ack | Count Reply0

data Pid : Type -> Type where
  MkPid : ((m) -> Response) -> Pid m

spawn_actor : ((m) -> Response) -> Eff (Pid m)
spawn_actor h = Pure (MkPid h)

post : Pid m -> m -> Eff Response
post (MkPid h) msg = Pure (h msg)

dispatch : Msg -> Response
dispatch Inc = Ack
dispatch Dec = Ack
dispatch (Query x) = Count x

deliver_bad : Response -> Eff Response
deliver_bad bad = Bind (spawn_actor dispatch) (\pid => post pid bad)
