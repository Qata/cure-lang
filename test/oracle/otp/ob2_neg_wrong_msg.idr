%default total

data Reply0 = R0
data Msg = Inc | Dec | Query Reply0
data Response = Ack | Count Reply0
data Pid : Type -> Type where
  MkPid : (m -> Response) -> Pid m
spawn_actor : {m : Type} -> (m -> Response) -> Pid m
spawn_actor h = MkPid h
post : {m : Type} -> Pid m -> m -> Response
post (MkPid h) msg = h msg
dispatch : Msg -> Response
dispatch Inc = Ack
dispatch Dec = Ack
dispatch (Query x) = Count x
data Other = OtherMsg

client : Other -> Response
client bad = post (spawn_actor dispatch) bad
