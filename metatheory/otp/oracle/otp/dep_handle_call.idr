%default total

-- THE DEPENDENT handle_call SHAPE (integration spine, server side / item 19). The client boundary
-- (dep_call_boundary) types call(server, req) : ReplyOf(req). The SERVER must produce the matching reply: a
-- gen_server handle_call returns {reply, Reply, NewState}, and here the Reply component has the request's OWN
-- type ReplyOf(request). This is what the `actor` macro currently CANNOT emit -- actor.cure:181 emits a UNIFORM
-- reply_type. handleCall is the target the macro must emit: a total function whose result tuple carries a reply
-- typed per-request, checked per branch against ReplyOf reduced at the matched constructor. It is the same
-- dependent-return discipline as Std.Otp.Proof.handle, wrapped in the {reply, _, state} tuple.

data RName  = Nm
data RCount = Cnt
data RAck   = Ack

data Req = GetCount | SetName RName | Ping

ReplyOf : Req -> Type
ReplyOf GetCount    = RCount
ReplyOf (SetName _) = RAck
ReplyOf Ping        = RAck

data ServerState = MkState

-- The reply tag (stands for OTP's :reply atom).
data Tag = Reply

-- handle_call's result: {reply, <the request's own reply>, new state}. The middle component is ReplyOf request,
-- so the SAME callback answers different requests at different reply types -- checked per branch.
handleCall : (request : Req) -> ServerState -> (Tag, ReplyOf request, ServerState)
handleCall GetCount    st = (Reply, Cnt, st)
handleCall (SetName n) st = (Reply, Ack, st)
handleCall Ping        st = (Reply, Ack, st)
