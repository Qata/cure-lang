%default total

-- THE DEPENDENT CALL BOUNDARY (integration spine, item 1+2). Std.Otp.Proof already types a reply at the
-- request's OWN type ReplyOf(req) at the REPLY rule, and Std.Otp.call types a UNIFORM reply r for the whole
-- server. The missing piece is the CLIENT-side dependent call: call(server, req) returning ReplyOf(req), so a
-- single server answers DIFFERENT requests at DIFFERENT reply types, checked at the call site. Std.Otp.call
-- avoids this only because a return-only implicit r cannot resolve through the effectful extern -- but
-- ReplyOf(req) is a function of the EXPLICIT request argument, so it IS determined. This models the boundary:
-- a server carries a total dependent handler (r : Req) -> ReplyOf r, and call dispatches through it, returning
-- the request's own reply type. clientGetCount / clientPing witness two calls to ONE server resolving to two
-- DISTINCT reply types.

data Nat2 = Z | S Nat2

-- The two distinct reply types plus a field payload -- the smallest heterogeneous request algebra.
data RName  = Nm
data RCount = Cnt Nat2
data RAck   = Ack

data Req = GetCount | SetName RName | Ping

-- Per-constructor reply type by large elimination: GetCount answers a count, the others an ack.
ReplyOf : Req -> Type
ReplyOf GetCount    = RCount
ReplyOf (SetName _) = RAck
ReplyOf Ping        = RAck

-- A server handle carrying its total dependent handler (erased to a raw pid in the real algebra).
data DepServer : Type where
  MkServer : ((r : Req) -> ReplyOf r) -> DepServer

-- THE DEPENDENT CALL: the reply has the request's OWN type. This is what Std.Otp.call lacks.
call : DepServer -> (r : Req) -> ReplyOf r
call (MkServer h) r = h r

-- A concrete total handler: every request answered at its own reply type.
myHandle : (r : Req) -> ReplyOf r
myHandle GetCount    = Cnt Z
myHandle (SetName n) = Ack
myHandle Ping        = Ack

-- Two calls to ONE server resolve to two DISTINCT reply types at the client -- the heterogeneity Std.Otp.call
-- cannot express.
clientGetCount : RCount
clientGetCount = call (MkServer myHandle) GetCount

clientPing : RAck
clientPing = call (MkServer myHandle) Ping
