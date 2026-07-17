%default total

data Req = RGet | RPut
data Rep = VNat | VUnit

reply_for : Req -> Rep
reply_for RGet = VNat
reply_for RPut = VUnit

data SType = SEnd | SSendReq Req SType | SRecvReq Req SType | SSendRep Rep SType | SRecvRep Rep SType

dual : SType -> SType
dual SEnd = SEnd
dual (SSendReq q k) = SRecvReq q (dual k)
dual (SRecvReq q k) = SSendReq q (dual k)
dual (SSendRep p k) = SRecvRep p (dual k)
dual (SRecvRep p k) = SSendRep p (dual k)

client : Req -> SType
client req = SSendReq req (SRecvRep (reply_for req) SEnd)

server : Req -> SType
server req = SRecvReq req (SSendRep (reply_for req) SEnd)

call_duality : (req : Req) -> client req = dual (server req)
call_duality req = Refl

data Compat : SType -> SType -> Type where
  CEnd : Compat SEnd SEnd
  CReqL : (q : Req) -> Compat l r -> Compat (SSendReq q l) (SRecvReq q r)
  CRepR : (p : Rep) -> Compat l r -> Compat (SRecvRep p l) (SSendRep p r)

call_compat : (req : Req) -> Compat (client req) (server req)
call_compat req = CReqL req (CRepR (reply_for req) CEnd)
