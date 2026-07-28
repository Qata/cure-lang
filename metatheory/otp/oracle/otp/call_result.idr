%default total

data Req = RGet | RPut
data Rep = VNat | VBool
data Bit = B0 | B1

RepVal : Rep -> Type
RepVal VNat = Nat
RepVal VBool = Bit

reply_for : Req -> Rep
reply_for RGet = VNat
reply_for RPut = VBool

data CallError = Timeout | NoProc | ServerDied

data CallResult : Req -> Type where
  Ok : (r : Req) -> RepVal (reply_for r) -> CallResult r
  Err : (r : Req) -> CallError -> CallResult r

data Status = Success | Failure

describe : CallResult r -> Status
describe (Ok rr v) = Success
describe (Err rr e) = Failure

get_reply : CallResult RGet
get_reply = Ok RGet (S Z)

put_reply : CallResult RPut
put_reply = Ok RPut B1
