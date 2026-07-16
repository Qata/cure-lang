%default total

data Reply0 = R0
data Reply1 = R1a | R1b
data Req = GetCount | SetName Reply0 | Ping

ReplyOf : Req -> Type
ReplyOf GetCount = Reply0
ReplyOf (SetName _) = Reply1
ReplyOf Ping = Reply1

data ReplyCap : Req -> Type where
  MkCap : ReplyCap r

data Replied = Done
data Pair = MkPair Replied Replied

reply : {r : Req} -> (1 _ : ReplyCap r) -> ReplyOf r -> Replied
reply MkCap _ = Done

handle : (r : Req) -> (1 _ : ReplyCap r) -> Replied
handle GetCount cap = Done
handle (SetName _) cap = reply cap R1a
handle Ping cap = reply cap R1b
