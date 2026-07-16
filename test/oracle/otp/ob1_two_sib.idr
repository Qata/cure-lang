%default total
data Reply0 = R0
data Req = A | B
ReplyOf : Req -> Type
ReplyOf A = Reply0
ReplyOf B = Reply0
data Cap1 : Req -> Type where
  MkC1 : Cap1 r
data Cap2 : Req -> Type where
  MkC2 : Cap2 r
data Replied = Done
use_both : {r : Req} -> (1 _ : Cap1 r) -> (1 _ : Cap2 r) -> ReplyOf r -> Replied
use_both MkC1 MkC2 _ = Done
use1 : {r : Req} -> (1 _ : Cap1 r) -> ReplyOf r -> Replied
use1 MkC1 _ = Done
handle : (r : Req) -> (1 _ : Cap1 r) -> (1 _ : Cap2 r) -> Replied
handle A c1 c2 = use_both c1 c2 R0
handle B c1 c2 = use_both c1 c2 R0
