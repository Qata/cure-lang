%default total

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList
data Mailbox = BNil | BCons Tag Mailbox

data InSet : Tag -> TagList -> Type where
  Here : InSet t (TCons t rest)
  There : InSet t rest -> InSet t (TCons y rest)

data InMbox : Tag -> Mailbox -> Type where
  MHere : InMbox t (BCons t rest)
  MThere : InMbox t rest -> InMbox t (BCons y rest)

data SelRecv : TagList -> Mailbox -> Tag -> Mailbox -> Type where
  SRHere : InSet t set -> SelRecv set (BCons t rest) t rest
  SRSkip : SelRecv set rest g after -> SelRecv set (BCons h rest) g (BCons h after)

selrecv_matches : SelRecv set before got after -> InSet got set
selrecv_matches (SRHere mem) = mem
selrecv_matches (SRSkip sr2) = selrecv_matches sr2

selrecv_present : SelRecv set before got after -> InMbox got before
selrecv_present (SRHere mem) = MHere
selrecv_present (SRSkip sr2) = MThere (selrecv_present sr2)
