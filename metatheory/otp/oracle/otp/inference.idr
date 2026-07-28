%default total

data Tag = TA | TB | TC

ta_ne_tb : TA = TB -> Void
ta_ne_tb Refl impossible
ta_ne_tc : TA = TC -> Void
ta_ne_tc Refl impossible
tb_ne_ta : TB = TA -> Void
tb_ne_ta Refl impossible
tb_ne_tc : TB = TC -> Void
tb_ne_tc Refl impossible
tc_ne_ta : TC = TA -> Void
tc_ne_ta Refl impossible
tc_ne_tb : TC = TB -> Void
tc_ne_tb Refl impossible

tag_eq : (a : Tag) -> (b : Tag) -> Dec (a = b)
tag_eq TA TA = Yes Refl
tag_eq TA TB = No ta_ne_tb
tag_eq TA TC = No ta_ne_tc
tag_eq TB TA = No tb_ne_ta
tag_eq TB TB = Yes Refl
tag_eq TB TC = No tb_ne_tc
tag_eq TC TA = No tc_ne_ta
tag_eq TC TB = No tc_ne_tb
tag_eq TC TC = Yes Refl

data TagList = TNil | TCons Tag TagList

data Handles : Tag -> TagList -> Type where
  HHere : Handles t (TCons t rest)
  HThere : Handles t rest -> Handles t (TCons y rest)

no_handles_nil : Handles t TNil -> Void
no_handles_nil HHere impossible
no_handles_nil (HThere _) impossible

handles_here : (t : Tag) -> (h : Tag) -> (rest : TagList) -> t = h -> Handles t (TCons h rest)
handles_here t h rest eq = rewrite eq in HHere

handles_cons_absurd : (Equivalent : t = h -> Void) -> (Handles t rest -> Void) -> Handles t (TCons h rest) -> Void
handles_cons_absurd neq nrest HHere = neq Refl
handles_cons_absurd neq nrest (HThere q) = nrest q

decide_handles : (t : Tag) -> (iface : TagList) -> Dec (Handles t iface)
decide_handles t TNil = No no_handles_nil
decide_handles t (TCons h rest) = case tag_eq t h of
  Yes eq => Yes (handles_here t h rest eq)
  No neq => case decide_handles t rest of
    Yes p => Yes (HThere p)
    No nrest => No (handles_cons_absurd neq nrest)

data AllHandled : TagList -> TagList -> Type where
  AHNil : AllHandled TNil iface
  AHCons : Handles t iface -> AllHandled rest iface -> AllHandled (TCons t rest) iface

ah_head_absurd : (Handles t iface -> Void) -> AllHandled (TCons t rest) iface -> Void
ah_head_absurd nt (AHCons ht ahrest) = nt ht
ah_tail_absurd : (AllHandled rest iface -> Void) -> AllHandled (TCons t rest) iface -> Void
ah_tail_absurd nrest (AHCons ht ahrest) = nrest ahrest

decide_all_handled : (s : TagList) -> (iface : TagList) -> Dec (AllHandled s iface)
decide_all_handled TNil iface = Yes AHNil
decide_all_handled (TCons t rest) iface = case decide_handles t iface of
  No nt => No (ah_head_absurd nt)
  Yes ht => case decide_all_handled rest iface of
    Yes hrest => Yes (AHCons ht hrest)
    No nrest => No (ah_tail_absurd nrest)
