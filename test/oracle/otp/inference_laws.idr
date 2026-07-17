%default total

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList

data Handles : Tag -> TagList -> Type where
  HHere : Handles t (TCons t rest)
  HThere : Handles t rest -> Handles t (TCons y rest)

data AllHandled : TagList -> TagList -> Type where
  AHNil : AllHandled TNil iface
  AHCons : Handles t iface -> AllHandled rest iface -> AllHandled (TCons t rest) iface

handles_mono : Handles t a -> AllHandled a b -> Handles t b
handles_mono HHere (AHCons ht srest) = ht
handles_mono (HThere h2) (AHCons sh srest) = handles_mono h2 srest

weaken : AllHandled s a -> AllHandled a b -> AllHandled s b
weaken AHNil sub = AHNil
weaken (AHCons ht ahrest) sub = AHCons (handles_mono ht sub) (weaken ahrest sub)

weaken_cons : AllHandled s iface -> (y : Tag) -> AllHandled s (TCons y iface)
weaken_cons AHNil y = AHNil
weaken_cons (AHCons ht ahrest) y = AHCons (HThere ht) (weaken_cons ahrest y)

self_member : (s : TagList) -> AllHandled s s
self_member TNil = AHNil
self_member (TCons t rest) = AHCons HHere (weaken_cons (self_member rest) t)
