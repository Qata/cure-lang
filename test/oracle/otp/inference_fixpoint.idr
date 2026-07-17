%default total

data Tag = TA | TB | TC
data TagList = TNil | TCons Tag TagList

data Handles : Tag -> TagList -> Type where
  HHere : Handles t (TCons t rest)
  HThere : Handles t rest -> Handles t (TCons y rest)
data AllHandled : TagList -> TagList -> Type where
  AHNil : AllHandled TNil iface
  AHCons : Handles t iface -> AllHandled rest iface -> AllHandled (TCons t rest) iface

iterate : (TagList -> TagList) -> TagList -> Nat -> TagList
iterate f x Z = x
iterate f x (S k) = f (iterate f x k)

handles_weaken : Handles t y -> AllHandled y z -> Handles t z
handles_weaken HHere (AHCons ht srest) = ht
handles_weaken (HThere h2) (AHCons hh srest) = handles_weaken h2 srest

all_handled_trans : AllHandled x y -> AllHandled y z -> AllHandled x z
all_handled_trans AHNil yz = AHNil
all_handled_trans (AHCons hx xrest) yz = AHCons (handles_weaken hx yz) (all_handled_trans xrest yz)

lfp_le : (f : TagList -> TagList) ->
         ((x : TagList) -> (y : TagList) -> AllHandled x y -> AllHandled (f x) (f y)) ->
         (a : TagList) -> AllHandled (f a) a -> (n : Nat) ->
         AllHandled (iterate f TNil n) a
lfp_le f mono a pre Z = AHNil
lfp_le f mono a pre (S k) = all_handled_trans (mono (iterate f TNil k) a (lfp_le f mono a pre k)) pre
