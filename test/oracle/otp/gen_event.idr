%default total

data Event = EvA | EvB | EvC
data B = F | T
data EvSet = MkEvSet B B B

member : Event -> EvSet -> B
member EvA (MkEvSet a b c) = a
member EvB (MkEvSet a b c) = b
member EvC (MkEvSet a b c) = c

step : Event -> EvSet -> Nat -> Nat
step e iface st = case member e iface of
  T => S st
  F => st

data IfaceList = INil | ICons EvSet IfaceList
data Manager : IfaceList -> Type where
  MNil : Manager INil
  MCons : (iface : EvSet) -> Nat -> Manager rest -> Manager (ICons iface rest)

add_handler : (iface : EvSet) -> Nat -> Manager ifaces -> Manager (ICons iface ifaces)
add_handler iface st mgr = MCons iface st mgr

notify : Event -> Manager ifaces -> Manager ifaces
notify e MNil = MNil
notify e (MCons iface st rest) = MCons iface (step e iface st) (notify e rest)

count : Manager ifaces -> Nat
count MNil = Z
count (MCons iface st rest) = S (count rest)

interfaces : Manager ifaces -> IfaceList
interfaces MNil = INil
interfaces (MCons iface st rest) = ICons iface (interfaces rest)

snat_cong : a = b -> S a = S b
snat_cong Refl = Refl

icons_cong : (iface : EvSet) -> a = b -> ICons iface a = ICons iface b
icons_cong iface Refl = Refl

notify_preserves_count : (e : Event) -> (mgr : Manager ifaces) -> count (notify e mgr) = count mgr
notify_preserves_count e MNil = Refl
notify_preserves_count e (MCons iface st rest) = snat_cong (notify_preserves_count e rest)

notify_preserves_ifaces : (e : Event) -> (mgr : Manager ifaces) -> interfaces (notify e mgr) = interfaces mgr
notify_preserves_ifaces e MNil = Refl
notify_preserves_ifaces e (MCons iface st rest) = icons_cong iface (notify_preserves_ifaces e rest)
