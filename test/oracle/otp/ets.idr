%default total

data Key = KA | KB | KC
data B = F | T

key_eq : Key -> Key -> B
key_eq KA KA = T
key_eq KA KB = F
key_eq KA KC = F
key_eq KB KA = F
key_eq KB KB = T
key_eq KB KC = F
key_eq KC KA = F
key_eq KC KB = F
key_eq KC KC = T

data Opt = ONone | OSome Nat
data Table = TEmpty | TIns Key Nat Table

lookup : Key -> Table -> Opt
lookup k TEmpty = ONone
lookup k (TIns k2 v rest) = case key_eq k k2 of
  T => OSome v
  F => lookup k rest

insert : Key -> Nat -> Table -> Table
insert k v t = TIns k v t

lookup_insert_eq : (k : Key) -> (v : Nat) -> (t : Table) -> lookup k (insert k v t) = OSome v
lookup_insert_eq KA v t = Refl
lookup_insert_eq KB v t = Refl
lookup_insert_eq KC v t = Refl

lookup_insert_neq : (k : Key) -> (k2 : Key) -> (v : Nat) -> (t : Table) -> key_eq k k2 = F -> lookup k (insert k2 v t) = lookup k t
lookup_insert_neq KA KA v t Refl impossible
lookup_insert_neq KA KB v t neq = Refl
lookup_insert_neq KA KC v t neq = Refl
lookup_insert_neq KB KA v t neq = Refl
lookup_insert_neq KB KB v t Refl impossible
lookup_insert_neq KB KC v t neq = Refl
lookup_insert_neq KC KA v t neq = Refl
lookup_insert_neq KC KB v t neq = Refl
lookup_insert_neq KC KC v t Refl impossible
