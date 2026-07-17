%default total

data MKey = MA | MB | MC
data MBit = MF | MT

keq : MKey -> MKey -> MBit
keq MA MA = MT
keq MA MB = MF
keq MA MC = MF
keq MB MA = MF
keq MB MB = MT
keq MB MC = MF
keq MC MA = MF
keq MC MB = MF
keq MC MC = MT

data Bag = BNil | BCons MKey Bag

count : MKey -> Bag -> Nat
count x BNil = Z
count x (BCons k rest) = case keq x k of
  MT => S (count x rest)
  MF => count x rest

insert : MKey -> Bag -> Bag
insert k t = BCons k t

delete_one : MKey -> Bag -> Bag
delete_one k BNil = BNil
delete_one k (BCons k2 rest) = case keq k k2 of
  MT => rest
  MF => BCons k2 (delete_one k rest)

insert_incr : (k : MKey) -> (t : Bag) -> count k (insert k t) = S (count k t)
insert_incr MA t = Refl
insert_incr MB t = Refl
insert_incr MC t = Refl

mtNeMf : MT = MF -> Void
mtNeMf Refl impossible

insert_other : (x : MKey) -> (k : MKey) -> (t : Bag) -> keq x k = MF -> count x (insert k t) = count x t
insert_other MA MA t neq = void (mtNeMf neq)
insert_other MA MB t neq = Refl
insert_other MA MC t neq = Refl
insert_other MB MA t neq = Refl
insert_other MB MB t neq = void (mtNeMf neq)
insert_other MB MC t neq = Refl
insert_other MC MA t neq = Refl
insert_other MC MB t neq = Refl
insert_other MC MC t neq = void (mtNeMf neq)

delete_insert : (k : MKey) -> (t : Bag) -> delete_one k (insert k t) = t
delete_insert MA t = Refl
delete_insert MB t = Refl
delete_insert MC t = Refl
