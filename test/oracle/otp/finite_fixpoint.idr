%default total

data B = F | T
data IF = MkIF B B B

data Imp : B -> B -> Type where
  ImpFF : Imp F F
  ImpFT : Imp F T
  ImpTT : Imp T T

data Sub : IF -> IF -> Type where
  MkSub : Imp a a2 -> Imp b b2 -> Imp c c2 -> Sub (MkIF a b c) (MkIF a2 b2 c2)

bot_imp : (a : B) -> Imp F a
bot_imp F = ImpFF
bot_imp T = ImpFT
bot_sub : (x : IF) -> Sub (MkIF F F F) x
bot_sub (MkIF a b c) = MkSub (bot_imp a) (bot_imp b) (bot_imp c)

bcount : B -> Nat
bcount F = Z
bcount T = S Z
size : IF -> Nat
size (MkIF a b c) = bcount a + (bcount b + bcount c)

data Le : Nat -> Nat -> Type where
  LeZ : Le Z n
  LeS : Le m n -> Le (S m) (S n)
le_trans : Le a b -> Le b c -> Le a c
le_trans LeZ bc = LeZ
le_trans (LeS ab) (LeS bc) = LeS (le_trans ab bc)

data StepResult : IF -> IF -> Type where
  Stable : Sub y x -> StepResult x y
  Grew   : Le (S (size x)) (size y) -> StepResult x y

grow_or_eq : (x : IF) -> (y : IF) -> Sub x y -> StepResult x y
grow_or_eq _ _ (MkSub ia ib ic) = case ia of
  ImpFF => case ib of
    ImpFF => case ic of
      ImpFF => Stable (MkSub ImpFF ImpFF ImpFF)
      ImpFT => Grew (LeS LeZ)
      ImpTT => Stable (MkSub ImpFF ImpFF ImpTT)
    ImpFT => case ic of
      ImpFF => Grew (LeS LeZ)
      ImpFT => Grew (LeS LeZ)
      ImpTT => Grew (LeS (LeS LeZ))
    ImpTT => case ic of
      ImpFF => Stable (MkSub ImpFF ImpTT ImpFF)
      ImpFT => Grew (LeS (LeS LeZ))
      ImpTT => Stable (MkSub ImpFF ImpTT ImpTT)
  ImpFT => case ib of
    ImpFF => case ic of
      ImpFF => Grew (LeS LeZ)
      ImpFT => Grew (LeS LeZ)
      ImpTT => Grew (LeS (LeS LeZ))
    ImpFT => case ic of
      ImpFF => Grew (LeS LeZ)
      ImpFT => Grew (LeS LeZ)
      ImpTT => Grew (LeS (LeS LeZ))
    ImpTT => case ic of
      ImpFF => Grew (LeS (LeS LeZ))
      ImpFT => Grew (LeS (LeS LeZ))
      ImpTT => Grew (LeS (LeS (LeS LeZ)))
  ImpTT => case ib of
    ImpFF => case ic of
      ImpFF => Stable (MkSub ImpTT ImpFF ImpFF)
      ImpFT => Grew (LeS (LeS LeZ))
      ImpTT => Stable (MkSub ImpTT ImpFF ImpTT)
    ImpFT => case ic of
      ImpFF => Grew (LeS (LeS LeZ))
      ImpFT => Grew (LeS (LeS LeZ))
      ImpTT => Grew (LeS (LeS (LeS LeZ)))
    ImpTT => case ic of
      ImpFF => Stable (MkSub ImpTT ImpTT ImpFF)
      ImpFT => Grew (LeS (LeS (LeS LeZ)))
      ImpTT => Stable (MkSub ImpTT ImpTT ImpTT)

iter : (IF -> IF) -> Nat -> IF
iter f Z = MkIF F F F
iter f (S k) = f (iter f k)
asc : (f : IF -> IF) -> ((x : IF) -> (y : IF) -> Sub x y -> Sub (f x) (f y)) -> (n : Nat) -> Sub (iter f n) (iter f (S n))
asc f mono Z = bot_sub (iter f (S Z))
asc f mono (S k) = mono (iter f k) (iter f (S k)) (asc f mono k)
propagate : (f : IF -> IF) -> ((x : IF) -> (y : IF) -> Sub x y -> Sub (f x) (f y)) -> (k : Nat) -> Sub (iter f (S k)) (iter f k) -> Sub (iter f (S (S k))) (iter f (S k))
propagate f mono k fx = mono (iter f (S k)) (iter f k) fx

data Empty : Type where
Uninhabited Empty where
  uninhabited x impossible
le_irrefl_succ : (n : Nat) -> Le (S n) n -> Empty
le_irrefl_succ Z h impossible
le_irrefl_succ (S k) (LeS h2) = le_irrefl_succ k h2

size_bound : (x : IF) -> Le (size x) (S (S (S Z)))
size_bound (MkIF F F F) = LeZ
size_bound (MkIF F F T) = (LeS LeZ)
size_bound (MkIF F T F) = (LeS LeZ)
size_bound (MkIF F T T) = (LeS (LeS LeZ))
size_bound (MkIF T F F) = (LeS LeZ)
size_bound (MkIF T F T) = (LeS (LeS LeZ))
size_bound (MkIF T T F) = (LeS (LeS LeZ))
size_bound (MkIF T T T) = (LeS (LeS (LeS LeZ)))

data ChainState : IF -> IF -> Nat -> Type where
  CFixed : Sub next prev -> ChainState prev next n
  CSize  : Le n (size prev) -> ChainState prev next n
chain_bound : (f : IF -> IF) -> ((x : IF) -> (y : IF) -> Sub x y -> Sub (f x) (f y)) -> (n : Nat) -> ChainState (iter f n) (iter f (S n)) n
chain_bound f mono Z = CSize LeZ
chain_bound f mono (S k) = case chain_bound f mono k of
  CFixed fx => CFixed (propagate f mono k fx)
  CSize sz => case grow_or_eq (iter f k) (iter f (S k)) (asc f mono k) of
    Stable st => CFixed (propagate f mono k st)
    Grew g => CSize (le_trans (LeS sz) g)

map_lfp_le : (f : IF -> IF) -> ((x : IF) -> (y : IF) -> Sub x y -> Sub (f x) (f y)) -> Sub (f (iter f (S (S (S (S Z)))))) (iter f (S (S (S (S Z)))))
map_lfp_le f mono = case chain_bound f mono (S (S (S (S Z)))) of
  CFixed fx => fx
  CSize sz => absurd (le_irrefl_succ (S (S (S Z))) (le_trans sz (size_bound (iter f (S (S (S (S Z))))))))
