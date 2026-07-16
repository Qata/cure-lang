%default total

data Tag = TInc | TDec | TQuery
data TagList = TNil | TCons Tag TagList

data Member : Tag -> TagList -> Type where
  MemHere : Member t (TCons t rest)
  MemThere : Member t rest -> Member t (TCons y rest)

data AllMember : TagList -> TagList -> Type where
  AMNil : AllMember TNil set
  AMCons : Member t set -> AllMember rest set -> AllMember (TCons t rest) set

data Proc = MkProc TagList TagList TagList

data WTProc : Proc -> Type where
  MkWTP : AllMember e set -> AllMember m set -> WTProc (MkProc set e m)

data System = SNil | SCons Proc System

data WTSys : System -> Type where
  WSNil : WTSys SNil
  WSCons : WTProc p -> WTSys rest -> WTSys (SCons p rest)

data Deliver : System -> System -> Type where
  DHere : Member t set -> Deliver (SCons (MkProc set e m) rest) (SCons (MkProc set (TCons t e) m) rest)
  DThere : Deliver rest rest2 -> Deliver (SCons p rest) (SCons p rest2)

preservation : WTSys b -> Deliver b a -> WTSys a
preservation (WSCons (MkWTP ame amm) wrest) (DHere mem) = WSCons (MkWTP (AMCons mem ame) amm) wrest
preservation (WSCons wtp wrest) (DThere d2) = WSCons wtp (preservation wrest d2)
