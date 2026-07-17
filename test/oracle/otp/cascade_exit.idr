%default total

data Trap = Trapping | NotTrapping
data Chain = CNil | CCons Trap Chain

data Cascade : Chain -> Chain -> Type where
  CascEmpty : Cascade CNil CNil
  CascStop : Cascade (CCons Trapping rest) (CCons Trapping rest)
  CascProp : Cascade rest after -> Cascade (CCons NotTrapping rest) after

data CascadeOf : Chain -> Type where
  MkCascadeOf : (after : Chain) -> Cascade before after -> CascadeOf before

run_cascade : (c : Chain) -> CascadeOf c
run_cascade CNil = MkCascadeOf CNil CascEmpty
run_cascade (CCons Trapping r) = MkCascadeOf (CCons Trapping r) CascStop
run_cascade (CCons NotTrapping r) = case run_cascade r of MkCascadeOf after casc => MkCascadeOf after (CascProp casc)
