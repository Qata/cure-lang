%default total

data CallError = Timeout | NoProc | ServerDied

data CallOutcome : Type -> Type where
  Replied : r -> CallOutcome r
  Failed : CallError -> CallOutcome r

resume : CallOutcome r -> (r -> s) -> (CallError -> s) -> s
resume (Replied x) on_reply on_fail = on_reply x
resume (Failed e) on_reply on_fail = on_fail e

data Reply = RVal

ok_call : CallOutcome Reply
ok_call = Replied RVal

dead_call : CallOutcome Reply
dead_call = Failed ServerDied
