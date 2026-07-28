%default total

data Nat' = Z | S Nat'
data Msg = MReq | MAns
data Local = LSend Msg Local | LRecv Msg Local | LEnd
data Sup = Run Local Local Nat' | Completed | Abandoned

proto_len : Local -> Nat'
proto_len LEnd = Z
proto_len (LSend m k) = S (proto_len k)
proto_len (LRecv m k) = S (proto_len k)

progress : Sup -> Sup
progress (Run orig LEnd b) = Completed
progress (Run orig (LSend m k) b) = Run orig k b
progress (Run orig (LRecv m k) b) = Run orig k b
progress Completed = Completed
progress Abandoned = Abandoned

crash : Sup -> Sup
crash (Run orig cur Z) = Abandoned
crash (Run orig cur (S b2)) = Run orig orig b2
crash Completed = Completed
crash Abandoned = Abandoned

progresses : Sup -> Nat' -> Sup
progresses s Z = s
progresses s (S m) = progresses (progress s) m

crashes : Sup -> Nat' -> Sup
crashes s Z = s
crashes s (S m) = crashes (crash s) m

-- progress completes: S(proto_len cur) progress steps reach Completed.
progress_completes : (orig : Local) -> (cur : Local) -> (b : Nat') -> progresses (Run orig cur b) (S (proto_len cur)) = Completed
progress_completes orig LEnd b = Refl
progress_completes orig (LSend m k) b = progress_completes orig k b
progress_completes orig (LRecv m k) b = progress_completes orig k b

-- crash abandons: S(budget) crashes reach Abandoned.
crash_abandons : (orig : Local) -> (cur : Local) -> (b : Nat') -> crashes (Run orig cur b) (S b) = Abandoned
crash_abandons orig cur Z = Refl
crash_abandons orig cur (S b2) = crash_abandons orig orig b2

-- both terminal states absorbing under either event.
completed_absorbs_crash : crash Completed = Completed
completed_absorbs_crash = Refl
completed_absorbs_progress : progress Completed = Completed
completed_absorbs_progress = Refl
abandoned_absorbs_progress : progress Abandoned = Abandoned
abandoned_absorbs_progress = Refl
abandoned_absorbs_crash : crash Abandoned = Abandoned
abandoned_absorbs_crash = Refl
