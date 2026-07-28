%default total

data Nat' = Z | S Nat'
data Msg = MReq | MAns
data Local = LSend Msg Local | LRecv Msg Local | LEnd

plus : Nat' -> Nat' -> Nat'
plus Z b = b
plus (S k) b = S (plus k b)

proto_len : Local -> Nat'
proto_len LEnd = Z
proto_len (LSend m k) = S (proto_len k)
proto_len (LRecv m k) = S (proto_len k)

data Serve : Local -> Local -> Type where
  SDone : Serve l l
  SSendStep : Serve k post -> Serve (LSend m k) post
  SRecvStep : Serve k post -> Serve (LRecv m k) post

run_len : Serve pre post -> Nat'
run_len SDone = Z
run_len (SSendStep rest) = S (run_len rest)
run_len (SRecvStep rest) = S (run_len rest)

snat_cong : {a : Nat'} -> {b : Nat'} -> a = b -> S a = S b
snat_cong e = rewrite e in Refl

plus_zero : (n : Nat') -> plus n Z = n
plus_zero Z = Refl
plus_zero (S k) = snat_cong (plus_zero k)

-- conservation: steps taken + obligations remaining = total protocol length.
conservation : {pre : Local} -> {post : Local} -> (s : Serve pre post) -> plus (run_len s) (proto_len post) = proto_len pre
conservation SDone = Refl
conservation (SSendStep rest) = snat_cong (conservation rest)
conservation (SRecvStep rest) = snat_cong (conservation rest)

-- a completing run performs exactly proto_len pre steps.
complete_run : (s : Serve pre LEnd) -> run_len s = proto_len pre
complete_run s = trans (sym (plus_zero (run_len s))) (conservation s)

data Terminated : Local -> Type where
  TNormal : Terminated LEnd
  TCrash : Terminated l

-- a completed run may stop normally (TNormal well-typed only at LEnd).
clean_shutdown : (s : Serve pre LEnd) -> Terminated LEnd
clean_shutdown s = TNormal

-- a crash may stop at any session state.
crash_anytime : (l : Local) -> Terminated l
crash_anytime l = TCrash
