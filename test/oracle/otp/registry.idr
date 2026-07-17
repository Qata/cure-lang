%default total

data Pid = MkPid

data GenServer : Type -> Type -> Type where
  MkGen : Pid -> GenServer q r

data PidOption = NoPid | SomePid Pid

server_pid : GenServer q r -> Pid
server_pid (MkGen p) = p

expect_server : Pid -> GenServer q r
expect_server p = MkGen p

with_pid : PidOption -> (Pid -> s) -> (() -> s) -> s
with_pid (SomePid p) on_found on_absent = on_found p
with_pid NoPid on_found on_absent = on_absent ()

found : PidOption
found = SomePid MkPid

absent : PidOption
absent = NoPid
