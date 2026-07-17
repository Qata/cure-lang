%default total

data ChildSpec = CA | CB | CC
data Children = CNil | CCons ChildSpec Children

data Child : ChildSpec -> Type where
  Alive : Child spec
  Restarting : Child spec

data Fleet : Children -> Type where
  FNil : Fleet CNil
  FCons : Child spec -> Fleet rest -> Fleet (CCons spec rest)

restart_all : Fleet specs -> Fleet specs
restart_all FNil = FNil
restart_all (FCons c rest) = FCons Alive (restart_all rest)

restart_one : Fleet (CCons spec rest) -> Fleet (CCons spec rest)
restart_one (FCons c others) = FCons Alive others

rest_for_one : Fleet specs -> Nat -> Fleet specs
rest_for_one f Z = restart_all f
rest_for_one FNil (S k2) = FNil
rest_for_one (FCons c rest) (S k2) = FCons c (rest_for_one rest k2)

establish : (specs : Children) -> Fleet specs
establish CNil = FNil
establish (CCons s rest) = FCons Alive (establish rest)

data Pool : ChildSpec -> Type where
  PNil : Pool spec
  PCons : Child spec -> Pool spec -> Pool spec

start_child : Pool spec -> Pool spec
start_child p = PCons Alive p

terminate_child : Pool spec -> Pool spec
terminate_child PNil = PNil
terminate_child (PCons c rest) = rest

restart_pool : Pool spec -> Pool spec
restart_pool PNil = PNil
restart_pool (PCons c rest) = PCons Alive (restart_pool rest)

pool_size : Pool spec -> Nat
pool_size PNil = Z
pool_size (PCons c rest) = S (pool_size rest)
start_grows : (p : Pool spec) -> pool_size (start_child p) = S (pool_size p)
start_grows p = Refl
terminate_start_id : (p : Pool spec) -> terminate_child (start_child p) = p
terminate_start_id p = Refl
restart_preserves_size : (p : Pool spec) -> pool_size (restart_pool p) = pool_size p
restart_preserves_size PNil = Refl
restart_preserves_size (PCons c rest) = cong S (restart_preserves_size rest)
