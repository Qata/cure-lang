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

establish : (specs : Children) -> Fleet specs
establish CNil = FNil
establish (CCons s rest) = FCons Alive (establish rest)
