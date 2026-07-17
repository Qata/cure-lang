%default total

data GKey = GA | GB | GC
data GCmp = GLt | GEq | GGt
data GBit = BF | BT
data GOpt = GNone | GSome Nat

gcmp : GKey -> GKey -> GCmp
gcmp GA GA = GEq
gcmp GA GB = GLt
gcmp GA GC = GLt
gcmp GB GA = GGt
gcmp GB GB = GEq
gcmp GB GC = GLt
gcmp GC GA = GGt
gcmp GC GB = GGt
gcmp GC GC = GEq

gkeq : GKey -> GKey -> GBit
gkeq GA GA = BT
gkeq GA GB = BF
gkeq GA GC = BF
gkeq GB GA = BF
gkeq GB GB = BT
gkeq GB GC = BF
gkeq GC GA = BF
gkeq GC GB = BF
gkeq GC GC = BT

data GTree = GLeaf | GNode GTree GKey Nat GTree

lookup : GKey -> GTree -> GOpt
lookup k GLeaf = GNone
lookup k (GNode l v w r) = case gcmp k v of
  GLt => lookup k l
  GEq => GSome w
  GGt => lookup k r

insert : GKey -> Nat -> GTree -> GTree
insert k val GLeaf = GNode GLeaf k val GLeaf
insert k val (GNode l v w r) = case gcmp k v of
  GLt => GNode (insert k val l) v w r
  GEq => GNode l v val r
  GGt => GNode l v w (insert k val r)

lookup_insert_eq : (k : GKey) -> (val : Nat) -> (t : GTree) -> lookup k (insert k val t) = GSome val
lookup_insert_eq GA val GLeaf = Refl
lookup_insert_eq GB val GLeaf = Refl
lookup_insert_eq GC val GLeaf = Refl
lookup_insert_eq GA val (GNode l GA w r) = Refl
lookup_insert_eq GA val (GNode l GB w r) = lookup_insert_eq GA val l
lookup_insert_eq GA val (GNode l GC w r) = lookup_insert_eq GA val l
lookup_insert_eq GB val (GNode l GA w r) = lookup_insert_eq GB val r
lookup_insert_eq GB val (GNode l GB w r) = Refl
lookup_insert_eq GB val (GNode l GC w r) = lookup_insert_eq GB val l
lookup_insert_eq GC val (GNode l GA w r) = lookup_insert_eq GC val r
lookup_insert_eq GC val (GNode l GB w r) = lookup_insert_eq GC val r
lookup_insert_eq GC val (GNode l GC w r) = Refl

btNeBf : BT = BF -> Void
btNeBf Refl impossible

lookup_insert_neq : (x : GKey) -> (k : GKey) -> (val : Nat) -> (t : GTree) -> gkeq x k = BF -> lookup x (insert k val t) = lookup x t
lookup_insert_neq GA GA val t neq = void (btNeBf neq)
lookup_insert_neq GB GB val t neq = void (btNeBf neq)
lookup_insert_neq GC GC val t neq = void (btNeBf neq)
lookup_insert_neq GA GB val GLeaf neq = Refl
lookup_insert_neq GA GB val (GNode l GA w r) neq = Refl
lookup_insert_neq GA GB val (GNode l GB w r) neq = Refl
lookup_insert_neq GA GB val (GNode l GC w r) neq = lookup_insert_neq GA GB val l neq
lookup_insert_neq GA GC val GLeaf neq = Refl
lookup_insert_neq GA GC val (GNode l GA w r) neq = Refl
lookup_insert_neq GA GC val (GNode l GB w r) neq = Refl
lookup_insert_neq GA GC val (GNode l GC w r) neq = Refl
lookup_insert_neq GB GA val GLeaf neq = Refl
lookup_insert_neq GB GA val (GNode l GA w r) neq = Refl
lookup_insert_neq GB GA val (GNode l GB w r) neq = Refl
lookup_insert_neq GB GA val (GNode l GC w r) neq = lookup_insert_neq GB GA val l neq
lookup_insert_neq GB GC val GLeaf neq = Refl
lookup_insert_neq GB GC val (GNode l GA w r) neq = lookup_insert_neq GB GC val r neq
lookup_insert_neq GB GC val (GNode l GB w r) neq = Refl
lookup_insert_neq GB GC val (GNode l GC w r) neq = Refl
lookup_insert_neq GC GA val GLeaf neq = Refl
lookup_insert_neq GC GA val (GNode l GA w r) neq = Refl
lookup_insert_neq GC GA val (GNode l GB w r) neq = Refl
lookup_insert_neq GC GA val (GNode l GC w r) neq = Refl
lookup_insert_neq GC GB val GLeaf neq = Refl
lookup_insert_neq GC GB val (GNode l GA w r) neq = lookup_insert_neq GC GB val r neq
lookup_insert_neq GC GB val (GNode l GB w r) neq = Refl
lookup_insert_neq GC GB val (GNode l GC w r) neq = Refl
