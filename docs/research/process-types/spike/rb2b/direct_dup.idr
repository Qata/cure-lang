%default total
data Box = MkBox
data Pair = MkPair Box Box
f : (1 _ : Box) -> Pair
f c = MkPair c c
