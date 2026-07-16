%default total
data Box = MkBox
data Widget = MkWidget
data Unit2 = U2
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
g : (1 _ : Box) -> Unit2
g c = let x = consume c in U2
