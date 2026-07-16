%default total
data Box = MkBox
data Widget = MkWidget
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
g : (1 _ : Box) -> Widget
g c = let x = consume c in x
