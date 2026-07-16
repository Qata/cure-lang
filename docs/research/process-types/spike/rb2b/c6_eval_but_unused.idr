%default total
data Box = MkBox
data Widget = MkWidget
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
consume2 : (1 _ : Box) -> Widget
consume2 MkBox = MkWidget
-- x unused, but c consumed in BOTH the let-value and the body: c used twice.
g : (1 _ : Box) -> Widget
g c = let x = consume c in consume2 c
