%default total
data Box = MkBox
data Widget = MkWidget
data WPair = MkWPair Widget Widget
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
g : (1 _ : Box) -> WPair
g c = let x = consume c in MkWPair x x
