%default total

data Kind = KLens | KAffine | KTraversal

Foci : Kind -> Type
Foci KLens = Unit
Foci KAffine = Bool
Foci KTraversal = Unit

mkLens : Foci KLens
mkLens = ()

okAffine : Foci KAffine
okAffine = True
