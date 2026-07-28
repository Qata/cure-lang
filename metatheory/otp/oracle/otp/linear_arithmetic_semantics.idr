-- Closed mirrors exercise the same zero/add/scale/normalization equations; the
-- Cure side additionally quantifies the reusable kernel-checked theorems.
%default total

dot : List Integer -> List Integer -> Integer
dot [] _ = 0
dot _ [] = 0
dot (coefficient :: coefficients) (value :: values) =
  coefficient * value + dot coefficients values

zeroHomomorphism : dot [0, 0] [7, -3] = 0
zeroHomomorphism = Refl

additionHomomorphism :
  dot [1 + 2, (-1) + 1] [4, 5] = dot [1, -1] [4, 5] + dot [2, 1] [4, 5]
additionHomomorphism = Refl

scalingHomomorphism :
  dot [2 * 1, 2 * (-1)] [4, 5] = 2 * dot [1, -1] [4, 5]
scalingHomomorphism = Refl

strictNormalization : ((dot [1] [3]) <= (4 - 1)) = ((dot [1] [3]) < 4)
strictNormalization = Refl

start : Bool
start = True
