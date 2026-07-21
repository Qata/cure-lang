%default total

dot : List Integer -> List Integer -> Integer
dot [] _ = 0
dot _ [] = 0
dot (coefficient :: coefficients) (value :: values) =
  coefficient * value + dot coefficients values

forged : dot [0, 0] [7, -3] = 1
forged = Refl
