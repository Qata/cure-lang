-- Executable mirror of the dimension-safe Farkas combination layer.
%default total
%unbound_implicits off

data Relation = LessOrEqual | LessThan

record LinearAtom where
  constructor MkAtom
  coefficients : List Integer
  constant : Integer
  relation : Relation

dot : List Integer -> List Integer -> Integer
dot [] _ = 0
dot _ [] = 0
dot (c :: cs) (v :: vs) = c * v + dot cs vs

evaluateAtom : LinearAtom -> List Integer -> Bool
evaluateAtom atom env = case atom.relation of
  LessOrEqual => dot atom.coefficients env <= atom.constant
  LessThan => dot atom.coefficients env < atom.constant

evaluateAtomChecked : LinearAtom -> List Integer -> Maybe Bool
evaluateAtomChecked atom env =
  if length atom.coefficients == length env then Just (evaluateAtom atom env) else Nothing

negateAtom : LinearAtom -> LinearAtom
negateAtom atom = case atom.relation of
  LessOrEqual => MkAtom (map negate atom.coefficients) (negate atom.constant) LessThan
  LessThan => MkAtom (map negate atom.coefficients) (negate atom.constant) LessOrEqual

normalizeAtom : LinearAtom -> LinearAtom
normalizeAtom atom = case atom.relation of
  LessOrEqual => atom
  LessThan => MkAtom atom.coefficients (atom.constant - 1) LessOrEqual

scaleAtom : Nat -> LinearAtom -> LinearAtom
scaleAtom k atom =
  let n = normalizeAtom atom
      scalar = cast k
  in MkAtom (map (scalar *) n.coefficients) (scalar * n.constant) LessOrEqual

addCoefficients : List Integer -> List Integer -> Maybe (List Integer)
addCoefficients [] [] = Just []
addCoefficients [] (_ :: _) = Nothing
addCoefficients (_ :: _) [] = Nothing
addCoefficients (x :: xs) (y :: ys) = case addCoefficients xs ys of
  Nothing => Nothing
  Just rest => Just ((x + y) :: rest)

addAtoms : LinearAtom -> LinearAtom -> Maybe LinearAtom
addAtoms left right =
  let l = normalizeAtom left
      r = normalizeAtom right
  in case addCoefficients l.coefficients r.coefficients of
    Nothing => Nothing
    Just cs => Just (MkAtom cs (l.constant + r.constant) LessOrEqual)

zeros : Nat -> List Integer
zeros Z = []
zeros (S k) = 0 :: zeros k

combine : Nat -> List LinearAtom -> List Nat -> Maybe LinearAtom
combine dimension [] [] = Just (MkAtom (zeros dimension) 0 LessOrEqual)
combine dimension [] (_ :: _) = Nothing
combine dimension (_ :: _) [] = Nothing
combine dimension (atom :: atoms) (k :: ks) = case combine dimension atoms ks of
  Nothing => Nothing
  Just accumulator => addAtoms (scaleAtom k atom) accumulator

allDimensions : Nat -> List LinearAtom -> Bool
allDimensions dimension [] = True
allDimensions dimension (atom :: rest) =
  length atom.coefficients == dimension && allDimensions dimension rest

allZero : List Integer -> Bool
allZero [] = True
allZero (x :: xs) = x == 0 && allZero xs

manifestContradiction : LinearAtom -> Bool
manifestContradiction atom = case atom.relation of
  LessThan => False
  LessOrEqual => allZero atom.coefficients && atom.constant < 0

checkCandidate : List LinearAtom -> LinearAtom -> List Nat -> Bool
checkCandidate hypotheses goal witness =
  let dimension = length goal.coefficients
      atoms = hypotheses ++ [negateAtom goal]
  in if allDimensions dimension atoms && length atoms == length witness
       then case combine dimension atoms witness of
         Nothing => False
         Just atom => manifestContradiction atom
       else False

aNonnegative : LinearAtom
aNonnegative = MkAtom [-1, 0] 0 LessOrEqual

bNonnegative : LinearAtom
bNonnegative = MkAtom [0, -1] 0 LessOrEqual

positiveGoal : LinearAtom
positiveGoal = MkAtom [-2, -3] 0 LessOrEqual

accepted : checkCandidate [aNonnegative, bNonnegative] positiveGoal [2, 3, 1] = True
accepted = Refl

forgedRejected : checkCandidate [aNonnegative, bNonnegative] positiveGoal [1, 1, 1] = False
forgedRejected = Refl

wrongLengthRejected : checkCandidate [aNonnegative, bNonnegative] positiveGoal [2, 3] = False
wrongLengthRejected = Refl

wrongDimensionRejected : checkCandidate [MkAtom [-1] 0 LessOrEqual] positiveGoal [1, 1] = False
wrongDimensionRejected = Refl

wrongValuationRejected : evaluateAtomChecked positiveGoal [1] = Nothing
wrongValuationRejected = Refl

-- 2n=1 is integer-inconsistent but rationally satisfiable. This checks one
-- candidate only; it intentionally makes no completeness claim for integers.
boundaryHypotheses : List LinearAtom
boundaryHypotheses = [MkAtom [2] 1 LessOrEqual, MkAtom [-2] (-1) LessOrEqual]

boundaryGoal : LinearAtom
boundaryGoal = MkAtom [0] (-1) LessOrEqual

boundarySampleRejected : checkCandidate boundaryHypotheses boundaryGoal [1, 1, 1] = False
boundarySampleRejected = Refl

start : Bool
start = checkCandidate [aNonnegative, bNonnegative] positiveGoal [2, 3, 1]
