%default total

-- NEGATION NORMAL FORM is meaning-preserving. Propositional formulas over variables; nnf pushes every
-- negation down to the leaves (via De Morgan and double-negation), nnf_neg computing the NNF of the negation.
-- nnfCorrect proves eval (nnf f) env = eval f env for every formula and assignment, with its mutual companion
-- nnfNegCorrect (eval (nnf_neg f) env = not (eval f env)), by mutual induction discharged by De Morgan's laws.

data Natt = Z | S Natt
data Bool2 = F | T

notb : Bool2 -> Bool2
notb T = F
notb F = T

andb : Bool2 -> Bool2 -> Bool2
andb T b = b
andb F b = F

orb : Bool2 -> Bool2 -> Bool2
orb T b = T
orb F b = b

dmAnd : (a : Bool2) -> (b : Bool2) -> notb (andb a b) = orb (notb a) (notb b)
dmAnd T T = Refl
dmAnd T F = Refl
dmAnd F T = Refl
dmAnd F F = Refl

dmOr : (a : Bool2) -> (b : Bool2) -> notb (orb a b) = andb (notb a) (notb b)
dmOr T T = Refl
dmOr T F = Refl
dmOr F T = Refl
dmOr F F = Refl

notnot : (a : Bool2) -> notb (notb a) = a
notnot T = Refl
notnot F = Refl

andbCong2 : (a : Bool2) -> (ap : Bool2) -> (b : Bool2) -> (bp : Bool2) -> a = ap -> b = bp -> andb a b = andb ap bp
andbCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

orbCong2 : (a : Bool2) -> (ap : Bool2) -> (b : Bool2) -> (bp : Bool2) -> a = ap -> b = bp -> orb a b = orb ap bp
orbCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

data Env = ENil | ECons Bool2 Env

lookup : Natt -> Env -> Bool2
lookup Z ENil = F
lookup Z (ECons x rest) = x
lookup (S k) ENil = F
lookup (S k) (ECons x rest) = lookup k rest

data Formula = FVar Natt | FNot Formula | FAnd Formula Formula | FOr Formula Formula

eval : Formula -> Env -> Bool2
eval (FVar v) env = lookup v env
eval (FNot g) env = notb (eval g env)
eval (FAnd a b) env = andb (eval a env) (eval b env)
eval (FOr a b) env = orb (eval a env) (eval b env)

nnf : Formula -> Formula
nnfNeg : Formula -> Formula
nnf (FVar v) = FVar v
nnf (FNot g) = nnfNeg g
nnf (FAnd a b) = FAnd (nnf a) (nnf b)
nnf (FOr a b) = FOr (nnf a) (nnf b)
nnfNeg (FVar v) = FNot (FVar v)
nnfNeg (FNot g) = nnf g
nnfNeg (FAnd a b) = FOr (nnfNeg a) (nnfNeg b)
nnfNeg (FOr a b) = FAnd (nnfNeg a) (nnfNeg b)

nnfCorrect : (f : Formula) -> (env : Env) -> eval (nnf f) env = eval f env
nnfNegCorrect : (f : Formula) -> (env : Env) -> eval (nnfNeg f) env = notb (eval f env)
nnfCorrect (FVar v) env = Refl
nnfCorrect (FNot g) env = nnfNegCorrect g env
nnfCorrect (FAnd a b) env = andbCong2 (eval (nnf a) env) (eval a env) (eval (nnf b) env) (eval b env) (nnfCorrect a env) (nnfCorrect b env)
nnfCorrect (FOr a b) env = orbCong2 (eval (nnf a) env) (eval a env) (eval (nnf b) env) (eval b env) (nnfCorrect a env) (nnfCorrect b env)
nnfNegCorrect (FVar v) env = Refl
nnfNegCorrect (FNot g) env = trans (nnfCorrect g env) (sym (notnot (eval g env)))
nnfNegCorrect (FAnd a b) env = trans (orbCong2 (eval (nnfNeg a) env) (notb (eval a env)) (eval (nnfNeg b) env) (notb (eval b env)) (nnfNegCorrect a env) (nnfNegCorrect b env)) (sym (dmAnd (eval a env) (eval b env)))
nnfNegCorrect (FOr a b) env = trans (andbCong2 (eval (nnfNeg a) env) (notb (eval a env)) (eval (nnfNeg b) env) (notb (eval b env)) (nnfNegCorrect a env) (nnfNegCorrect b env)) (sym (dmOr (eval a env) (eval b env)))
