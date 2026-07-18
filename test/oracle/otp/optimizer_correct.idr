%default total

-- A VERIFIED OPTIMIZING COMPILER. Constant folding (fold) evaluates constant subexpressions at compile time;
-- foldPreserves proves it never changes a program's value (eval (fold e) = eval e -- semantic preservation of
-- a transformation). Composed with compiler correctness (compileCorrect), optCorrect proves the OPTIMIZED
-- compilation is still correct against the ORIGINAL semantics: exec (compile (fold e)) s = eval e :: s.

data Natt = Z | S Natt

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

times : Natt -> Natt -> Natt
times Z b = Z
times (S k) b = plus b (times k b)

data Expr = Lit Natt | Add Expr Expr | Mul Expr Expr

eval : Expr -> Natt
eval (Lit n) = n
eval (Add a b) = plus (eval a) (eval b)
eval (Mul a b) = times (eval a) (eval b)

data Instr = Push Natt | AddOp | MulOp
data Program = PNil | PCons Instr Program
data Stack = SNil | SCons Natt Stack

app : Program -> Program -> Program
app PNil q = q
app (PCons i is) q = PCons i (app is q)

compile : Expr -> Program
compile (Lit n) = PCons (Push n) PNil
compile (Add a b) = app (compile a) (app (compile b) (PCons AddOp PNil))
compile (Mul a b) = app (compile a) (app (compile b) (PCons MulOp PNil))

exec : Program -> Stack -> Stack
exec PNil s = s
exec (PCons (Push n) rest) s = exec rest (SCons n s)
exec (PCons AddOp rest) SNil = exec rest SNil
exec (PCons AddOp rest) (SCons top SNil) = exec rest (SCons top SNil)
exec (PCons AddOp rest) (SCons top (SCons below s2)) = exec rest (SCons (plus below top) s2)
exec (PCons MulOp rest) SNil = exec rest SNil
exec (PCons MulOp rest) (SCons top SNil) = exec rest (SCons top SNil)
exec (PCons MulOp rest) (SCons top (SCons below s2)) = exec rest (SCons (times below top) s2)

execAppend : (p : Program) -> (q : Program) -> (s : Stack) -> exec (app p q) s = exec q (exec p s)
execAppend PNil q s = Refl
execAppend (PCons (Push n) rest) q s = execAppend rest q (SCons n s)
execAppend (PCons AddOp rest) q SNil = execAppend rest q SNil
execAppend (PCons AddOp rest) q (SCons top SNil) = execAppend rest q (SCons top SNil)
execAppend (PCons AddOp rest) q (SCons top (SCons below s2)) = execAppend rest q (SCons (plus below top) s2)
execAppend (PCons MulOp rest) q SNil = execAppend rest q SNil
execAppend (PCons MulOp rest) q (SCons top SNil) = execAppend rest q (SCons top SNil)
execAppend (PCons MulOp rest) q (SCons top (SCons below s2)) = execAppend rest q (SCons (times below top) s2)

execCong : (p : Program) -> (s1 : Stack) -> (s2 : Stack) -> s1 = s2 -> exec p s1 = exec p s2
execCong p s1 s2 e = rewrite e in Refl

compileCorrect : (e : Expr) -> (s : Stack) -> exec (compile e) s = SCons (eval e) s
compileCorrect (Lit n) s = Refl
compileCorrect (Add a b) s =
  trans (execAppend (compile a) (app (compile b) (PCons AddOp PNil)) s)
    (trans (execCong (app (compile b) (PCons AddOp PNil)) (exec (compile a) s) (SCons (eval a) s) (compileCorrect a s))
      (trans (execAppend (compile b) (PCons AddOp PNil) (SCons (eval a) s))
        (trans (execCong (PCons AddOp PNil) (exec (compile b) (SCons (eval a) s)) (SCons (eval b) (SCons (eval a) s)) (compileCorrect b (SCons (eval a) s)))
          Refl)))
compileCorrect (Mul a b) s =
  trans (execAppend (compile a) (app (compile b) (PCons MulOp PNil)) s)
    (trans (execCong (app (compile b) (PCons MulOp PNil)) (exec (compile a) s) (SCons (eval a) s) (compileCorrect a s))
      (trans (execAppend (compile b) (PCons MulOp PNil) (SCons (eval a) s))
        (trans (execCong (PCons MulOp PNil) (exec (compile b) (SCons (eval a) s)) (SCons (eval b) (SCons (eval a) s)) (compileCorrect b (SCons (eval a) s)))
          Refl)))

foldAdd : Expr -> Expr -> Expr
foldAdd (Lit m) (Lit k) = Lit (plus m k)
foldAdd (Lit m) (Add p q) = Add (Lit m) (Add p q)
foldAdd (Lit m) (Mul p q) = Add (Lit m) (Mul p q)
foldAdd (Add p q) y = Add (Add p q) y
foldAdd (Mul p q) y = Add (Mul p q) y

foldMul : Expr -> Expr -> Expr
foldMul (Lit m) (Lit k) = Lit (times m k)
foldMul (Lit m) (Add p q) = Mul (Lit m) (Add p q)
foldMul (Lit m) (Mul p q) = Mul (Lit m) (Mul p q)
foldMul (Add p q) y = Mul (Add p q) y
foldMul (Mul p q) y = Mul (Mul p q) y

fold : Expr -> Expr
fold (Lit n) = Lit n
fold (Add a b) = foldAdd (fold a) (fold b)
fold (Mul a b) = foldMul (fold a) (fold b)

plusCong2 : (a : Natt) -> (ap : Natt) -> (b : Natt) -> (bp : Natt) -> a = ap -> b = bp -> plus a b = plus ap bp
plusCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

timesCong2 : (a : Natt) -> (ap : Natt) -> (b : Natt) -> (bp : Natt) -> a = ap -> b = bp -> times a b = times ap bp
timesCong2 a ap b bp ea eb = rewrite ea in rewrite eb in Refl

sconsCong : (a : Natt) -> (b : Natt) -> (s : Stack) -> a = b -> SCons a s = SCons b s
sconsCong a b s e = rewrite e in Refl

foldAddCorrect : (x : Expr) -> (y : Expr) -> eval (foldAdd x y) = plus (eval x) (eval y)
foldAddCorrect (Lit m) (Lit k) = Refl
foldAddCorrect (Lit m) (Add p q) = Refl
foldAddCorrect (Lit m) (Mul p q) = Refl
foldAddCorrect (Add p q) y = Refl
foldAddCorrect (Mul p q) y = Refl

foldMulCorrect : (x : Expr) -> (y : Expr) -> eval (foldMul x y) = times (eval x) (eval y)
foldMulCorrect (Lit m) (Lit k) = Refl
foldMulCorrect (Lit m) (Add p q) = Refl
foldMulCorrect (Lit m) (Mul p q) = Refl
foldMulCorrect (Add p q) y = Refl
foldMulCorrect (Mul p q) y = Refl

foldPreserves : (e : Expr) -> eval (fold e) = eval e
foldPreserves (Lit n) = Refl
foldPreserves (Add a b) = trans (foldAddCorrect (fold a) (fold b)) (plusCong2 (eval (fold a)) (eval a) (eval (fold b)) (eval b) (foldPreserves a) (foldPreserves b))
foldPreserves (Mul a b) = trans (foldMulCorrect (fold a) (fold b)) (timesCong2 (eval (fold a)) (eval a) (eval (fold b)) (eval b) (foldPreserves a) (foldPreserves b))

optCorrect : (e : Expr) -> (s : Stack) -> exec (compile (fold e)) s = SCons (eval e) s
optCorrect e s = trans (compileCorrect (fold e) s) (sconsCong (eval (fold e)) (eval e) s (foldPreserves e))
