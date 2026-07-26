%default total

-- COMPILER CORRECTNESS WITH VARIABLES AND ENVIRONMENTS. The source language gains De Bruijn variables (Var k
-- reads the k-th environment entry); the target stack machine gains a Load instruction that pushes a variable
-- from the read-only environment threaded through exec. compileCorrect proves exec (compile e) env s =
-- eval e env :: s for every expression, environment, and initial stack -- the classic "compiling with an
-- environment" result, a real step up from the closed-expression case.

data Natt = Z | S Natt

plus : Natt -> Natt -> Natt
plus Z b = b
plus (S k) b = S (plus k b)

times : Natt -> Natt -> Natt
times Z b = Z
times (S k) b = plus b (times k b)

data NL = NNil | NCons Natt NL

lookup : Natt -> NL -> Natt
lookup Z NNil = Z
lookup Z (NCons x rest) = x
lookup (S k) NNil = Z
lookup (S k) (NCons x rest) = lookup k rest

data Expr = Lit Natt | Var Natt | Add Expr Expr | Mul Expr Expr

eval : Expr -> NL -> Natt
eval (Lit n) env = n
eval (Var k) env = lookup k env
eval (Add a b) env = plus (eval a env) (eval b env)
eval (Mul a b) env = times (eval a env) (eval b env)

data Instr = Push Natt | Load Natt | AddOp | MulOp
data Program = PNil | PCons Instr Program

app : Program -> Program -> Program
app PNil q = q
app (PCons i is) q = PCons i (app is q)

compile : Expr -> Program
compile (Lit n) = PCons (Push n) PNil
compile (Var k) = PCons (Load k) PNil
compile (Add a b) = app (compile a) (app (compile b) (PCons AddOp PNil))
compile (Mul a b) = app (compile a) (app (compile b) (PCons MulOp PNil))

exec : Program -> NL -> NL -> NL
exec PNil env s = s
exec (PCons (Push n) rest) env s = exec rest env (NCons n s)
exec (PCons (Load k) rest) env s = exec rest env (NCons (lookup k env) s)
exec (PCons AddOp rest) env NNil = exec rest env NNil
exec (PCons AddOp rest) env (NCons top NNil) = exec rest env (NCons top NNil)
exec (PCons AddOp rest) env (NCons top (NCons below s2)) = exec rest env (NCons (plus below top) s2)
exec (PCons MulOp rest) env NNil = exec rest env NNil
exec (PCons MulOp rest) env (NCons top NNil) = exec rest env (NCons top NNil)
exec (PCons MulOp rest) env (NCons top (NCons below s2)) = exec rest env (NCons (times below top) s2)

execAppend : (p : Program) -> (q : Program) -> (env : NL) -> (s : NL) -> exec (app p q) env s = exec q env (exec p env s)
execAppend PNil q env s = Refl
execAppend (PCons (Push n) rest) q env s = execAppend rest q env (NCons n s)
execAppend (PCons (Load k) rest) q env s = execAppend rest q env (NCons (lookup k env) s)
execAppend (PCons AddOp rest) q env NNil = execAppend rest q env NNil
execAppend (PCons AddOp rest) q env (NCons top NNil) = execAppend rest q env (NCons top NNil)
execAppend (PCons AddOp rest) q env (NCons top (NCons below s2)) = execAppend rest q env (NCons (plus below top) s2)
execAppend (PCons MulOp rest) q env NNil = execAppend rest q env NNil
execAppend (PCons MulOp rest) q env (NCons top NNil) = execAppend rest q env (NCons top NNil)
execAppend (PCons MulOp rest) q env (NCons top (NCons below s2)) = execAppend rest q env (NCons (times below top) s2)

execCong : (p : Program) -> (env : NL) -> (s1 : NL) -> (s2 : NL) -> s1 = s2 -> exec p env s1 = exec p env s2
execCong p env s1 s2 e = rewrite e in Refl

compileCorrect : (e : Expr) -> (env : NL) -> (s : NL) -> exec (compile e) env s = NCons (eval e env) s
compileCorrect (Lit n) env s = Refl
compileCorrect (Var k) env s = Refl
compileCorrect (Add a b) env s =
  trans (execAppend (compile a) (app (compile b) (PCons AddOp PNil)) env s)
    (trans (execCong (app (compile b) (PCons AddOp PNil)) env (exec (compile a) env s) (NCons (eval a env) s) (compileCorrect a env s))
      (trans (execAppend (compile b) (PCons AddOp PNil) env (NCons (eval a env) s))
        (trans (execCong (PCons AddOp PNil) env (exec (compile b) env (NCons (eval a env) s)) (NCons (eval b env) (NCons (eval a env) s)) (compileCorrect b env (NCons (eval a env) s)))
          Refl)))
compileCorrect (Mul a b) env s =
  trans (execAppend (compile a) (app (compile b) (PCons MulOp PNil)) env s)
    (trans (execCong (app (compile b) (PCons MulOp PNil)) env (exec (compile a) env s) (NCons (eval a env) s) (compileCorrect a env s))
      (trans (execAppend (compile b) (PCons MulOp PNil) env (NCons (eval a env) s))
        (trans (execCong (PCons MulOp PNil) env (exec (compile b) env (NCons (eval a env) s)) (NCons (eval b env) (NCons (eval a env) s)) (compileCorrect b env (NCons (eval a env) s)))
          Refl)))
