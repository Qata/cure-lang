%default total

-- COMPILER CORRECTNESS for arithmetic expressions (McCarthy-Painter / Hutton). Compile expressions to a
-- stack machine and prove exec (compile e) s = eval e :: s -- the compiled code leaves exactly the
-- evaluator's value on top of the stack, for every expression and initial stack. Source semantics (eval) and
-- target semantics (exec) agree via compile. The crux is execAppend (exec distributes over ++), then
-- induction on the expression.

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
