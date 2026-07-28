%default total

data Nat' = Z | S Nat'
data List = LNil | LCons Nat' List

app : List -> List -> List
app LNil b = b
app (LCons x rest) b = LCons x (app rest b)

lcons_cong : (x : Nat') -> a = b -> LCons x a = LCons x b
lcons_cong x e = rewrite e in Refl

app_nil : (a : List) -> app a LNil = a
app_nil LNil = Refl
app_nil (LCons x rest) = lcons_cong x (app_nil rest)

app_assoc : (a : List) -> (b : List) -> (c : List) -> app (app a b) c = app a (app b c)
app_assoc LNil b c = Refl
app_assoc (LCons x rest) b c = lcons_cong x (app_assoc rest b c)

rev : List -> List
rev LNil = LNil
rev (LCons x rest) = app (rev rest) (LCons x LNil)

revacc : List -> List -> List
revacc LNil acc = acc
revacc (LCons x rest) acc = revacc rest (LCons x acc)

fast_rev : List -> List
fast_rev l = revacc l LNil

revacc_spec : (l : List) -> (acc : List) -> revacc l acc = app (rev l) acc
revacc_spec LNil acc = Refl
revacc_spec (LCons x rest) acc = trans (revacc_spec rest (LCons x acc)) (sym (app_assoc (rev rest) (LCons x LNil) acc))

fast_rev_correct : (l : List) -> fast_rev l = rev l
fast_rev_correct l = trans (revacc_spec l LNil) (app_nil (rev l))
