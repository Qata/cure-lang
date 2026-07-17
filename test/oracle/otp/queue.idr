%default total

data QList = QNil | QCons Nat QList

append : QList -> QList -> QList
append QNil ys = ys
append (QCons h t) ys = QCons h (append t ys)

reverse : QList -> QList
reverse QNil = QNil
reverse (QCons h t) = append (reverse t) (QCons h QNil)

cons_cong : (h : Nat) -> a = b -> QCons h a = QCons h b
cons_cong h Refl = Refl

append_assoc : (xs : QList) -> (ys : QList) -> (zs : QList) -> append (append xs ys) zs = append xs (append ys zs)
append_assoc QNil ys zs = Refl
append_assoc (QCons h t) ys zs = cons_cong h (append_assoc t ys zs)

data Q = MkQ QList QList

to_list : Q -> QList
to_list (MkQ f b) = append f (reverse b)

enqueue : Nat -> Q -> Q
enqueue x (MkQ f b) = MkQ f (QCons x b)

enqueue_appends : (x : Nat) -> (q : Q) -> to_list (enqueue x q) = append (to_list q) (QCons x QNil)
enqueue_appends x (MkQ f b) = sym (append_assoc f (reverse b) (QCons x QNil))
