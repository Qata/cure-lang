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

append_nil_r : (xs : QList) -> append xs QNil = xs
append_nil_r QNil = Refl
append_nil_r (QCons h t) = cons_cong h (append_nil_r t)

data QOut = QEmpty | Out Nat Q

deq_list : QList -> QOut
deq_list QNil = QEmpty
deq_list (QCons h t) = Out h (MkQ t QNil)

dequeue : Q -> QOut
dequeue (MkQ (QCons h f2) b) = Out h (MkQ f2 b)
dequeue (MkQ QNil b) = deq_list (reverse b)

reassemble : QOut -> QList
reassemble QEmpty = QNil
reassemble (Out x q2) = QCons x (to_list q2)

deq_list_reassembles : (xs : QList) -> reassemble (deq_list xs) = xs
deq_list_reassembles QNil = Refl
deq_list_reassembles (QCons h t) = cons_cong h (append_nil_r t)

dequeue_reassembles : (q : Q) -> reassemble (dequeue q) = to_list q
dequeue_reassembles (MkQ (QCons h f2) b) = Refl
dequeue_reassembles (MkQ QNil b) = deq_list_reassembles (reverse b)
