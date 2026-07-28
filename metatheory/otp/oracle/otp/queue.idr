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

append_cong : (c : QList) -> a = b -> append a c = append b c
append_cong c Refl = Refl

enqueue_respects : (x : Nat) -> (q1 : Q) -> (q2 : Q) -> to_list q1 = to_list q2 -> to_list (enqueue x q1) = to_list (enqueue x q2)
enqueue_respects x q1 q2 e = trans (enqueue_appends x q1) (trans (append_cong (QCons x QNil) e) (sym (enqueue_appends x q2)))

dequeue_respects : (q1 : Q) -> (q2 : Q) -> to_list q1 = to_list q2 -> reassemble (dequeue q1) = reassemble (dequeue q2)
dequeue_respects q1 q2 e = trans (dequeue_reassembles q1) (trans e (sym (dequeue_reassembles q2)))

data QOpt = QNone | QSome Nat

peek_list : QList -> QOpt
peek_list QNil = QNone
peek_list (QCons h t) = QSome h

peek : Q -> QOpt
peek (MkQ (QCons h f2) b) = QSome h
peek (MkQ QNil b) = peek_list (reverse b)

head_of : QOut -> QOpt
head_of QEmpty = QNone
head_of (Out x q2) = QSome x

peek_list_deq : (xs : QList) -> peek_list xs = head_of (deq_list xs)
peek_list_deq QNil = Refl
peek_list_deq (QCons h t) = Refl

peek_dequeue : (q : Q) -> peek q = head_of (dequeue q)
peek_dequeue (MkQ (QCons h f2) b) = Refl
peek_dequeue (MkQ QNil b) = peek_list_deq (reverse b)

data B = F | T

qnull : QList -> B
qnull QNil = T
qnull (QCons h t) = F

andb : B -> B -> B
andb F b = F
andb T b = b

is_empty : Q -> B
is_empty (MkQ f b) = andb (qnull f) (qnull b)

qnull_append_cons : (xs : QList) -> (h : Nat) -> qnull (append xs (QCons h QNil)) = F
qnull_append_cons QNil h = Refl
qnull_append_cons (QCons a t) h = Refl

qnull_reverse : (xs : QList) -> qnull (reverse xs) = qnull xs
qnull_reverse QNil = Refl
qnull_reverse (QCons h t) = qnull_append_cons (reverse t) h

is_empty_reflects : (q : Q) -> is_empty q = qnull (to_list q)
is_empty_reflects (MkQ (QCons h f2) b) = Refl
is_empty_reflects (MkQ QNil b) = sym (qnull_reverse b)
