%default total

-- SIBLING REFINEMENT under a plain match: matching a variable scrutinee refines not only the goal but any
-- sibling hypothesis whose type mentions it (including function-typed siblings). This is the standard
-- behaviour of dependent pattern matching in Idris/Agda/Coq; the Cure side needed the elaborator's
-- abstract_term to shift the abstraction target under binders. boolMt (boolean modus tollens with a
-- function-typed sibling g) and useEq (a plain equation sibling) both check with no convoy.

data Bool2 = F | T

notb : Bool2 -> Bool2
notb T = F
notb F = T

boolMt : (b : Bool2) -> (c : Bool2) -> (b = T -> c = T) -> (c = F) -> b = F
boolMt T c g hc = case trans (sym (g Refl)) hc of Refl impossible
boolMt F c g hc = Refl

useEq : (b : Bool2) -> (b = T) -> notb b = F
useEq T p = Refl
useEq F p = case p of Refl impossible
