%default total

-- MAILBOX EXHAUSTIVENESS => IN-PROTOCOL PROGRESS (algebra item 3). A server's receive loop follows a session
-- (a sequence of expected receives); its MAILBOX is the set of message tags it actually handles. The safety
-- property is: if the mailbox COVERS the session -- handles every tag the protocol will ever deliver -- the loop
-- runs to completion, discharging every receive obligation, and NEVER gets stuck on an unhandled message.
-- `exhaustiveProgress` proves it: coverage implies the run takes exactly `len s` steps. `stepsLeLen` proves the
-- dual bound (a run never overruns its obligations), so coverage is exactly the condition for MAXIMAL progress;
-- `stuckExample` witnesses that a missing handler stalls the loop at the unhandled tag. The per-message handled
-- decision is routed through `stepsPick` so it is a visible argument (the Cure side needs this to refine the
-- frozen recursive call; Idris reduces past it freely).

data Bool2 = F | T
data Natt = Z | S Natt

andb : Bool2 -> Bool2 -> Bool2
andb T b = b
andb F b = F

andbTrueL : (a : Bool2) -> (b : Bool2) -> andb a b = T -> a = T
andbTrueL T b e = Refl
andbTrueL F b e = case e of Refl impossible

andbTrueR : (a : Bool2) -> (b : Bool2) -> andb a b = T -> b = T
andbTrueR T b e = e
andbTrueR F b e = case e of Refl impossible

le : Natt -> Natt -> Bool2
le Z _ = T
le (S k) Z = F
le (S k) (S j) = le k j

-- Message tags and their decidable equality.
data Tag = TA | TB | TC

tagEq : Tag -> Tag -> Bool2
tagEq TA TA = T
tagEq TA TB = F
tagEq TA TC = F
tagEq TB TA = F
tagEq TB TB = T
tagEq TB TC = F
tagEq TC TA = F
tagEq TC TB = F
tagEq TC TC = T

-- The MAILBOX: the set of tags the server's receive loop handles.
data TagSet = TNil | TCons Tag TagSet

member : TagSet -> Tag -> Bool2
member TNil t = F
member (TCons h rest) t = case tagEq h t of
  T => T
  F => member rest t

-- The PROTOCOL: a sequence of expected receives (the session type).
data Session = SEnd | SRecv Tag Session

len : Session -> Natt
len SEnd = Z
len (SRecv t k) = S (len k)

-- The mailbox COVERS the session: every expected tag is handled.
covers : TagSet -> Session -> Bool2
covers set SEnd = T
covers set (SRecv t k) = andb (member set t) (covers set k)

-- One loop step's decision as a VISIBLE argument: handled => make progress; unhandled => stuck (no progress).
stepsPick : Bool2 -> Natt -> Natt
stepsPick T rest = S rest
stepsPick F rest = Z

-- Run the loop, counting handled receives until an unhandled tag (stuck) or SEnd (done).
steps : TagSet -> Session -> Natt
steps set SEnd = Z
steps set (SRecv t k) = stepsPick (member set t) (steps set k)

-- Progress never overruns the obligations: at most `len s` receives happen.
stepsPickLe : (handled : Bool2) -> (rest : Natt) -> (bound : Natt) -> le rest bound = T ->
              le (stepsPick handled rest) (S bound) = T
stepsPickLe T rest bound hle = hle
stepsPickLe F rest bound hle = Refl

stepsLeLen : (set : TagSet) -> (s : Session) -> le (steps set s) (len s) = T
stepsLeLen set SEnd = Refl
stepsLeLen set (SRecv t k) = stepsPickLe (member set t) (steps set k) (len k) (stepsLeLen set k)

-- MAIN: EXHAUSTIVENESS => PROGRESS. If the mailbox covers the session, the loop takes exactly `len s` steps --
-- every receive obligation discharged, never stuck.
exhaustiveProgress : (set : TagSet) -> (s : Session) -> covers set s = T -> steps set s = len s
exhaustiveProgress set SEnd hcov = Refl
exhaustiveProgress set (SRecv t k) hcov =
  rewrite andbTrueL (member set t) (covers set k) hcov in
  rewrite exhaustiveProgress set k (andbTrueR (member set t) (covers set k) hcov) in
  Refl

-- Necessity, concretely: mailbox {TA} does NOT cover a session expecting TB, so the loop stalls at 0 steps
-- while the protocol still had one obligation (len = 1). Coverage is thus exactly the no-stuck condition.
stuckExample : steps (TCons TA TNil) (SRecv TB SEnd) = Z
stuckExample = Refl
