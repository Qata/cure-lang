%default total

-- TWO-PHASE COMMIT SAFETY. Participants vote; the coordinator commits iff EVERY vote is yes, else aborts.
-- Proved: VALIDITY (commit iff unanimous, both directions), a REFLECTION between the boolean allYes check and
-- an inductive "some participant voted No" predicate (soundness + completeness), that a dissenter forces
-- abort, and ATOMICITY / uniform agreement (every participant reaches the same decision -- no participant
-- commits while another aborts).

data Bool2 = F | T
data Vote = VYes | VNo
data Votes = VNil | VCons Vote Votes

allYes : Votes -> Bool2
allYes VNil = T
allYes (VCons VYes rest) = allYes rest
allYes (VCons VNo rest) = F

data Decision = Commit | Abort

decideB : Bool2 -> Decision
decideB T = Commit
decideB F = Abort

decide : Votes -> Decision
decide vs = decideB (allYes vs)

data HasNo : Votes -> Type where
  HNHere  : (rest : Votes) -> HasNo (VCons VNo rest)
  HNThere : (v : Vote) -> (rest : Votes) -> HasNo rest -> HasNo (VCons v rest)

hasnoSound : (vs : Votes) -> HasNo vs -> allYes vs = F
hasnoSound (VCons VNo rest) (HNHere rest) = Refl
hasnoSound (VCons v rest) (HNThere v rest h2) = case v of
  VYes => hasnoSound rest h2
  VNo => Refl

hasnoComplete : (vs : Votes) -> allYes vs = F -> HasNo vs
hasnoComplete VNil e = case e of Refl impossible
hasnoComplete (VCons VYes rest) e = HNThere VYes rest (hasnoComplete rest e)
hasnoComplete (VCons VNo rest) e = HNHere rest

commitValid : (vs : Votes) -> allYes vs = T -> decide vs = Commit
commitValid vs e = rewrite e in Refl

validCommitB : (b : Bool2) -> (decideB b = Commit) -> b = T
validCommitB T e = Refl
validCommitB F e = case e of Refl impossible

validCommit : (vs : Votes) -> decide vs = Commit -> allYes vs = T
validCommit vs e = validCommitB (allYes vs) e

abortOnNo : (vs : Votes) -> HasNo vs -> decide vs = Abort
abortOnNo vs h = rewrite hasnoSound vs h in Refl

data DList = DNil | DCons Decision DList

outcomes : Decision -> Votes -> DList
outcomes d VNil = DNil
outcomes d (VCons v rest) = DCons d (outcomes d rest)

data AllSame : (d : Decision) -> (ds : DList) -> Type where
  ASNil  : AllSame d DNil
  ASCons : (d0 : Decision) -> (rest : DList) -> AllSame d0 rest -> AllSame d0 (DCons d0 rest)

allSameReplicate : (d : Decision) -> (vs : Votes) -> AllSame d (outcomes d vs)
allSameReplicate d VNil = ASNil
allSameReplicate d (VCons v rest) = ASCons d (outcomes d rest) (allSameReplicate d rest)

atomicity : (vs : Votes) -> AllSame (decide vs) (outcomes (decide vs) vs)
atomicity vs = allSameReplicate (decide vs) vs
