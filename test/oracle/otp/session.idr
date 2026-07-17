%default total

data Tag = TA | TB | TC
data SType = SEnd | SSend Tag SType | SRecv Tag SType | SSelect SType SType | SOffer SType SType

dual : SType -> SType
dual SEnd = SEnd
dual (SSend t k) = SRecv t (dual k)
dual (SRecv t k) = SSend t (dual k)
dual (SSelect a b) = SOffer (dual a) (dual b)
dual (SOffer a b) = SSelect (dual a) (dual b)

dual_involution : (s : SType) -> dual (dual s) = s
dual_involution SEnd = Refl
dual_involution (SSend t k) = rewrite dual_involution k in Refl
dual_involution (SRecv t k) = rewrite dual_involution k in Refl
dual_involution (SSelect a b) = rewrite dual_involution a in rewrite dual_involution b in Refl
dual_involution (SOffer a b) = rewrite dual_involution a in rewrite dual_involution b in Refl

data Compat : SType -> SType -> Type where
  CEnd : Compat SEnd SEnd
  CSR : (t : Tag) -> Compat l r -> Compat (SSend t l) (SRecv t r)
  CRS : (t : Tag) -> Compat l r -> Compat (SRecv t l) (SSend t r)
  CSel : Compat la ra -> Compat lb rb -> Compat (SSelect la lb) (SOffer ra rb)
  COff : Compat la ra -> Compat lb rb -> Compat (SOffer la lb) (SSelect ra rb)

compat_dual : Compat l r -> l = dual r
compat_dual CEnd = Refl
compat_dual (CSR t c2) = cong (SSend t) (compat_dual c2)
compat_dual (CRS t c2) = cong (SRecv t) (compat_dual c2)
compat_dual (CSel ca cb) = cong2 SSelect (compat_dual ca) (compat_dual cb)
compat_dual (COff ca cb) = cong2 SOffer (compat_dual ca) (compat_dual cb)

dual_compat : (s : SType) -> Compat s (dual s)
dual_compat SEnd = CEnd
dual_compat (SSend t k) = CSR t (dual_compat k)
dual_compat (SRecv t k) = CRS t (dual_compat k)
dual_compat (SSelect a b) = CSel (dual_compat a) (dual_compat b)
dual_compat (SOffer a b) = COff (dual_compat a) (dual_compat b)

compat_sym : Compat l r -> Compat r l
compat_sym CEnd = CEnd
compat_sym (CSR t c2) = CRS t (compat_sym c2)
compat_sym (CRS t c2) = CSR t (compat_sym c2)
compat_sym (CSel ca cb) = COff (compat_sym ca) (compat_sym cb)
compat_sym (COff ca cb) = CSel (compat_sym ca) (compat_sym cb)

data SStep : SType -> SType -> SType -> SType -> Type where
  StepSR : SStep (SSend t lk) (SRecv t rk) lk rk
  StepRS : SStep (SRecv t lk) (SSend t rk) lk rk
  SelL : SStep (SSelect la lb) (SOffer ra rb) la ra
  SelR : SStep (SSelect la lb) (SOffer ra rb) lb rb
  OffL : SStep (SOffer la lb) (SSelect ra rb) la ra
  OffR : SStep (SOffer la lb) (SSelect ra rb) lb rb

session_preservation : Compat l r -> SStep l r l2 r2 -> Compat l2 r2
session_preservation (CSR t c2) StepSR = c2
session_preservation (CRS t c2) StepRS = c2
session_preservation (CSel ca cb) SelL = ca
session_preservation (CSel ca cb) SelR = cb
session_preservation (COff ca cb) OffL = ca
session_preservation (COff ca cb) OffR = cb

data SRun : SType -> SType -> SType -> SType -> Type where
  SRDone : SRun l r l r
  SRStep : SStep l r lm rm -> SRun lm rm l2 r2 -> SRun l r l2 r2

session_run_safe : Compat l r -> SRun l r l2 r2 -> Compat l2 r2
session_run_safe c SRDone = c
session_run_safe c (SRStep st rest) = session_run_safe (session_preservation c st) rest

data Progress : SType -> SType -> Type where
  PDone : Progress SEnd SEnd
  PStepSR : Progress (SSend t lk) (SRecv t rk)
  PStepRS : Progress (SRecv t lk) (SSend t rk)
  PStepSel : Progress (SSelect la lb) (SOffer ra rb)
  PStepOff : Progress (SOffer la lb) (SSelect ra rb)

session_progress : Compat l r -> Progress l r
session_progress CEnd = PDone
session_progress (CSR t c2) = PStepSR
session_progress (CRS t c2) = PStepRS
session_progress (CSel ca cb) = PStepSel
session_progress (COff ca cb) = PStepOff

run_sr : (t : Tag) -> SRun lk rk SEnd SEnd -> SRun (SSend t lk) (SRecv t rk) SEnd SEnd
run_sr t x = SRStep StepSR x

run_rs : (t : Tag) -> SRun lk rk SEnd SEnd -> SRun (SRecv t lk) (SSend t rk) SEnd SEnd
run_rs t x = SRStep StepRS x

run_sel : SRun la ra SEnd SEnd -> SRun (SSelect la lb) (SOffer ra rb) SEnd SEnd
run_sel x = SRStep SelL x

run_off : SRun la ra SEnd SEnd -> SRun (SOffer la lb) (SSelect ra rb) SEnd SEnd
run_off x = SRStep OffL x

compat_terminates : Compat l r -> SRun l r SEnd SEnd
compat_terminates CEnd = SRDone
compat_terminates (CSR t c2) = run_sr t (compat_terminates c2)
compat_terminates (CRS t c2) = run_rs t (compat_terminates c2)
compat_terminates (CSel ca cb) = run_sel (compat_terminates ca)
compat_terminates (COff ca cb) = run_off (compat_terminates ca)

compat_unique : (r : SType) -> (r2 : SType) -> Compat l r -> Compat l r2 -> r = r2
compat_unique r r2 c1 c2 = trans (sym (dual_involution r)) (trans (cong dual (trans (sym (compat_dual c1)) (compat_dual c2))) (dual_involution r2))

sstep_sym : SStep l r l2 r2 -> SStep r l r2 l2
sstep_sym StepSR = StepRS
sstep_sym StepRS = StepSR
sstep_sym SelL = OffL
sstep_sym SelR = OffR
sstep_sym OffL = SelL
sstep_sym OffR = SelR

srun_sym : SRun l r l2 r2 -> SRun r l r2 l2
srun_sym SRDone = SRDone
srun_sym (SRStep st rest) = SRStep (sstep_sym st) (srun_sym rest)
