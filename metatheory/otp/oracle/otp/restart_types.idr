%default total

data Bool' = False | True
data ExitReason = Normal | Abnormal
data RestartType = Permanent | Transient | Temporary

should_restart : RestartType -> ExitReason -> Bool'
should_restart Permanent r = True
should_restart Transient Normal = False
should_restart Transient Abnormal = True
should_restart Temporary r = False

-- permanent always restarts, whatever the exit reason.
permanent_always : (r : ExitReason) -> should_restart Permanent r = True
permanent_always r = Refl

-- temporary never restarts.
temporary_never : (r : ExitReason) -> should_restart Temporary r = False
temporary_never r = Refl

-- transient discriminates on the exit reason.
transient_on_normal : should_restart Transient Normal = False
transient_on_normal = Refl

transient_on_abnormal : should_restart Transient Abnormal = True
transient_on_abnormal = Refl
