%default total

data Phase = PInit | PRunning | PTerminated

data Callback : Phase -> Phase -> Type where
  CbInit      : Callback PInit PRunning
  CbCall      : Callback PRunning PRunning
  CbCast      : Callback PRunning PRunning
  CbInfo      : Callback PRunning PRunning
  CbStop      : Callback PRunning PTerminated
  CbTerminate : Callback PTerminated PTerminated

data Lifecycle : Phase -> Phase -> Type where
  LEnd : Lifecycle p p
  LStep : Callback from mid -> Lifecycle mid to -> Lifecycle from to

init_only : Callback PInit to -> to = PRunning
init_only CbInit = Refl

nothing_reinits : Callback from PInit -> Void
nothing_reinits CbInit impossible
nothing_reinits CbCall impossible
nothing_reinits CbCast impossible
nothing_reinits CbInfo impossible
nothing_reinits CbStop impossible
nothing_reinits CbTerminate impossible

terminated_absorbing : Callback PTerminated to -> to = PTerminated
terminated_absorbing CbTerminate = Refl

no_resurrection : Lifecycle PTerminated to -> to = PTerminated
no_resurrection LEnd = Refl
no_resurrection (LStep CbTerminate lc2) = no_resurrection lc2
