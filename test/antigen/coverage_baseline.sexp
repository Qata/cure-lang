; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 188 193)
(cover-floor Cure.Core.Conv 79 79)
(cover-floor Cure.Core.Eval 89 91)
(cover-floor Cure.Core.Inductive 87 99)
(cover-floor Cure.Core.Kernel 403 438)
(cover-floor Cure.Core.Normalise 104 104)
(cover-floor Cure.Core.Quote 35 35)
(cover-floor Cure.Core.Serialize 115 127)
(cover-total 1100 1166)
