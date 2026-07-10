; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 178 189)
(cover-floor Cure.Core.Conv 63 71)
(cover-floor Cure.Core.Eval 66 83)
(cover-floor Cure.Core.Inductive 74 84)
(cover-floor Cure.Core.Kernel 358 394)
(cover-floor Cure.Core.Normalise 98 100)
(cover-floor Cure.Core.Quote 28 30)
(cover-floor Cure.Core.Serialize 101 106)
(cover-total 966 1057)
