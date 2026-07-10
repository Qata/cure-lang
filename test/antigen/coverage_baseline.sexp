; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 178 189)
(cover-floor Cure.Core.Conv 63 75)
(cover-floor Cure.Core.Eval 67 85)
(cover-floor Cure.Core.Inductive 78 98)
(cover-floor Cure.Core.Kernel 358 399)
(cover-floor Cure.Core.Normalise 98 100)
(cover-floor Cure.Core.Quote 28 32)
(cover-floor Cure.Core.Serialize 101 110)
(cover-total 971 1088)
