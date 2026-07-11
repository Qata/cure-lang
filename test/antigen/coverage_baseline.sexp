; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 186 191)
(cover-floor Cure.Core.Conv 79 79)
(cover-floor Cure.Core.Eval 89 89)
(cover-floor Cure.Core.Inductive 86 98)
(cover-floor Cure.Core.Kernel 404 443)
(cover-floor Cure.Core.Normalise 103 103)
(cover-floor Cure.Core.Quote 35 35)
(cover-floor Cure.Core.Serialize 113 123)
(cover-total 1095 1161)
