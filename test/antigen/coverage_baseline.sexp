; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 176 179)
(cover-floor Cure.Core.Conv 63 63)
(cover-floor Cure.Core.Eval 65 65)
(cover-floor Cure.Core.Inductive 74 74)
(cover-floor Cure.Core.Kernel 350 355)
(cover-floor Cure.Core.Normalise 96 97)
(cover-floor Cure.Core.Quote 28 28)
(cover-floor Cure.Core.Serialize 94 94)
(cover-total 946 955)
