; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 186 191)
(cover-floor Cure.Core.Conv 76 76)
(cover-floor Cure.Core.Eval 86 86)
(cover-floor Cure.Core.Inductive 83 84)
(cover-floor Cure.Core.Kernel 403 412)
(cover-floor Cure.Core.Normalise 100 100)
(cover-floor Cure.Core.Quote 32 32)
(cover-floor Cure.Core.Serialize 113 117)
(cover-total 1079 1098)
