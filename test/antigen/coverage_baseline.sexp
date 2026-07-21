; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 191 197)
(cover-floor Cure.Core.Conv 79 83)
(cover-floor Cure.Core.Eval 91 96)
(cover-floor Cure.Core.Inductive 99 118)
(cover-floor Cure.Core.Kernel 438 486)
(cover-floor Cure.Core.Normalise 104 104)
(cover-floor Cure.Core.Quote 35 36)
(cover-floor Cure.Core.Serialize 115 127)
(cover-total 1152 1246)
