import Mathlib

/-!
# StealthAudit

Lean 4 + Mathlib companion to J. Park, "Hadamard configurations and sharp cubic-period bounds for
stealth in dimensions 10, 11, and 12" (4 Nov 2026; `paper/stealth_hadamard.pdf` in this
repository).

Every file under `StealthAudit/` is built automatically (lakefile globs `StealthAudit.+`), so this
root file imports nothing beyond Mathlib. Shared definitions are in `StealthAudit/Basic.lean`. The
work list is `ROADMAP.md`; CI writes `verification/STATUS.md` and redraws `docs/roadmap.html`.

`ROADMAP.md` and `README.md` say which results of the paper are proved here and which are not.
-/
