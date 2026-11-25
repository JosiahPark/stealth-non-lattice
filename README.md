# stealth-non-lattice

J. Park, *Hadamard configurations and sharp cubic-period bounds for stealth in dimensions 10, 11, and 12*
(4 Nov 2026): [`view.pdf`](view.pdf).

## Lean verification roadmap

[![Roadmap: which results of the paper are proved in Lean, and the status of every work item](stealth-lean/docs/roadmap.svg)](stealth-lean/ROADMAP.md)

**[Interactive map](https://claude.ai/artifact/FhkMghsQM4tqQxUNSNoc6P)** (external link, claude.ai): the same roadmap, where selecting an item shows its full
statement, its Lean file, its verified theorems and what it needs.

The picture is redrawn by CI after every verified build of `main`. Click it for the statements of the items
([`stealth-lean/ROADMAP.md`](stealth-lean/ROADMAP.md)). An hourly formalize task works through the roadmap one
item at a time.

[`stealth-lean/`](stealth-lean/) is a Lean 4 + Mathlib project that formalizes results of the paper. Proved
there, with only Lean's standard axioms: Theorem 1.1 (including that the configurations are not translates of
lattices), Theorem 1.2 (the bound `N ≥ 2n`, and for `n ≥ 3` its equality case: `N = 2n` exactly for
translated antipodal Hadamard arrays), Lemma 4.1, Proposition 3.1, Theorem 5.1 and
Corollary 5.2 (with their equality cases), Theorem 5.3, Lemma 6.1, and Theorem 1.3 (in the marked
period model, period shape `Q`). Proposition 7.1 is proved for the pair-coefficient definition of formal
duality (taken from Cohn–Kumar–Reiher–Schürmann as the definition); its equivalence with their analytic
definition is not formalized.

- [What is and is not verified](stealth-lean/README.md)
- [Roadmap: the ordered work list, with the statement of every item](stealth-lean/ROADMAP.md)
- [Verification status: every theorem with its axioms](stealth-lean/verification/STATUS.md) (rewritten by CI;
  [workflow runs](https://github.com/JosiahPark/stealth-non-lattice/actions/workflows/lean.yml))
