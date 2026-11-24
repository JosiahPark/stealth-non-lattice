# stealth-non-lattice

J. Park, *Hadamard configurations and sharp cubic-period bounds for stealth in dimensions 10, 11, and 12*
(4 Nov 2026): [`view.pdf`](view.pdf).

## Lean verification

**[Interactive roadmap map](https://josiahpark.github.io/stealth-non-lattice/stealth-lean/docs/roadmap.html)**:
every item of the formalization plan in its section, with the paper's results it feeds and their Lean status
(page source: [`stealth-lean/docs/roadmap.html`](https://github.com/JosiahPark/stealth-non-lattice/blob/main/stealth-lean/docs/roadmap.html)).

[`stealth-lean/`](https://github.com/JosiahPark/stealth-non-lattice/tree/main/stealth-lean) is a Lean 4 + Mathlib
project that formalizes results of the paper. Proved there, with only Lean's standard axioms: Theorem 1.1
(including that the configurations are not translates of lattices), the bound `N ≥ 2n` of Theorem 1.2 and its
converse, Lemma 4.1, Proposition 3.1 in gap form, the inequalities of Theorem 5.1 and Corollary 5.2, and
Theorem 5.3. Not proved: the equality case of Theorem 1.2, Theorem 1.3, Lemma 6.1 and Proposition 7.1.

- [What is and is not verified](https://github.com/JosiahPark/stealth-non-lattice/blob/main/stealth-lean/README.md)
- [Roadmap](https://github.com/JosiahPark/stealth-non-lattice/blob/main/stealth-lean/ROADMAP.md)
- [Verification status](https://github.com/JosiahPark/stealth-non-lattice/blob/main/stealth-lean/verification/STATUS.md)
  (every theorem with its axioms; rewritten by CI)
