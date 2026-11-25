# Stealth Hadamard configurations: Lean verification

[![Roadmap: which results of the paper are proved in Lean, and the status of every work item](docs/roadmap.svg)](ROADMAP.md)

**[Interactive map](https://claude.ai/artifact/FhkMghsQM4tqQxUNSNoc6P)** (external link, claude.ai). The picture is redrawn by CI after every verified build of
`main`. Statements of the items: [ROADMAP.md](ROADMAP.md). Every theorem with its axioms:
[verification/STATUS.md](verification/STATUS.md).

This folder of [stealth-non-lattice](https://github.com/JosiahPark/stealth-non-lattice) holds a Lean 4 + Mathlib
(v4.35.0) project, `StealthAudit`, that formalizes results of

> J. Park, *Hadamard configurations and sharp cubic-period bounds for stealth in dimensions 10, 11, and 12*
> (4 Nov 2026), included at [`paper/stealth_hadamard.pdf`](paper/stealth_hadamard.pdf).

The paper builds periodic point configurations `P_n = C_n + 2ℤⁿ` (`n = 10, 11, 12`) from the 24 sign rows of
an order-12 Hadamard matrix and their antipodes. They are not lattices, and have stealth radius `K = 1` and
stealth center density `Δ_st = 1/24`. It also proves that a motif with marked period `2ℤⁿ` and `K ≥ 1` has
at least `2n` points, with equality only for antipodal Hadamard arrays.

## What is and is not verified

Every theorem under `StealthAudit/` compiles with only Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). [`verification/STATUS.md`](verification/STATUS.md) lists them and is
rewritten by CI after every build on `main`; at the initial commit it has 168 theorems in 18 files.

| Paper result | Status in Lean | Main Lean statements |
|---|---|---|
| Theorem 1.1 (explicit examples) | **Proved**: for `n ∈ {10, 11, 12}`, 24 points distinct modulo `2ℤⁿ` with `K = 1`, `ρ = 24/2ⁿ`, `Δ_st = 1/24`, and `X + 2ℤⁿ` is not a translate of an additive subgroup of `ℝⁿ` (so not of a lattice). The last sentence (comparison with duals of record lattice packings) is checked as arithmetic on the quoted values only. | `theorem_1_1_full` (`NotLattice.lean`), `paley_configuration` (`Theorem11.lean`), `Comparisons.lean` |
| Proposition 3.1 (binary Fourier gap) | **Proved**: for a nonempty binary motif, `4K² = min {4, d⊥}`, `K = √(min {4, d⊥})/2` and `Δ_st = (min {4, d⊥}/4)^{n/2}/N`, with `d⊥` defined as the least weight of a nonzero character sum (no code or dual code is defined). | `gapSq_eq_min_four_dualDist`, `centerDensity_eq_min_four_dualDist` (`DualDistance.lean`), `gapAtLeast_iff_hasStrength`, `gapSq_le_four` (`BinaryMotif.lean`) |
| Paley certificate of §3 | **Proved** by kernel evaluation: `Sᵀ = −S`, `S Sᵀ = 11 I`, `H Hᵀ = 12 I`, entries `±1`. | `isHadamard_paley12` (`Paley12.lean`) |
| Theorem 1.2 (sharp cardinality and equality) | **Proved.** Bound, for every `n`: `K ≥ 1` gives `N ≥ 2n`. Equality, for `n ≥ 3`: a motif with `N = 2n` points has `K ≥ 1` exactly when it is, up to a common translation, a relabelling and shifts by `2ℤⁿ`, the antipodal array of a Hadamard matrix of order `n`. | `two_mul_le_card_of_one_le_stealthRadius` (`StealthRadius.lean`), `theorem_1_2` (`Theorem12.lean`), `equality_hadamard` (`EqualityHadamard.lean`), `stealthRadius_antipodalMotif` (`AntipodalArray.lean`) |
| Lemma 4.1 (rank obstruction) | **Proved**: `K > 1` gives `N ≥ 1 + n + n(n−1)/2`. | `rank_obstruction_of_one_lt_stealthRadius` (`StealthRadius.lean`) |
| Theorem 5.1 (bounded complexity) | **Proved**: `n ≥ 5`, `N < D_n` give `Δ_st ≤ 1/(2n)`, with equality exactly for translated antipodal Hadamard arrays of order `n` (up to relabelling and shifts by `2ℤⁿ`). | `centerDensity_le_of_card_lt`, `centerDensity_eq_iff_of_card_lt` (`BoundedComplexity.lean`), `centerDensity_eq_iff_antipodalHadamard` (`BoundedComplexityEquality.lean`) |
| Corollary 5.2 (dimension 12) | **Proved**: `N < 79` gives `Δ_st ≤ 1/24`, with equality exactly for translated 24-point antipodal Hadamard configurations of order 12. | `centerDensity_le_dim_twelve`, `centerDensity_eq_iff_antipodalHadamard_dim_twelve` |
| Theorem 5.3 (binary motifs, `n = 10, 11, 12`) | **Proved**: `Δ_st ≤ 1/24`, with equality exactly for strength three with 24 points; the value is attained. | `centerDensity_le_of_isBinary`, `centerDensity_eq_iff_of_isBinary` (`BinaryOptimality.lean`) |
| Lemma 6.1 (strict reciprocal-Gram maximum) | **Proved** for `n ≥ 4`: every test vector has `vᵀv = 4`, and there is `δ > 0` such that every symmetric positive definite `Q` with `det Q = 1` and `0 < ‖Q − 1‖² < δ` (`‖·‖²` the sum of squared entries) has a test vector with `vᵀQv < 4`. | `lemma_6_1` (`ReciprocalGram.lean`), `exists_testVector_quadForm_neg` (`TraceFreeSign.lean`), `exists_trace_free_constant` (`TraceFreeConstant.lean`), `trace_sub_one_le_two_frobSq` (`DetOneTrace.lean`) |
| Theorem 1.3 (local maximality) | **Not proved** (items F4, F5). Proved toward it: Lemma 6.1, and for strength three with `N ≡ 8 (mod 16)` every test vector has nonzero amplitude. | `lemma_6_1`, `amp_testVector_ne_zero` (`TestAmplitudes.lean`) |
| Proposition 7.1 (no formal dual) | **Not proved**: the library has no definition of formal duality. Its arithmetic is checked: `a_X(2u) = N`, and `2ⁿ/24` is not an integer. | `FormalDualityArithmetic.lean` |

Three things to keep in mind when reading the table:

- **The stealth radius is defined by formula (2) of the paper.** `K(P)` here is half the least norm of a
  nonzero `u ∈ ℤⁿ` with `a_X(u) = ∑_x e^{πi u·x} ≠ 0`. The diffraction measure of a periodic set, and the
  derivation of (2) from it, are not formalized.
- **A motif is an indexed family** `X : ι → Fin n → ℝ`; repeated points are allowed unless
  `DistinctModPeriod X` is assumed. "Strength three" is the Fourier form (character sums of weights 1, 2, 3
  vanish).
- The Lean statements were written and compared with the paper in one session and have not been reviewed
  independently.

## Roadmap

[`ROADMAP.md`](ROADMAP.md) is the ordered work list: diffraction normalization (A), binary motifs and
orthogonal arrays (B), the Hadamard construction (C), the sharp cardinality theorem (D), optimality
consequences (E), local optimality (F), formal duality and numerical comparisons (G). The picture at the top shows
which items are done and which is next; an hourly formalize task takes the first open item, proves it, and ticks it
only when `lake build` and `axiom_audit.py` pass.

[`docs/roadmap.svg`](docs/roadmap.svg), shown above, is the static picture of the roadmap.
[`docs/roadmap.html`](docs/roadmap.html) is the interactive version of the same map. Its external copy is the
[claude.ai artifact](https://claude.ai/artifact/FhkMghsQM4tqQxUNSNoc6P), republished by the hourly formalize task whenever the roadmap changes
(`tools/artifact_page.py` writes the copy; the artifact shows the snapshot it was published with). It follows the
style of
[steklov-lean](https://github.com/JosiahPark/steklov-lean) and
[balian-low-asymptotics-hermitian-optimality](https://github.com/JosiahPark/balian-low-asymptotics-hermitian-optimality):
sections as bands, one box per item, the paper's results as a spine on the right. CI refreshes the picture and
the page's snapshot after every verification run; opened in a browser, the page also reads `ROADMAP.md` and the
status live from `main`.

## Layout

- `paper/stealth_hadamard.pdf`: the paper.
- `StealthAudit.lean`, `StealthAudit/Basic.lean`: root file and shared definitions (phases, amplitudes,
  `GapAtLeast`, `gapSq`, `stealthRadius`, `density`, `centerDensity`, binary motifs, character sums,
  `IsHadamard`, `antipodalMotif`).
- `StealthAudit/<Name>.lean`: one file per roadmap item. Every file under `StealthAudit/` is built
  automatically, and each starts with a docstring saying what it proves and what it does not.
- `axiom_audit.py`: after `lake build`, runs `#print axioms` on every theorem and fails on `sorry`,
  non-standard axioms, escape hatches (`native_decide`, `axiom`, `unsafe`, heartbeat options, …), or a proof
  that is just one of its own hypotheses. It writes `verification/STATUS.md` and `verification/STATUS.json`.
- `tools/build_roadmap.py`: redraws `docs/roadmap.svg` and refreshes the snapshot inside `docs/roadmap.html`, from
  `ROADMAP.md`, the status, and the layout data in `docs/roadmap_config.json`.
- `tools/artifact_page.py`: writes the copy of `docs/roadmap.html` that is published as the external map.
- `../.github/workflows/lean.yml` (at the repository root): on every push that touches this folder it builds and
  audits the project; on `main` it then commits the status, the roadmap picture and the roadmap page when they
  change.

## Running locally

With elan installed and network access to the Mathlib cache, from this folder:

```
lake exe cache get && lake build && python3 axiom_audit.py
```

The setup follows [steklov-lean](https://github.com/JosiahPark/steklov-lean) (CI, axiom audit, status files),
[balian-low-asymptotics-hermitian-optimality](https://github.com/JosiahPark/balian-low-asymptotics-hermitian-optimality)
(roadmap page) and [entropy-quotients-lean](https://github.com/JosiahPark/entropy-quotients-lean). The paper is
an AI-assisted draft, as its §8 says; the Lean library, roadmap and scaffold were written with Claude Code on
2026-11-24.
