# Roadmap: Lean companion to "Hadamard configurations and sharp cubic-period bounds for stealth in dimensions 10, 11, and 12"

Paper: J. Park, 4 Nov 2026, [`paper/stealth_hadamard.pdf`](paper/stealth_hadamard.pdf).
It constructs periodic point configurations `P_n = C_n + 2ℤⁿ` (`n = 10, 11, 12`) from the 24 sign rows
of an order-12 Hadamard matrix and their antipodes, with stealth radius `K = 1` and stealth center
density `Δ_st = 1/24` (Theorem 1.1); proves that a motif with marked period `2ℤⁿ` and `K ≥ 1` has at
least `2n` points, with equality only for antipodal Hadamard arrays (Theorem 1.2); and proves local
maximality under perturbations of the motif and of the marked period (Theorem 1.3).

An hourly formalize task takes the FIRST unchecked item (`- [ ]`), writes it in the file the item names, and
ticks it (`- [x]`) in the same commit, only after `lake build` and `axiom_audit.py` pass with the pinned toolchain;
CI then confirms on main. `- [-]` marks an item that is skipped or split.
[docs/roadmap.svg](docs/roadmap.svg) is a picture of this file and [docs/roadmap.html](docs/roadmap.html) an
interactive map of it; CI redraws both after every verification run (`tools/build_roadmap.py`, with the layout
data of `docs/roadmap_config.json`), and the page also reads this file live from main when opened in a browser.
Its external copy is the [claude.ai artifact](https://claude.ai/artifact/FhkMghsQM4tqQxUNSNoc6P), which the formalize task republishes after each change.
[verification/STATUS.md](verification/STATUS.md) lists every theorem with its axioms.

Layout: `StealthAudit.lean` (root, imports Mathlib only), `StealthAudit/Basic.lean` (shared definitions:
`dot`, `phase`, `amp`, `sqNorm`, `Survives`, `GapAtLeast`, `gapSq`, `stealthRadius`, `density`,
`centerDensity`, `DistinctModPeriod`, `ind`, `oddSupp`, `IsBinary`, `charSum`, `HasStrength`,
`IsHadamard`, `antipodalMotif`), then one file per item, `StealthAudit/<Name>.lean`. Every file under
`StealthAudit/` is built automatically. CI (`.github/workflows/lean.yml` at the repository root; this
project is the folder `stealth-lean/` of the repository) runs `lake build` with
Lean 4.35.0 + Mathlib v4.35.0, then `axiom_audit.py`.

Conventions of the library. The marked period is `2ℤⁿ`. A motif is an indexed family
`X : ι → Fin n → ℝ`, `N = Fintype.card ι`; repeated points are allowed, and "distinct representatives"
is the separate hypothesis `DistinctModPeriod X`. Formula (2) of the paper is the DEFINITION of the
stealth radius here: `gapSq X = 4 K(P)²` is the least `‖u‖²` over nonzero `u ∈ ℤⁿ` with
`a_X(u) = ∑_x e^{πi u·x} ≠ 0`, and `GapAtLeast X s` says `4 K(P)² ≥ s`. So `K ≥ 1` is `GapAtLeast X 4`
and `K > 1` is `GapAtLeast X 5`. The diffraction measure of a periodic set is not defined in Lean.

Rules: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern` or
heartbeat options. Each file starts with a `/-! ... -/` docstring saying what it proves and what it does
NOT prove. A statement of the paper that is not proved in Lean may enter only as an explicit, named
hypothesis. Nothing here may be described as a proof of a theorem of the paper unless it has no such
hypothesis and this file says which clauses it covers.

The items ticked on 2026-11-24 were written in one session and compiled there with the pinned toolchain
(`lake build`, then `axiom_audit.py`: 168 of 168 theorems with standard axioms only), before the first
CI run of this repository.

## A. Diffraction normalization

§2 of the paper, for the cubic period `2ℤⁿ`: amplitudes, the stealth radius, the density and the stealth
center density (1).

- [x] A1. Phase algebra: `u ↦ e^{πi u·x}` is a unitary character of `ℤⁿ`; `a_X(0) = N`; the inner product
  of two evaluation columns is `∑_x conj (e^{πi u·x}) e^{πi v·x} = a_X(v − u)`; a common translation of the
  motif multiplies every amplitude by a unit, and shifting points by vectors of `2ℤⁿ` changes nothing.
  File `StealthAudit/PhaseAlgebra.lean`.
  - Done 2026-11-24: `phase_zero`, `phase_add`, `phase_neg`, `norm_phase`, `amp_zero`, `sum_conj_phase_mul_phase`, `amp_translate`, `gapAtLeast_translate`, `survives_translate`, `phase_add_period`, `amp_add_period`
- [x] A2. The stealth radius is well defined: for a nonempty motif in dimension `n ≥ 1` some nonzero
  frequency has nonzero amplitude, so `gapSq X` is a minimum; `GapAtLeast X s ↔ s ≤ gapSq X`;
  `K ≥ 1 ↔ GapAtLeast X 4` and `K > 1 ↔ GapAtLeast X 5`; `Δ_st = Kⁿ / N` for the period `2ℤⁿ`;
  translation invariance of `K` and `Δ_st`. File `StealthAudit/StealthRadius.lean`.
  - Done 2026-11-24: `exists_survives`, `exists_survives_sqNorm_eq_gapSq`, `gapSq_le_of_survives`, `gapAtLeast_iff_le_gapSq`, `gapSq_pos`, `four_mul_stealthRadius_sq`, `one_le_stealthRadius_iff`, `one_lt_stealthRadius_iff`, `centerDensity_eq`, `gapSq_translate`, `stealthRadius_translate`, `centerDensity_translate`. The file also restates D3 with `stealthRadius`: `two_mul_le_card_of_one_le_stealthRadius`, `rank_obstruction_of_one_lt_stealthRadius`.
- [ ] A3. General marked period, formula (3). For a real symmetric positive definite `Q` (`Matrix (Fin n)
  (Fin n) ℝ`) define `quadForm Q u = ∑ i j, u i * Q i j * u j` for `u : Fin n → ℤ` and
  `gapQ X Q = ⨅ {quadForm Q u : u ≠ 0, amp X u ≠ 0}` (as an infimum in `ℝ` over the set of values; show it
  is attained when `Q` is positive definite, `n ≥ 1` and `ι` is nonempty, using `exists_survives` and that
  `{u : quadForm Q u ≤ c}` is finite). Define `centerDensityQ X Q = (gapQ X Q / 4) ^ ((n : ℝ) / 2) / N` (the
  right side of (3) with `Q = Q_B`). Prove `gapQ X 1 = gapSq X` and `centerDensityQ X 1 = centerDensity X`.
  The derivation of (3) from a period matrix `B` (`Q_B = |det B|^{2/n} B⁻¹ B⁻ᵀ`, density
  `N / (2ⁿ |det B|)`) is a statement about the linear image `B (X + 2ℤⁿ)` and its dual lattice; state it as
  a docstring remark, not as a theorem, unless the dual-lattice side is also defined.
  File `StealthAudit/PeriodShape.lean`.

## B. Binary motifs and orthogonal arrays

§3 up to Proposition 3.1. A binary motif has all coordinates in `{0, 1}`; `charSum X S` is the binary
character sum `∑_x ∏_{i ∈ S} (1 − 2xᵢ)`; `HasStrength X t` says the character sums of weights `1, …, t`
vanish (the Fourier form of "orthogonal array of strength `t`").

- [x] B1. Exact binary Fourier gap, gap form of Proposition 3.1: for a binary motif `a_X(u)` is the
  character sum of the odd support of `u`; the number of odd coordinates of `u` is at most `‖u‖²`, and a
  nonzero `u` with all coordinates even has `‖u‖² ≥ 4`; hence for `t ≤ 3`, `4K² ≥ t + 1` exactly when the
  motif has strength `t`; `a_X(2eᵢ) = N`, so `4K² ≤ 4`; `K = 1` exactly for strength three, and then
  `Δ_st = 1/N`. File `StealthAudit/BinaryMotif.lean`.
  - Done 2026-11-24: `amp_of_isBinary`, `phase_of_binary`, `card_oddSupp_le_sqNorm`, `four_le_sqNorm_of_oddSupp_eq_empty`, `gapAtLeast_iff_hasStrength`, `amp_two_mul_single`, `not_gapAtLeast_five`, `gapSq_le_four`, `le_gapSq_iff_hasStrength`, `gapSq_eq_four_iff_hasStrength`, `stealthRadius_eq_one_iff`, `centerDensity_of_hasStrength_three`. The two displayed formulas of Proposition 3.1 with `min {4, d⊥}` are not stated as single equations (item B2).
- [ ] B2. Proposition 3.1 as displayed. Define the dual distance
  `dualDist X : ℕ∞ = ⨅ S ∈ {S : S.Nonempty ∧ charSum X S ≠ 0}, (S.card : ℕ∞)` (so `⊤` if no character sum
  survives) and prove, for a nonempty binary motif in dimension `n ≥ 1`:
  `(gapSq X : ℕ∞) = min 4 (dualDist X)` (from `le_gapSq_iff_hasStrength` and `gapSq_le_four` of B1, with
  `HasStrength X t ↔ (t : ℕ∞) < dualDist X`), hence `stealthRadius X = √(min 4 d⊥) / 2` and
  `centerDensity X ^ 2 = (min 4 d⊥ / 4) ^ n / N ^ 2` (the square of the second formula; the paper's form
  with exponent `n/2` as a `Real.rpow` is optional). File `StealthAudit/DualDistance.lean`.
- [x] B3. Marginals: for a binary motif and a set `T` of coordinates,
  `2^{|T|} · #{x ∈ X : x = 0 on T} = ∑_{S ⊆ T} charSum X S`; hence strength `t ≤ n` forces `2^t ∣ N`
  (for `t = 3`: "uniformity on any three coordinates forces `8 ∣ |C|`"), and for strength three with
  `N ≡ 8 (mod 16)` every character sum of weight four is nonzero. File `StealthAudit/Marginals.lean`.
  - Done 2026-11-24: `prod_one_add_sign`, `two_pow_mul_card_zeros`, `two_pow_mul_card_zeros_of_hasStrength`, `two_pow_dvd_card_of_hasStrength`, `charSum_ne_zero_of_card_mod_sixteen`. Only the all-zero pattern is counted; uniformity for the other patterns is not stated.

## C. The Hadamard construction

§3 after Proposition 3.1: Theorem 1.1 and the explicit integral certificate.

- [x] C1. Hadamard matrices (`IsHadamard H`: entries `±1`, `H Hᵀ = m I`): `Hᵀ H = m I`; two distinct rows
  differ in exactly `m/2` columns and agree in exactly `m/2` columns. File `StealthAudit/Hadamard.lean`.
  - Done 2026-11-24: `IsHadamard.row_orthogonal`, `IsHadamard.col_orthogonal`, `IsHadamard.transpose_mul`, `IsHadamard.two_mul_card_ne`, `IsHadamard.two_mul_card_eq`, `IsHadamard.entry_mul_self`
- [x] C2. Antipodal arrays: for a Hadamard matrix `H` of order `m` and `n ≥ 1` distinct columns,
  `antipodalMotif H c` (rows of `H` and `−H`, sign `s ↦ (1 − s)/2`) is binary with character sums
  `(1 + (−1)^{|S|}) ∑_r ∏_{i ∈ S} H r (c i)`, so it has strength three; hence `K = 1`,
  `ρ = 2m / 2ⁿ` (with multiplicity) and `Δ_st = 1/(2m)`. With `n = m` this is the converse half of
  Theorem 1.2. File `StealthAudit/AntipodalArray.lean`.
  - Done 2026-11-24: `isBinary_antipodalMotif`, `charSum_antipodalMotif`, `hasStrength_three_antipodalMotif`, `gapAtLeast_four_antipodalMotif`, `stealthRadius_antipodalMotif`, `density_antipodalMotif`, `centerDensity_antipodalMotif`
- [x] C3. The Paley matrix of order 12: with `χ` the quadratic character of `𝔽₁₁` and `S` indexed by
  `{∞} ∪ 𝔽₁₁` as in §3, `Sᵀ = −S`, `S Sᵀ = 11 I`, and `H = I + S` has entries `±1` and `H Hᵀ = 12 I`.
  All by kernel evaluation (`decide`), no `native_decide`. File `StealthAudit/Paley12.lean`.
  - Done 2026-11-24: `chi11_eq`, `paleyS_transpose`, `paleyS_mul_transpose`, `paley12_mul_transpose`, `paley12_entry`, `isHadamard_paley12`
- [x] C4. Distinct rows: if `m < 2n` (fewer than `m/2` columns deleted), the `2m` points of
  `antipodalMotif H c` are pairwise distinct modulo `2ℤⁿ`. File `StealthAudit/DistinctRows.lean`.
  - Done 2026-11-24: `distinctModPeriod_antipodalMotif`, `exists_col_mem_of_card_lt`, `eq_of_sub_eq_two_mul_int`
- [x] C5. Theorem 1.1 without the non-lattice clause: for `7 ≤ n ≤ 12` and `n` distinct columns of the
  Paley matrix, the 24 points are binary, distinct modulo `2ℤⁿ`, with `K = 1`, `ρ = 24/2ⁿ`, `Δ_st = 1/24`;
  for `n ∈ {10, 11, 12}` such a motif exists on the index type `Fin 24`. File `StealthAudit/Theorem11.lean`.
  - Done 2026-11-24: `paley_configuration`, `theorem_1_1`, and the relabelling lemmas `amp_reindex`, `gapSq_reindex`, `stealthRadius_reindex`, `density_reindex`, `centerDensity_reindex`, `distinctModPeriod_reindex`, `isBinary_reindex`
- [x] C6. The non-lattice clause of Theorem 1.1: if a binary motif with points distinct modulo `2ℤⁿ` has
  `X + 2ℤⁿ` equal to a translate of an additive subgroup of `ℝⁿ`, then `N` is a power of two (reduce
  modulo 2: the classes form a subgroup of `𝔽₂ⁿ`); `24` is not a power of two; hence the Paley
  configurations are not translates of additive subgroups, in particular not of lattices. Theorem 1.1
  with this clause. File `StealthAudit/NotLattice.lean`.
  - Done 2026-11-24: `exists_card_eq_two_pow`, `bits_injective`, `card_eq_two_pow_of_isSubgroupTranslate`, `twentyfour_ne_two_pow`, `not_isSubgroupTranslate_paley`, `theorem_1_1_full`. The last sentence of Theorem 1.1 (comparison with duals of record lattice packings) is arithmetic on quoted values, item G1.

## D. The sharp cardinality theorem

§4: Theorem 1.2 and Lemma 4.1. The bound `N ≥ 2n` and Lemma 4.1 are proved; the equality case of
Theorem 1.2 (items D4–D9) is open.

- [x] D1. Rank principle: for frequencies `b : κ → ℤⁿ` with `a_X(b q − b p) = 0` for all `p ≠ q`, the
  evaluation columns `(e^{πi (b p)·x})_x` are mutually orthogonal of squared norm `N`, so `|κ| ≤ N` for a
  nonempty motif. File `StealthAudit/RankPrinciple.lean`.
  - Done 2026-11-24: `evalMatrix`, `conjTranspose_mul_evalMatrix`, `conjTranspose_mul_evalMatrix_of_orthogonal`, `card_le_card_of_orthogonal`, `card_le_card_of_gapAtLeast`
- [x] D2. Indicator frequencies `ind S = ∑_{i ∈ S} eᵢ`: `‖ind T − ind S‖² = |S \ T| + |T \ S|`; the rank
  principle for an injective family of sets with pairwise symmetric differences of fewer than `s`
  elements. File `StealthAudit/Indicator.lean`.
  - Done 2026-11-24: `sqNorm_ind_sub_ind`, `sqNorm_ind`, `ind_injective`, `ind_sub_ind_ne_zero`, `card_le_card_of_gapAtLeast_ind`
- [x] D3. The bounds: `4K² ≥ 2` and `n ≥ 1` give `N ≥ 2`; `4K² ≥ 3` gives `N ≥ n + 1`; **Theorem 1.2, the
  bound**: `K ≥ 1` gives `N ≥ 2n` (frequencies `B_j = {0, e_j} ∪ {e_i, e_i + e_j : i ≠ j}`), for every `n`;
  **Lemma 4.1**: `K > 1` gives `N ≥ 1 + n + n(n−1)/2`. File `StealthAudit/CardinalityBound.lean`.
  - Done 2026-11-24: `two_le_card_of_gapAtLeast_two`, `succ_le_card_of_gapAtLeast_three`, `two_mul_le_card_of_gapAtLeast_four`, `rank_obstruction`, with `pivotSet`, `pivotSet_injective`, `card_sdiff_add_card_sdiff_le_three`. In terms of `stealthRadius`: `two_mul_le_card_of_one_le_stealthRadius`, `rank_obstruction_of_one_lt_stealthRadius` (in `StealthRadius.lean`).
- [ ] D4. Row orthogonality in the equality case: if `κ` is a finite type with
  `Fintype.card κ = Fintype.card ι`, `ι` nonempty, and `b : κ → Fin n → ℤ` satisfies
  `amp X (b q − b p) = 0` for all `p ≠ q`, then for all `k l : ι`,
  `∑ p, conj (phase (b p) (X k)) * phase (b p) (X l) = if k = l then N else 0`
  (reindex `evalMatrix X b` to a square matrix along `Fintype.equivOfCardEq`; from
  `conjTranspose_mul_evalMatrix_of_orthogonal` of D1, `((N : ℂ)⁻¹ • Mᴴ) * M = 1`, and `mul_eq_one_comm`
  gives `M * ((N : ℂ)⁻¹ • Mᴴ) = 1`). File `StealthAudit/RowOrthogonality.lean`.
- [ ] D5. The pivot factorization (4): for `x y : Fin n → ℝ`, `j : Fin n`, and `w i = phase (ind {i}) (y − x)`
  (that is, `e^{πi (yᵢ − xᵢ)}`), prove `phase (ind S) (y − x) = ∏ i ∈ S, w i` and
  `∑ p : Fin n × Bool, conj (phase (ind (pivotSet j p)) x) * phase (ind (pivotSet j p)) y`
  `= (1 + w j) * (1 + ∑ i ∈ univ.erase j, w i)` (`pivotSet` of D3; the sum over `p = (i, c)` splits as
  `(1 + w j) * ∑ i, (if i = j then 1 else w i)`). File `StealthAudit/PivotFactorization.lean`.
- [ ] D6. The unit-modulus system: let `n ≥ 3` and `w : Fin n → ℂ` with `‖w i‖ = 1` for all `i` and
  `(1 + w j) * (1 + ∑ i ∈ univ.erase j, w i) = 0` for all `j`. Then every `w i` is `1` or `−1`, and either
  all `w i = −1` or `2 * #{i : w i = 1} = n`. Proof of §4: with `W = 1 + ∑ i, w i`, each `w j` is `−1` or
  `W`; if `r ≥ 1` of them equal `a = W ≠ −1`, then `(r − 1) a = n − r − 1`; `r = 1` forces `n = 2`; so `a`
  is real of modulus one, hence `a = 1` and `2r = n`. File `StealthAudit/UnitRootSystem.lean`.
- [ ] D7. Differences in the equality case: if `GapAtLeast X 4`, `Fintype.card ι = 2 * n` and `n ≥ 3`, then
  for `k ≠ l` every coordinate difference `X l i − X k i` is an integer, and the number of `i` for which it
  is odd is `n` or `n/2` (D4 with `κ = Fin n × Bool`, `b = ind ∘ pivotSet j`, for every `j`; D5; D6;
  `e^{πi d} = ±1` forces `d ∈ ℤ` with the matching parity). In particular the points are distinct modulo
  `2ℤⁿ`, and `n` is even when `N > 2`. File `StealthAudit/EqualityDifferences.lean`.
- [ ] D8. From Hamming distances to a Hadamard matrix: let `Y : ι → Fin n → ℝ` be a binary motif with
  `Fintype.card ι = 2 * n`, `n ≥ 1`, such that for `k ≠ l` the points `Y k`, `Y l` differ in exactly `n` or
  exactly `n/2` coordinates (`2 * #{i : Y k i ≠ Y l i} = n` in the second case). Then there are a Hadamard
  matrix `H : Matrix (Fin n) (Fin n) ℤ` and a bijection `e : Fin n × Bool ≃ ι` with
  `Y (e p) = antipodalMotif H id p` for all `p` (sign vectors `1 − 2Y k` have pairwise inner products `0`
  or `−n`; "differ in all coordinates" pairs the points; non-paired points are orthogonal, and there are
  at most `n` mutually orthogonal nonzero vectors in `ℝⁿ`, so there are exactly `n` pairs).
  Probably two files; split when taken. File `StealthAudit/EqualityHadamard.lean`.
- [ ] D9. Theorem 1.2 assembled: for `n ≥ 3`, a nonempty motif `X` with `Fintype.card ι = 2 * n` has
  `GapAtLeast X 4` if and only if there are `t : Fin n → ℝ`, a Hadamard matrix `H` of order `n`, a
  bijection `e : Fin n × Bool ≃ ι` and integers `z` with
  `X (e p) i = t i + antipodalMotif H id p i + 2 * z p i` (forward: D7, D8 after translating `X k₀` to the
  origin and reducing modulo 2; backward: `gapAtLeast_four_antipodalMotif` of C2, `gapAtLeast_translate`
  and `amp_add_period` of A1). File `StealthAudit/Theorem12.lean`.

## E. Optimality consequences

§5: Theorem 5.1, Corollary 5.2, Theorem 5.3.

- [x] E1. Theorem 5.1 (bounded-complexity cubic optimality), the inequality and the first half of the
  equality clause: for `n ≥ 5` and `N < D_n = 1 + n + n(n−1)/2` points at arbitrary real positions,
  `Δ_st ≤ 1/(2n)`, and `Δ_st = 1/(2n)` exactly when `4K² = 4` and `N = 2n`. Corollary 5.2, the
  inequality: for `n = 12` and `N < 79`, `Δ_st ≤ 1/24`. File `StealthAudit/BoundedComplexity.lean`.
  - Done 2026-11-24: `centerDensity_le_of_card_lt`, `centerDensity_eq_iff_of_card_lt`, `centerDensity_le_dim_twelve`, `centerDensity_lt_or_gapSq_eq_four`, `gapSq_le_four_of_card_lt`, `centerDensity_le_inv_of_gapSq_bound`, `centerDensity_lt_inv_of_gapSq_bound`, `sq_lt_two_pow`, `four_mul_three_pow_lt_four_pow`. That the equality case is a translated antipodal Hadamard array is item E3 (it needs D9).
- [x] E2. Theorem 5.3 (all binary motifs in dimensions 10–12): for `n ∈ {10, 11, 12}` every nonempty
  binary motif has `Δ_st ≤ 1/24`, with equality exactly for strength three with 24 points, and the value
  `1/24` is attained. File `StealthAudit/BinaryOptimality.lean`.
  - Done 2026-11-24: `centerDensity_le_of_isBinary`, `centerDensity_eq_iff_of_isBinary`, `exists_isBinary_centerDensity_eq`, `twentyfour_le_card_of_hasStrength_three`, `centerDensity_lt_or_hasStrength_three`. "Strength three" is the Fourier form `HasStrength X 3`; repeated points are allowed in the bound.
- [ ] E3. The last sentence of Theorem 5.1 and the equality statement of Corollary 5.2: under the
  hypotheses of E1, `Δ_st = 1/(2n)` if and only if `X` is, up to a common translation and shifts by
  `2ℤⁿ`, an antipodal Hadamard array in the sense of D9 (from `centerDensity_eq_iff_of_card_lt` of E1,
  `gapAtLeast_iff_le_gapSq` of A2 and D9); for `n = 12`, `N < 79`: `Δ_st = 1/24` exactly for translated
  24-point antipodal Hadamard configurations. File `StealthAudit/BoundedComplexityEquality.lean`.

## F. Local optimality of the marked configuration

§6: Lemma 6.1 and Theorem 1.3. Nothing of this section is proved yet except the weight-four step
(`charSum_ne_zero_of_card_mod_sixteen` in B3).

- [ ] F1. The sign lemma inside Lemma 6.1: let `n ≥ 4` and let `E : Matrix (Fin n) (Fin n) ℝ` be
  symmetric with trace `0` and `E ≠ 0`. Then there is `v` in
  `V = {2eᵢ} ∪ {∑_{i ∈ I} εᵢ eᵢ : |I| = 4, εᵢ = ±1}` with `vᵀ E v < 0`. (If some `E i i < 0` take `2eᵢ`.
  Otherwise all diagonal entries vanish; pick `a ≠ b` with `E a b ≠ 0` and a 4-set `I ∋ a, b`; the 16
  values `q(ε) = ∑_{i ≠ j ∈ I} εᵢ εⱼ E i j` sum to `0`, and `∑_ε ε_a ε_b q(ε) = 32 E a b ≠ 0`, so some
  `q(ε) < 0`.) State `V` as a `Set (Fin n → ℤ)` named `testVectors n`. File `StealthAudit/TraceFreeSign.lean`.
- [ ] F2. Amplitudes on the test vectors: for a binary motif of strength three with
  `N ≡ 8 (mod 16)` and `n ≥ 4`, `amp X v ≠ 0` for every `v ∈ testVectors n` (for `2eᵢ`:
  `amp_two_mul_single` of B1; for `|I| = 4`: `amp_of_isBinary` with `oddSupp v = I`, then
  `charSum_ne_zero_of_card_mod_sixteen` of B3). File `StealthAudit/TestAmplitudes.lean`.
- [ ] F3. Lemma 6.1 (strict reciprocal-Gram maximum): with `m Q = ⨅ v ∈ testVectors n, vᵀ Q v` (a minimum
  over a finite set), there is `δ > 0` such that every symmetric positive definite `Q` with `det Q = 1`
  and `0 < ‖Q − 1‖ < δ` has `m Q < 4`, and `m 1 = 4`. (F1, compactness of the unit sphere of trace-free
  symmetric matrices for the constant `c_n`, and `tr F = O(‖F‖²)` from `det (1 + F) = 1`.) Split when
  taken. File `StealthAudit/ReciprocalGram.lean`.
- [ ] F4. Stability of the amplitudes: for fixed `u`, `X ↦ amp X u` is continuous on `ι → Fin n → ℝ`, so a
  finite set of nonzero amplitudes stays nonzero in a neighbourhood of `X`.
  File `StealthAudit/AmpContinuity.lean`.
- [ ] F5. Theorem 1.3 in the marked period model of A3: for a binary motif `C` of strength three with
  `N ≡ 8 (mod 16)`, `n ≥ 4`: there are neighbourhoods of `C` and of `Q = 1` (determinant one, positive
  definite) on which `centerDensityQ X Q ≤ 1/N = centerDensityQ C 1`, with strict inequality when `Q ≠ 1`
  (A3, F2, F3, F4). The isolation statement for `n = 12`, `N = 24` needs D9. Split when taken.
  File `StealthAudit/Theorem13.lean`.

## G. Formal duality and numerical comparisons

§7. The lattice values in the table are quoted from the literature; only arithmetic is checked.

- [x] G1. The comparisons of the table: `3^{5/2} = 9√3`; the ratios `(1/24)/(1/(16√3)) = 2/√3`,
  `(1/24)/(1/(2·3^{5/2})) = 3^{5/2}/12`, `(1/24)/(1/27) = 9/8`; `1/(16√3)`, `1/(2·3^{5/2})`, `1/27`,
  `5/128`, `9/256` are all below `1/24`. File `StealthAudit/Comparisons.lean`.
  - Done 2026-11-24: `three_rpow_five_halves`, `ratio_dim_ten`, `ratio_dim_eleven`, `ratio_dim_twelve`, `lt_dim_ten`, `lt_dim_eleven`, `lt_dim_twelve`, `cohn_table_lt`. The six lattice and packing values are inputs, not derived.
- [ ] G2. The unit-density radii of the table: with `r n = 2 * (24 : ℝ) ^ (-(1 / (n : ℝ)))`, prove
  `1.455488 < r 10 < 1.455489`, `1.498153 < r 11 < 1.498154`, `1.534660 < r 12 < 1.534661` (each bound
  `a < 2 · 24^{-1/n}` is `(a / 2) ^ n * 24 < 1`, a rational inequality for `norm_num`, through
  `Real.rpow_natCast` and monotonicity of `x ↦ x ^ n`), and `r n = 2 * (centerDensity X) ^ (1 / (n : ℝ))`
  for the motif of `theorem_1_1`. File `StealthAudit/UnitDensityRadius.lean`.
- [x] G3. The arithmetic of Proposition 7.1: for a binary motif `a_X(2u) = N` for every `u ∈ ℤⁿ`;
  `24 ∤ 2ⁿ`; `2ⁿ/24` is not an integer. File `StealthAudit/FormalDualityArithmetic.lean`.
  - Done 2026-11-24: `amp_two_mul`, `not_twentyfour_dvd_two_pow`, `two_pow_div_twentyfour_not_int`. Proposition 7.1 itself is not proved (see "Not attempted here").

## Not attempted here

- The diffraction measure of a periodic set and the derivation of formula (2) from it. `stealthRadius` is defined by (2).
- Proposition 7.1 (no ordinary periodic formal dual): it needs a Lean definition of formal duality of periodic configurations in the sense of Cohn, Kumar, Reiher and Schürmann. Only its arithmetic is checked (G3).
- The values quoted in §7 from the literature (center densities of duals of record lattice packings, Cohn's table). They enter G1 as numbers.
- Any statement about arbitrary period lattices or supercells beyond the marked period model of Theorem 1.3; the paper claims none.
- The finite-instance Python script `verify_hadamard.py` of §8 is not part of this repository; its checks of the Paley matrix are subsumed by C1–C5.
