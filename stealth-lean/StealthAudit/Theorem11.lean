import StealthAudit.DistinctRows
import StealthAudit.Paley12

/-!
# C5. Theorem 1.1 (explicit examples), without the non-lattice clause

The configurations `P_n` of the paper are `antipodalMotif paley12 c + 2ℤⁿ` for `n` distinct
columns `c` of the order-12 Paley matrix. Proved here:

* `amp_reindex`, `gapSq_reindex`, `stealthRadius_reindex`, `density_reindex`,
  `centerDensity_reindex`, `distinctModPeriod_reindex`, `isBinary_reindex`: relabelling the points
  of a motif along a bijection changes nothing;
* `paley_configuration`: for `7 ≤ n` and any `n` distinct columns, the 24 points are `0/1`
  vectors, pairwise distinct modulo `2ℤⁿ`, with `K(P) = 1`, `ρ(P) = 24 / 2ⁿ`, `Δ_st(P) = 1/24`;
* `theorem_1_1`: for each `n ∈ {10, 11, 12}` there is a motif `X : Fin 24 → Fin n → ℝ` of 24
  points, pairwise distinct modulo `2ℤⁿ`, with `K(P) = 1`, `ρ(P) = 24 / 2ⁿ` and
  `Δ_st(P) = 1/24`.

What this file does NOT prove: the remaining clauses of Theorem 1.1, namely that the
configurations are not translates of lattices (roadmap item C6, `NotLattice.lean`) and the comparison of the
unit-density radius `2 · 24^{-1/n}` with duals of record lattice packings (section G; those
record values are quoted from Cohn's table, not derived). `K(P)` is the quantity defined by
formula (2) of the paper, not a radius derived from a diffraction measure.
-/

noncomputable section

open Finset

namespace Stealth

/-! ### Relabelling the points -/

section Reindex

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem amp_reindex (e : κ ≃ ι) (X : ι → Fin n → ℝ) : amp (X ∘ e) = amp X := by
  funext u
  exact Equiv.sum_comp e fun k => phase u (X k)

theorem gapSq_reindex (e : κ ≃ ι) (X : ι → Fin n → ℝ) : gapSq (X ∘ e) = gapSq X := by
  unfold gapSq Survives
  rw [amp_reindex]

theorem stealthRadius_reindex (e : κ ≃ ι) (X : ι → Fin n → ℝ) :
    stealthRadius (X ∘ e) = stealthRadius X := by
  unfold stealthRadius
  rw [gapSq_reindex]

theorem density_reindex (e : κ ≃ ι) (X : ι → Fin n → ℝ) : density (X ∘ e) = density X := by
  unfold density
  rw [Fintype.card_congr e]

theorem centerDensity_reindex (e : κ ≃ ι) (X : ι → Fin n → ℝ) :
    centerDensity (X ∘ e) = centerDensity X := by
  unfold centerDensity
  rw [stealthRadius_reindex, density_reindex]

omit [Fintype ι] [Fintype κ] in
theorem distinctModPeriod_reindex (e : κ ≃ ι) {X : ι → Fin n → ℝ} (h : DistinctModPeriod X) :
    DistinctModPeriod (X ∘ e) := fun k l hkl => h (e k) (e l) fun h' => hkl (e.injective h')

omit [Fintype ι] [Fintype κ] in
theorem isBinary_reindex (e : κ ≃ ι) {X : ι → Fin n → ℝ} (h : IsBinary X) : IsBinary (X ∘ e) :=
  fun k i => h (e k) i

end Reindex

/-! ### The Paley configurations -/

theorem card_paley_index : Fintype.card (Option (ZMod 11) × Bool) = 24 := by decide

/-- The projected Paley arrays: for `7 ≤ n` and `n` distinct columns of the order-12 Paley
matrix, the 24 rows of `H` and `-H` give a binary motif of 24 points, distinct modulo `2ℤⁿ`,
with `K(P) = 1`, `ρ(P) = 24 / 2ⁿ` and `Δ_st(P) = 1/24`. -/
theorem paley_configuration {n : ℕ} (hn : 7 ≤ n) {c : Fin n → Option (ZMod 11)}
    (hc : Function.Injective c) :
    IsBinary (antipodalMotif paley12 c) ∧ DistinctModPeriod (antipodalMotif paley12 c) ∧
      stealthRadius (antipodalMotif paley12 c) = 1 ∧
      density (antipodalMotif paley12 c) = 24 / 2 ^ n ∧
      centerDensity (antipodalMotif paley12 c) = 1 / 24 := by
  have hcard : Fintype.card (Option (ZMod 11)) = 12 := by decide
  refine ⟨isBinary_antipodalMotif isHadamard_paley12 c,
    distinctModPeriod_antipodalMotif isHadamard_paley12 hc (by rw [hcard]; omega),
    stealthRadius_antipodalMotif (by omega) isHadamard_paley12 hc, ?_, ?_⟩
  · rw [density_antipodalMotif, hcard]
    norm_num
  · rw [centerDensity_antipodalMotif (by omega) isHadamard_paley12 hc, hcard]
    norm_num

/-- **Theorem 1.1 (explicit examples), without the non-lattice clause.** For each
`n ∈ {10, 11, 12}` there is a periodic configuration `X + 2ℤⁿ` with 24 representatives modulo
`2ℤⁿ` (pairwise distinct) such that `K = 1`, `ρ = 24 / 2ⁿ` and `Δ_st = 1/24`. -/
theorem theorem_1_1 (n : ℕ) (hn : n = 10 ∨ n = 11 ∨ n = 12) :
    ∃ X : Fin 24 → Fin n → ℝ, IsBinary X ∧ DistinctModPeriod X ∧ stealthRadius X = 1 ∧
      density X = 24 / 2 ^ n ∧ centerDensity X = 1 / 24 := by
  have hcard : Fintype.card (Option (ZMod 11)) = 12 := by decide
  obtain ⟨c⟩ : Nonempty (Fin n ↪ Option (ZMod 11)) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hcard]; omega)
  obtain ⟨hb, hd, hK, hρ, hΔ⟩ := paley_configuration (n := n) (by omega) c.injective
  let e : Fin 24 ≃ Option (ZMod 11) × Bool :=
    (Fintype.equivFinOfCardEq card_paley_index).symm
  refine ⟨antipodalMotif paley12 c ∘ e, isBinary_reindex e hb, distinctModPeriod_reindex e hd, ?_,
    ?_, ?_⟩
  · rw [stealthRadius_reindex, hK]
  · rw [density_reindex, hρ]
  · rw [centerDensity_reindex, hΔ]

end Stealth

end
