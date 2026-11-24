import StealthAudit.Marginals
import StealthAudit.BoundedComplexity
import StealthAudit.Theorem11

/-!
# E2. Theorem 5.3: all binary motifs in dimensions 10–12

For `n ∈ {10, 11, 12}` and a nonempty binary motif `X : ι → Fin n → ℝ` (repeated points
allowed), with marked period `2ℤⁿ`:

* `twentyfour_le_card_of_hasStrength_three`: a binary motif of strength three in dimension
  `n ≥ 10` has at least 24 points (`N ≥ 2n` by Theorem 1.2 and `8 ∣ N` by B3);
* `centerDensity_lt_or_hasStrength_three`: either `Δ_st < 1/24`, or the motif has strength three;
* `centerDensity_le_of_isBinary`: **Theorem 5.3, the bound.** `Δ_st(X + 2ℤⁿ) ≤ 1/24`;
* `centerDensity_eq_iff_of_isBinary`: **Theorem 5.3, the equality case.** `Δ_st = 1/24` exactly
  when the motif has strength three and 24 points;
* `exists_isBinary_centerDensity_eq`: the value `1/24` is attained (by the projected Paley arrays
  of Theorem 1.1), so the maximum over binary motifs is `1/24`.

"Strength three" is `HasStrength X 3`, the Fourier form (character sums of weights 1, 2, 3
vanish); for motifs without repeated points this is the paper's "orthogonal array of strength
three".

What this file does NOT prove: anything about motifs that are not binary (Theorem 5.1 is
`BoundedComplexity.lean`), or about period lattices other than `2ℤⁿ`.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Fin n → ℝ}

/-- A binary motif of strength three in dimension `n ≥ 10` has at least 24 points. -/
theorem twentyfour_le_card_of_hasStrength_three (hn : 10 ≤ n) (hX : IsBinary X)
    (hs : HasStrength X 3) : 24 ≤ Fintype.card ι := by
  have h8 := two_pow_dvd_card_of_hasStrength hX hs (by omega : 3 ≤ n)
  have h2n := two_mul_le_card_of_gapAtLeast_four X (gapAtLeast_of_hasStrength hX 3 le_rfl hs)
  obtain ⟨m, hm⟩ := h8
  omega

/-- For `n ∈ {10, 11, 12}`, a binary motif has `Δ_st < 1/24` unless it has strength three. -/
theorem centerDensity_lt_or_hasStrength_three (hn : n = 10 ∨ n = 11 ∨ n = 12) (hX : IsBinary X) :
    centerDensity X < 1 / 24 ∨ HasStrength X 3 := by
  have hn0 : 0 < n := by omega
  have hg := gapSq_le_four hn0 hX
  have hpos := gapSq_pos hn0 X
  have gap : ∀ s : ℕ, s ≤ gapSq X → GapAtLeast X s := fun s hs =>
    (gapAtLeast_iff_le_gapSq hn0 X s).mpr (by exact_mod_cast hs)
  obtain h | h | h | h : gapSq X = 1 ∨ gapSq X = 2 ∨ gapSq X = 3 ∨ gapSq X = 4 := by omega
  · left
    have h' := centerDensity_lt_inv_of_gapSq_bound X 24 1 (by norm_num) Fintype.card_pos
      (by rw [h]; rcases hn with rfl | rfl | rfl <;> norm_num)
    norm_num at h' ⊢
    exact h'
  · left
    have h' := centerDensity_lt_inv_of_gapSq_bound X 24 2 (by norm_num)
      (two_le_card_of_gapAtLeast_two hn0 X (gap 2 (by omega)))
      (by rw [h]; rcases hn with rfl | rfl | rfl <;> norm_num)
    norm_num at h' ⊢
    exact h'
  · left
    have h' := centerDensity_lt_inv_of_gapSq_bound X 24 (n + 1) (by norm_num)
      (succ_le_card_of_gapAtLeast_three X (gap 3 (by omega)))
      (by rw [h]; rcases hn with rfl | rfl | rfl <;> norm_num)
    norm_num at h' ⊢
    exact h'
  · right
    exact (gapSq_eq_four_iff_hasStrength hn0 hX).mp h

/-- **Theorem 5.3, the bound.** For `n ∈ {10, 11, 12}`, every nonempty binary motif has
`Δ_st(X + 2ℤⁿ) ≤ 1/24`. -/
theorem centerDensity_le_of_isBinary (hn : n = 10 ∨ n = 11 ∨ n = 12) (hX : IsBinary X) :
    centerDensity X ≤ 1 / 24 := by
  rcases centerDensity_lt_or_hasStrength_three hn hX with h | h
  · exact h.le
  · rw [centerDensity_of_hasStrength_three (by omega) hX h]
    have h24 := twentyfour_le_card_of_hasStrength_three (by omega) hX h
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h24)

/-- **Theorem 5.3, the equality case.** For `n ∈ {10, 11, 12}`, a nonempty binary motif has
`Δ_st = 1/24` exactly when it has strength three and 24 points. -/
theorem centerDensity_eq_iff_of_isBinary (hn : n = 10 ∨ n = 11 ∨ n = 12) (hX : IsBinary X) :
    centerDensity X = 1 / 24 ↔ HasStrength X 3 ∧ Fintype.card ι = 24 := by
  have hNpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · intro heq
    rcases centerDensity_lt_or_hasStrength_three hn hX with h | h
    · exact absurd heq h.ne
    · refine ⟨h, ?_⟩
      rw [centerDensity_of_hasStrength_three (by omega) hX h] at heq
      have h2 : (Fintype.card ι : ℝ) = 24 := by
        field_simp at heq
        linarith
      exact_mod_cast h2
  · rintro ⟨h, hc⟩
    rw [centerDensity_of_hasStrength_three (by omega) hX h, hc]
    norm_num

omit [Fintype ι] [Nonempty ι] in
/-- The bound of Theorem 5.3 is attained: for `n ∈ {10, 11, 12}` there is a binary motif of 24
points, distinct modulo `2ℤⁿ`, with `Δ_st = 1/24`. -/
theorem exists_isBinary_centerDensity_eq (n : ℕ) (hn : n = 10 ∨ n = 11 ∨ n = 12) :
    ∃ X : Fin 24 → Fin n → ℝ, IsBinary X ∧ DistinctModPeriod X ∧ centerDensity X = 1 / 24 := by
  obtain ⟨X, hb, hd, -, -, hΔ⟩ := theorem_1_1 n hn
  exact ⟨X, hb, hd, hΔ⟩

end Stealth

end
