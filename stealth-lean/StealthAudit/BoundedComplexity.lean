import StealthAudit.StealthRadius

/-!
# E1. Theorem 5.1: bounded-complexity cubic optimality

For a nonempty motif `X : ι → Fin n → ℝ` at arbitrary real positions with marked period `2ℤⁿ`,
`N = Fintype.card ι` and `D_n = 1 + n + n(n-1)/2`. Proved here:

* `sq_lt_two_pow`, `four_mul_three_pow_lt_four_pow`: `n² < 2ⁿ` and `4 · 3ⁿ < 4ⁿ` for `n ≥ 5`
  (the arithmetic behind the comparison of the four terms of (5));
* `centerDensity_le_inv_of_gapSq_bound`, `centerDensity_lt_inv_of_gapSq_bound`: if `N ≥ M` and
  `c² · (4K²)ⁿ ≤ M² · 4ⁿ` (resp. `<`), then `Δ_st ≤ 1/c` (resp. `<`); the case `c = 2n` is
  `centerDensity_le_of_gapSq_bound`, `centerDensity_lt_of_gapSq_bound`;
* `gapSq_le_four_of_card_lt`: if `N < D_n` then `K(P) ≤ 1` (Lemma 4.1);
* `centerDensity_le_of_card_lt`: **Theorem 5.1, the inequality.** If `n ≥ 5` and `N < D_n`, then
  `Δ_st(P) ≤ 1/(2n)`;
* `centerDensity_eq_iff_of_card_lt`: **Theorem 5.1, the equality clause, first half.** Under the
  same hypotheses, `Δ_st(P) = 1/(2n)` exactly when `4 K(P)² = 4` and `N = 2n`;
* `centerDensity_le_dim_twelve`: **Corollary 5.2, the inequality.** For `n = 12` and `N < 79`,
  `Δ_st(P) ≤ 1/24`.

What this file does NOT prove: that the equality case `K(P) = 1`, `N = 2n` is a translated
antipodal Hadamard array (the equality case of Theorem 1.2, roadmap items D4–D9), hence not the
last sentence of Theorem 5.1 nor the equality statement of Corollary 5.2. Nothing here concerns
period lattices other than `2ℤⁿ`.
-/

noncomputable section

open Finset

namespace Stealth

/-! ### Arithmetic -/

theorem sq_lt_two_pow {n : ℕ} (hn : 5 ≤ n) : n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h5 : 5 * m ≤ m * m := Nat.mul_le_mul_right m hm
    rw [h2]
    nlinarith

theorem four_mul_three_pow_lt_four_pow {n : ℕ} (hn : 5 ≤ n) : 4 * 3 ^ n < 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ, pow_succ]
    omega

theorem four_pow_eq (n : ℕ) : 4 ^ n = 2 ^ n * 2 ^ n := by
  rw [← mul_pow]
  norm_num

/-! ### From a bound on the gap to a bound on the density -/

section Density

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem stealthRadius_nonneg (X : ι → Fin n → ℝ) : 0 ≤ stealthRadius X := by
  unfold stealthRadius
  positivity

omit [Nonempty ι] in
/-- `(c Kⁿ)² · 4ⁿ = c² (4K²)ⁿ`. -/
theorem mul_radius_pow_sq (X : ι → Fin n → ℝ) (c : ℝ) :
    (c * stealthRadius X ^ n) ^ 2 * 4 ^ n = c ^ 2 * (gapSq X : ℝ) ^ n := by
  rw [← four_mul_stealthRadius_sq X]
  ring

/-- If `N ≥ M` and `c² (4K²)ⁿ ≤ M² 4ⁿ`, then `Δ_st ≤ 1/c`. -/
theorem centerDensity_le_inv_of_gapSq_bound (X : ι → Fin n → ℝ) (c M : ℕ) (hc : 0 < c)
    (hM : M ≤ Fintype.card ι) (h : c ^ 2 * gapSq X ^ n ≤ M ^ 2 * 4 ^ n) :
    centerDensity X ≤ 1 / (c : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hK := stealthRadius_nonneg X
  have h' : (c : ℝ) ^ 2 * (gapSq X : ℝ) ^ n ≤ (M : ℝ) ^ 2 * 4 ^ n := by exact_mod_cast h
  rw [← mul_radius_pow_sq] at h'
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hsq : ((c : ℝ) * stealthRadius X ^ n) ^ 2 ≤ (M : ℝ) ^ 2 := le_of_mul_le_mul_right h' h4
  have hle : (c : ℝ) * stealthRadius X ^ n ≤ (M : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hMN : (M : ℝ) ≤ Fintype.card ι := by exact_mod_cast hM
  rw [centerDensity_eq, div_le_div_iff₀ hN hc']
  linarith

/-- If `N ≥ M` and `c² (4K²)ⁿ < M² 4ⁿ`, then `Δ_st < 1/c`. -/
theorem centerDensity_lt_inv_of_gapSq_bound (X : ι → Fin n → ℝ) (c M : ℕ) (hc : 0 < c)
    (hM : M ≤ Fintype.card ι) (h : c ^ 2 * gapSq X ^ n < M ^ 2 * 4 ^ n) :
    centerDensity X < 1 / (c : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hK := stealthRadius_nonneg X
  have h' : (c : ℝ) ^ 2 * (gapSq X : ℝ) ^ n < (M : ℝ) ^ 2 * 4 ^ n := by exact_mod_cast h
  rw [← mul_radius_pow_sq] at h'
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hsq : ((c : ℝ) * stealthRadius X ^ n) ^ 2 < (M : ℝ) ^ 2 := lt_of_mul_lt_mul_right h' h4.le
  have hlt : (c : ℝ) * stealthRadius X ^ n < (M : ℝ) :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hMN : (M : ℝ) ≤ Fintype.card ι := by exact_mod_cast hM
  rw [centerDensity_eq, div_lt_div_iff₀ hN hc']
  linarith

/-- If `N ≥ M` and `(2n)² (4K²)ⁿ ≤ M² 4ⁿ`, then `Δ_st ≤ 1/(2n)`. -/
theorem centerDensity_le_of_gapSq_bound (hn : 0 < n) (X : ι → Fin n → ℝ) (M : ℕ)
    (hM : M ≤ Fintype.card ι) (h : (2 * n) ^ 2 * gapSq X ^ n ≤ M ^ 2 * 4 ^ n) :
    centerDensity X ≤ 1 / (2 * (n : ℝ)) := by
  have h' := centerDensity_le_inv_of_gapSq_bound X (2 * n) M (by omega) hM h
  push_cast at h'
  exact h'

/-- If `N ≥ M` and `(2n)² (4K²)ⁿ < M² 4ⁿ`, then `Δ_st < 1/(2n)`. -/
theorem centerDensity_lt_of_gapSq_bound (hn : 0 < n) (X : ι → Fin n → ℝ) (M : ℕ)
    (hM : M ≤ Fintype.card ι) (h : (2 * n) ^ 2 * gapSq X ^ n < M ^ 2 * 4 ^ n) :
    centerDensity X < 1 / (2 * (n : ℝ)) := by
  have h' := centerDensity_lt_inv_of_gapSq_bound X (2 * n) M (by omega) hM h
  push_cast at h'
  exact h'

/-- If `N < D_n`, then `K(P) ≤ 1` (the contrapositive of Lemma 4.1). -/
theorem gapSq_le_four_of_card_lt (hn : 0 < n) (X : ι → Fin n → ℝ)
    (hN : Fintype.card ι < 1 + n + n.choose 2) : gapSq X ≤ 4 := by
  by_contra hlt
  have h5 : GapAtLeast X 5 := (gapAtLeast_iff_le_gapSq hn X 5).mpr (by omega)
  have := rank_obstruction X h5
  omega

/-- For `n ≥ 5`, either `Δ_st < 1/(2n)`, or `4 K(P)² = 4`. -/
theorem centerDensity_lt_or_gapSq_eq_four (hn : 5 ≤ n) (X : ι → Fin n → ℝ)
    (hN : Fintype.card ι < 1 + n + n.choose 2) :
    centerDensity X < 1 / (2 * (n : ℝ)) ∨ gapSq X = 4 := by
  have hn0 : 0 < n := by omega
  have hg := gapSq_le_four_of_card_lt hn0 X hN
  have hpos := gapSq_pos hn0 X
  have hsq := sq_lt_two_pow hn
  have h34 := four_mul_three_pow_lt_four_pow hn
  have h4 := four_pow_eq n
  have h2n : 32 ≤ 2 ^ n := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have gap : ∀ s : ℕ, s ≤ gapSq X → GapAtLeast X s := fun s hs =>
    (gapAtLeast_iff_le_gapSq hn0 X s).mpr (by exact_mod_cast hs)
  obtain h | h | h | h : gapSq X = 1 ∨ gapSq X = 2 ∨ gapSq X = 3 ∨ gapSq X = 4 := by omega
  · left
    refine centerDensity_lt_of_gapSq_bound hn0 X 1 Fintype.card_pos ?_
    rw [h, h4]
    have e1 : (2 * n) ^ 2 * 1 ^ n = 4 * n ^ 2 := by ring
    have e2 : 1 ^ 2 * (2 ^ n * 2 ^ n) = 2 ^ n * 2 ^ n := by ring
    rw [e1, e2]
    calc 4 * n ^ 2 < 4 * 2 ^ n := by omega
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
  · left
    refine centerDensity_lt_of_gapSq_bound hn0 X 2
      (two_le_card_of_gapAtLeast_two hn0 X (gap 2 (by omega))) ?_
    rw [h, h4]
    have e1 : (2 * n) ^ 2 * 2 ^ n = 4 * (n ^ 2 * 2 ^ n) := by ring
    have e2 : 2 ^ 2 * (2 ^ n * 2 ^ n) = 4 * (2 ^ n * 2 ^ n) := by ring
    rw [e1, e2]
    have hlt : n ^ 2 * 2 ^ n < 2 ^ n * 2 ^ n :=
      mul_lt_mul_of_pos_right hsq (by positivity)
    omega
  · left
    refine centerDensity_lt_of_gapSq_bound hn0 X (n + 1)
      (succ_le_card_of_gapAtLeast_three X (gap 3 (by omega))) ?_
    rw [h]
    have e1 : (2 * n) ^ 2 * 3 ^ n = n ^ 2 * (4 * 3 ^ n) := by ring
    rw [e1]
    have hn2 : 0 < n ^ 2 := by positivity
    calc n ^ 2 * (4 * 3 ^ n) < n ^ 2 * 4 ^ n := mul_lt_mul_of_pos_left h34 hn2
      _ ≤ (n + 1) ^ 2 * 4 ^ n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
  · right
    exact h

/-- **Theorem 5.1 (bounded-complexity cubic optimality), the inequality.** Let `n ≥ 5` and let
`P = X + 2ℤⁿ` have `N < D_n = 1 + n + n(n-1)/2` representatives at arbitrary real positions.
Then `Δ_st(P) ≤ 1/(2n)`. -/
theorem centerDensity_le_of_card_lt (hn : 5 ≤ n) (X : ι → Fin n → ℝ)
    (hN : Fintype.card ι < 1 + n + n.choose 2) : centerDensity X ≤ 1 / (2 * (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  rcases centerDensity_lt_or_gapSq_eq_four hn X hN with h | h
  · exact h.le
  · have h2n := two_mul_le_card_of_gapAtLeast_four X
      ((gapAtLeast_iff_le_gapSq hn0 X 4).mpr (by rw [h]; norm_num))
    refine centerDensity_le_of_gapSq_bound hn0 X (2 * n) h2n ?_
    rw [h]

/-- **Theorem 5.1, the equality clause (first half).** Under the hypotheses of Theorem 5.1,
`Δ_st(P) = 1/(2n)` exactly when `4 K(P)² = 4` (that is, `K(P) = 1`) and `N = 2n`. -/
theorem centerDensity_eq_iff_of_card_lt (hn : 5 ≤ n) (X : ι → Fin n → ℝ)
    (hN : Fintype.card ι < 1 + n + n.choose 2) :
    centerDensity X = 1 / (2 * (n : ℝ)) ↔ gapSq X = 4 ∧ Fintype.card ι = 2 * n := by
  have hn0 : 0 < n := by omega
  have hNpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hK1 : gapSq X = 4 → stealthRadius X = 1 := by
    intro h
    have h4 := four_mul_stealthRadius_sq X
    rw [h] at h4
    have hnn := stealthRadius_nonneg X
    have h1 : stealthRadius X ^ 2 = 1 := by
      have : (4 : ℝ) * stealthRadius X ^ 2 = 4 := by rw [h4]; norm_num
      linarith
    nlinarith [sq_nonneg (stealthRadius X - 1)]
  constructor
  · intro heq
    rcases centerDensity_lt_or_gapSq_eq_four hn X hN with h | h
    · exact absurd heq h.ne
    · refine ⟨h, ?_⟩
      rw [centerDensity_eq, hK1 h, one_pow] at heq
      have h2 : (Fintype.card ι : ℝ) = 2 * (n : ℝ) := by
        have hn' : (0 : ℝ) < 2 * (n : ℝ) := by positivity
        field_simp at heq
        linarith
      exact_mod_cast h2
  · rintro ⟨h, hcard⟩
    rw [centerDensity_eq, hK1 h, one_pow, hcard]
    push_cast
    ring

end Density

/-- **Corollary 5.2 (the dimension-12 cubic-cell threshold), the inequality.** Among equally
weighted periodic configurations with marked period `2ℤ¹²` and fewer than `D₁₂ = 79`
representatives in that cell, `Δ_st ≤ 1/24`. -/
theorem centerDensity_le_dim_twelve {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Fin 12 → ℝ)
    (hN : Fintype.card ι < 79) : centerDensity X ≤ 1 / 24 := by
  have h := centerDensity_le_of_card_lt (n := 12) (by norm_num) X (by
    have : Nat.choose 12 2 = 66 := by decide
    omega)
  norm_num at h ⊢
  exact h

end Stealth

end
