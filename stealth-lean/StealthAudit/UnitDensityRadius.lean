import StealthAudit.Theorem11

/-!
# G2. The unit-density radii of the table in §7

After rescaling the configurations of Theorem 1.1 to unit density, the stealth radius becomes
`r n = 2 · 24^{−1/n}`. The table of §7 lists `1.455488812…`, `1.498153270…`, `1.534660772…` for
`n = 10, 11, 12`. Proved here:

* `unitRadius_pow`: `(r n / 2)ⁿ = 1/24`;
* `lt_unitRadius_iff`, `unitRadius_lt_iff`: for `a ≥ 0`, `a < r n ↔ (a/2)ⁿ · 24 < 1` and
  `r n < a ↔ 1 < (a/2)ⁿ · 24`, so each table bound is a rational inequality;
* `unitRadius_ten`, `unitRadius_eleven`, `unitRadius_twelve`: the six-decimal bounds;
* `unitRadius_eq_centerDensity`: `r n = 2 · Δ_st(X)^{1/n}` for the motifs of `theorem_1_1`.

What this file does NOT prove: anything about the lattice values in the table (they are quoted from the
literature; see G1).
-/

noncomputable section

namespace Stealth

/-- The unit-density stealth radius `2 · 24^{−1/n}`. -/
def unitRadius (n : ℕ) : ℝ := 2 * (24 : ℝ) ^ (-(1 / (n : ℝ)))

theorem unitRadius_pos (n : ℕ) : 0 < unitRadius n := by
  unfold unitRadius; positivity

theorem unitRadius_pow {n : ℕ} (hn : n ≠ 0) : (unitRadius n / 2) ^ n = 1 / 24 := by
  unfold unitRadius
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  have : -(1 / (n : ℝ)) * n = -1 := by
    field_simp
  rw [this, Real.rpow_neg_one]
  norm_num

theorem lt_unitRadius_iff {n : ℕ} (hn : n ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    a < unitRadius n ↔ (a / 2) ^ n * 24 < 1 := by
  have hr := unitRadius_pos n
  have hpow := unitRadius_pow hn
  constructor
  · intro h
    have : (a / 2) ^ n < (unitRadius n / 2) ^ n :=
      pow_lt_pow_left₀ (by linarith) (by positivity) hn
    rw [hpow] at this
    linarith
  · intro h
    have h' : (a / 2) ^ n < (unitRadius n / 2) ^ n := by rw [hpow]; linarith
    have := lt_of_pow_lt_pow_left₀ n (by positivity) h'
    linarith

theorem unitRadius_lt_iff {n : ℕ} (hn : n ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    unitRadius n < a ↔ 1 < (a / 2) ^ n * 24 := by
  have hr := unitRadius_pos n
  have hpow := unitRadius_pow hn
  constructor
  · intro h
    have : (unitRadius n / 2) ^ n < (a / 2) ^ n :=
      pow_lt_pow_left₀ (by linarith) (by positivity) hn
    rw [hpow] at this
    linarith
  · intro h
    have h' : (unitRadius n / 2) ^ n < (a / 2) ^ n := by rw [hpow]; linarith
    have := lt_of_pow_lt_pow_left₀ n (by positivity) h'
    linarith

theorem unitRadius_ten : 1.455488 < unitRadius 10 ∧ unitRadius 10 < 1.455489 := by
  constructor
  · rw [lt_unitRadius_iff (by norm_num) (by norm_num)]; norm_num
  · rw [unitRadius_lt_iff (by norm_num) (by norm_num)]; norm_num

theorem unitRadius_eleven : 1.498153 < unitRadius 11 ∧ unitRadius 11 < 1.498154 := by
  constructor
  · rw [lt_unitRadius_iff (by norm_num) (by norm_num)]; norm_num
  · rw [unitRadius_lt_iff (by norm_num) (by norm_num)]; norm_num

theorem unitRadius_twelve : 1.534660 < unitRadius 12 ∧ unitRadius 12 < 1.534661 := by
  constructor
  · rw [lt_unitRadius_iff (by norm_num) (by norm_num)]; norm_num
  · rw [unitRadius_lt_iff (by norm_num) (by norm_num)]; norm_num

/-- For the motifs of Theorem 1.1, `r n = 2 · Δ_st^{1/n}`. -/
theorem unitRadius_eq_centerDensity (n : ℕ) (hn : n = 10 ∨ n = 11 ∨ n = 12) :
    ∃ X : Fin 24 → Fin n → ℝ, centerDensity X = 1 / 24 ∧
      unitRadius n = 2 * centerDensity X ^ (1 / (n : ℝ)) := by
  obtain ⟨X, -, -, -, -, hΔ⟩ := theorem_1_1 n hn
  refine ⟨X, hΔ, ?_⟩
  rw [hΔ, unitRadius, one_div (24 : ℝ), Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]

end Stealth

end
