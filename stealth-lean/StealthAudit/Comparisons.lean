import StealthAudit.Basic

/-!
# G1. The numerical comparisons of §7

The table of §7 compares `Δ_st(P_n) = 1/24` with the center densities `1/(16√3)`,
`1/(2 · 3^{5/2})` and `1/27` of the duals of the best known lattice packings in dimensions 10,
11 and 12, and with the best known packing center densities `5/128`, `9/256`, `1/27` of Cohn's
table. Those six values are QUOTED INPUTS from the literature; nothing here derives them, and
nothing here is a statement about lattices or packings. Proved here, as arithmetic:

* `three_rpow_five_halves`: `3^{5/2} = 9√3`;
* `ratio_dim_ten`, `ratio_dim_eleven`, `ratio_dim_twelve`: the ratios of the table,
  `(1/24) / (1/(16√3)) = 2/√3`, `(1/24) / (1/(2 · 3^{5/2})) = 3^{5/2}/12`,
  `(1/24) / (1/27) = 9/8`;
* `lt_dim_ten`, `lt_dim_eleven`, `lt_dim_twelve`: `1/(16√3) < 1/24`, `1/(2 · 3^{5/2}) < 1/24`,
  `1/27 < 1/24`;
* `cohn_table_lt`: `5/128 < 1/24`, `9/256 < 1/24` and `1/27 < 1/24`.

What this file does NOT prove: that the quoted values are the center densities of any lattice,
the decimal values `1.4554…`, `1.4981…`, `1.5346…` of the unit-density radius `2 · 24^{-1/n}`
(roadmap item G2), and no comparison with all lattices (the paper claims none).
-/

noncomputable section

namespace Stealth

/-- `3^{5/2} = 9√3`. -/
theorem three_rpow_five_halves : (3 : ℝ) ^ ((5 : ℝ) / 2) = 9 * Real.sqrt 3 := by
  have h : ((5 : ℝ) / 2) = 2 + 1 / 2 := by norm_num
  rw [h, Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.sqrt_eq_rpow]
  norm_num

theorem sqrt_three_gt : (3 : ℝ) / 2 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- Dimension 10: `(1/24) / (1/(16√3)) = 2/√3`. -/
theorem ratio_dim_ten : ((1 : ℝ) / 24) / (1 / (16 * Real.sqrt 3)) = 2 / Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Dimension 11: `(1/24) / (1/(2 · 3^{5/2})) = 3^{5/2}/12`. -/
theorem ratio_dim_eleven :
    ((1 : ℝ) / 24) / (1 / (2 * (3 : ℝ) ^ ((5 : ℝ) / 2))) = (3 : ℝ) ^ ((5 : ℝ) / 2) / 12 := by
  rw [three_rpow_five_halves]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-- Dimension 12: `(1/24) / (1/27) = 9/8`. -/
theorem ratio_dim_twelve : ((1 : ℝ) / 24) / (1 / 27) = 9 / 8 := by norm_num

/-- Dimension 10: `1/(16√3) < 1/24`. -/
theorem lt_dim_ten : 1 / (16 * Real.sqrt 3) < (1 : ℝ) / 24 := by
  have h := sqrt_three_gt
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Dimension 11: `1/(2 · 3^{5/2}) < 1/24`. -/
theorem lt_dim_eleven : 1 / (2 * (3 : ℝ) ^ ((5 : ℝ) / 2)) < (1 : ℝ) / 24 := by
  have h := sqrt_three_gt
  rw [three_rpow_five_halves, div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Dimension 12: `1/27 < 1/24`. -/
theorem lt_dim_twelve : (1 : ℝ) / 27 < 1 / 24 := by norm_num

/-- The best known packing center densities of Cohn's table in dimensions 10, 11, 12 (quoted
values) are below `1/24`. -/
theorem cohn_table_lt : (5 : ℝ) / 128 < 1 / 24 ∧ (9 : ℝ) / 256 < 1 / 24 ∧ (1 : ℝ) / 27 < 1 / 24 := by
  norm_num

end Stealth

end
