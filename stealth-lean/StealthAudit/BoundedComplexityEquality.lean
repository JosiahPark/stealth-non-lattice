import StealthAudit.BoundedComplexity
import StealthAudit.Theorem12

/-!
# E3. The equality statements of Theorem 5.1 and Corollary 5.2

Under the hypotheses of Theorem 5.1 (`n ≥ 5`, fewer than `D_n = 1 + n + n(n−1)/2` points at arbitrary
real positions), E1 shows `Δ_st ≤ 1/(2n)` with equality exactly when `K = 1` and `N = 2n`. With
Theorem 1.2 (D9) the equality case is identified:

* `centerDensity_eq_iff_antipodalHadamard`: **last sentence of Theorem 5.1.** `Δ_st = 1/(2n)` if and
  only if `X` is, up to a common translation, a relabelling and shifts by `2ℤⁿ`, the antipodal array of a
  Hadamard matrix of order `n` (in particular `N = 2n`);
* `centerDensity_eq_iff_antipodalHadamard_dim_twelve`: **equality in Corollary 5.2.** For `n = 12` and
  fewer than `79` points, `Δ_st = 1/24` exactly for translated 24-point antipodal Hadamard configurations
  of order 12.

`IsAntipodalHadamard X` names the right side of Theorem 1.2 (D9).

What this file does NOT prove: anything beyond the bounded-complexity hypothesis `N < D_n`.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- `X` is, up to a common translation, a relabelling and shifts by `2ℤⁿ`, the antipodal array of a
Hadamard matrix of order `n` (the right side of Theorem 1.2). -/
def IsAntipodalHadamard (X : ι → Fin n → ℝ) : Prop :=
  ∃ (t : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℤ), IsHadamard H ∧
    ∃ (e : Fin n × Bool ≃ ι) (z : Fin n × Bool → Fin n → ℤ),
      ∀ p i, X (e p) i = t i + antipodalMotif H id p i + 2 * (z p i : ℝ)

theorem card_of_isAntipodalHadamard {X : ι → Fin n → ℝ} (h : IsAntipodalHadamard X) :
    Fintype.card ι = 2 * n := by
  obtain ⟨-, -, -, e, -, -⟩ := h
  rw [← Fintype.card_congr e]
  simp [mul_comm]

/-- **Theorem 5.1, last sentence.** For `n ≥ 5` and `N < D_n`, `Δ_st = 1/(2n)` exactly for translated
antipodal Hadamard arrays of order `n`. -/
theorem centerDensity_eq_iff_antipodalHadamard [Nonempty ι] (hn : 5 ≤ n) (X : ι → Fin n → ℝ)
    (hN : Fintype.card ι < 1 + n + n.choose 2) :
    centerDensity X = 1 / (2 * (n : ℝ)) ↔ IsAntipodalHadamard X := by
  have hn0 : 0 < n := by omega
  rw [centerDensity_eq_iff_of_card_lt hn X hN]
  constructor
  · rintro ⟨hg, hc⟩
    have h4 : GapAtLeast X 4 := (gapAtLeast_iff_le_gapSq hn0 X 4).mpr (by rw [hg]; norm_num)
    exact (theorem_1_2 (by omega) hc).mp h4
  · intro h
    have hc := card_of_isAntipodalHadamard h
    have h4 : GapAtLeast X 4 := (theorem_1_2 (by omega) hc).mpr h
    have hle := gapSq_le_four_of_card_lt hn0 X hN
    have hge : (4 : ℤ) ≤ gapSq X := (gapAtLeast_iff_le_gapSq hn0 X 4).mp h4
    exact ⟨by omega, hc⟩

/-- **Corollary 5.2, equality.** For `n = 12` and fewer than `79` points, `Δ_st = 1/24` exactly for
translated 24-point antipodal Hadamard configurations of order 12. -/
theorem centerDensity_eq_iff_antipodalHadamard_dim_twelve [Nonempty ι] (X : ι → Fin 12 → ℝ)
    (hN : Fintype.card ι < 79) : centerDensity X = 1 / 24 ↔ IsAntipodalHadamard X := by
  have h := centerDensity_eq_iff_antipodalHadamard (n := 12) (by norm_num) X (by
    have : Nat.choose 12 2 = 66 := by decide
    omega)
  norm_num at h ⊢
  exact h

end Stealth

end
