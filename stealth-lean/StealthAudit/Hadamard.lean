import StealthAudit.Basic

/-!
# C1. Hadamard matrices: columns and Hamming distances

For a Hadamard matrix `H` indexed by a finite type `α` (entries `±1`, `H Hᵀ = |α| I`; the
structure `IsHadamard` of `Basic.lean`):

* `IsHadamard.entry_mul_self`: `H i j * H i j = 1`;
* `IsHadamard.row_orthogonal`: `∑ₖ H i k * H j k = |α|` if `i = j` and `0` otherwise;
* `IsHadamard.col_orthogonal`, `IsHadamard.transpose_mul`: the same for columns, `Hᵀ H = |α| I`
  (the "Hadamard column orthogonality" used in the proof of Theorem 1.1);
* `IsHadamard.two_mul_card_ne`: two distinct rows differ in exactly half of the columns
  (`2 · #{k : H i k ≠ H j k} = |α|`), the Hamming-distance statement of the proof of Theorem 1.1;
* `IsHadamard.two_mul_card_eq`: and they agree in exactly half of the columns.

What this file does NOT prove: existence of a Hadamard matrix of any order (the order-12 Paley
matrix is `Paley12.lean`), and nothing about stealth.
-/

noncomputable section

open Finset Matrix

namespace Stealth

variable {α : Type*} [Fintype α] [DecidableEq α] {H : Matrix α α ℤ}

theorem IsHadamard.entry_mul_self (hH : IsHadamard H) (i j : α) : H i j * H i j = 1 := by
  rcases hH.entry i j with h | h <;> simp [h]

/-- Distinct rows of a Hadamard matrix are orthogonal, and each row has squared norm `|α|`. -/
theorem IsHadamard.row_orthogonal (hH : IsHadamard H) (i j : α) :
    ∑ k, H i k * H j k = if i = j then (Fintype.card α : ℤ) else 0 := by
  have h := congrFun (congrFun hH.mul_transpose i) j
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Distinct columns of a Hadamard matrix are orthogonal, and each column has squared norm
`|α|`. -/
theorem IsHadamard.col_orthogonal (hH : IsHadamard H) (a b : α) :
    ∑ r, H r a * H r b = if a = b then (Fintype.card α : ℤ) else 0 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact (IsEmpty.false a).elim
  have hm : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let A : Matrix α α ℚ := Matrix.of fun i j => (H i j : ℚ)
  have h1 : A * ((Fintype.card α : ℚ)⁻¹ • Aᵀ) = 1 := by
    ext i j
    have h := hH.row_orthogonal i j
    have hq : ∑ k, (H i k : ℚ) * (H j k : ℚ) = if i = j then (Fintype.card α : ℚ) else 0 := by
      exact_mod_cast h
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, Matrix.one_apply, A]
    have h2 : ∑ k, (H i k : ℚ) * ((Fintype.card α : ℚ)⁻¹ * (H j k : ℚ))
        = (Fintype.card α : ℚ)⁻¹ * ∑ k, (H i k : ℚ) * (H j k : ℚ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2, hq]
    by_cases hij : i = j
    · simp [hij, hm]
    · simp [hij]
  have h3 : ((Fintype.card α : ℚ)⁻¹ • Aᵀ) * A = 1 := mul_eq_one_comm.mp h1
  have h4 := congrFun (congrFun h3 a) b
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
    smul_eq_mul, Matrix.one_apply, A] at h4
  have h5 : ∑ r, (H r a : ℚ) * (H r b : ℚ) = if a = b then (Fintype.card α : ℚ) else 0 := by
    have h6 : ∑ r, (Fintype.card α : ℚ)⁻¹ * (H r a : ℚ) * (H r b : ℚ)
        = (Fintype.card α : ℚ)⁻¹ * ∑ r, (H r a : ℚ) * (H r b : ℚ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h6] at h4
    by_cases hab : a = b
    · simp only [hab, ite_true] at h4 ⊢
      exact ((inv_mul_eq_one₀ hm).mp h4).symm
    · simp only [hab, ite_false] at h4 ⊢
      rcases mul_eq_zero.mp h4 with h7 | h7
      · exact absurd (inv_eq_zero.mp h7) hm
      · exact h7
  exact_mod_cast h5

/-- `Hᵀ H = |α| I`. -/
theorem IsHadamard.transpose_mul (hH : IsHadamard H) :
    Hᵀ * H = (Fintype.card α : ℤ) • (1 : Matrix α α ℤ) := by
  ext a b
  have h := hH.col_orthogonal a b
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Two distinct rows of a Hadamard matrix differ in exactly half of the columns. -/
theorem IsHadamard.two_mul_card_ne (hH : IsHadamard H) {i j : α} (hij : i ≠ j) :
    2 * (univ.filter fun k => H i k ≠ H j k).card = Fintype.card α := by
  have hrow := hH.row_orthogonal i j
  simp only [hij, ite_false] at hrow
  have hpt : ∀ k, H i k * H j k = 1 - 2 * (if H i k ≠ H j k then (1 : ℤ) else 0) := by
    intro k
    rcases hH.entry i k with h1 | h1 <;> rcases hH.entry j k with h2 | h2 <;> simp [h1, h2]
  simp only [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole] at hrow
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hrow
  have : (2 * (univ.filter fun k => H i k ≠ H j k).card : ℤ) = (Fintype.card α : ℤ) := by
    linarith
  exact_mod_cast this

/-- Two distinct rows of a Hadamard matrix agree in exactly half of the columns. -/
theorem IsHadamard.two_mul_card_eq (hH : IsHadamard H) {i j : α} (hij : i ≠ j) :
    2 * (univ.filter fun k => H i k = H j k).card = Fintype.card α := by
  have h1 := hH.two_mul_card_ne hij
  have h2 : (univ.filter fun k => H i k = H j k).card + (univ.filter fun k => H i k ≠ H j k).card
      = Fintype.card α := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not (s := univ) (fun k => H i k = H j k)
  omega

end Stealth

end
