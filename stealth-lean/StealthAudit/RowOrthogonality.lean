import StealthAudit.RankPrinciple

/-!
# D4. Row orthogonality in the equality case of the rank principle

In the rank principle (D1) the evaluation columns `V_p = (e^{πi (b p)·x})_{x ∈ X}` of a family of
frequencies with pairwise vanishing amplitudes are mutually orthogonal of squared norm `N`. When there
are exactly `N` frequencies the evaluation matrix is square, `N^{-1/2}` times it is unitary, and so its
ROWS are orthogonal too. This is the step of §4 of the paper that turns the equality `N = 2n` into
identities between pairs of points.

Proved here:

* `evalMatrix_mul_conjTranspose_of_card_eq`: with `|κ| = N` and pairwise vanishing amplitudes, the
  evaluation matrix, reindexed to a square matrix along a bijection `κ ≃ ι`, satisfies `M Mᴴ = N • 1`;
* `sum_conj_phase_mul_phase_of_card_eq`: in that case, for all points `k l`,
  `∑_p conj (e^{πi (b p)·X k}) e^{πi (b p)·X l} = N` if `k = l` and `0` otherwise.

What this file does NOT prove: any consequence for the equality case of Theorem 1.2 itself (items D5–D9).
-/

noncomputable section

open Finset Matrix
open scoped ComplexConjugate

namespace Stealth

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] in
/-- With exactly `N` frequencies whose pairwise differences have zero amplitude, the evaluation
matrix reindexed along `e : κ ≃ ι` satisfies `M Mᴴ = N • 1`. -/
theorem evalMatrix_mul_conjTranspose_of_card_eq [Nonempty ι] (X : ι → Fin n → ℝ)
    (b : κ → Fin n → ℤ) (e : κ ≃ ι) (h : ∀ p q, p ≠ q → amp X (b q - b p) = 0) :
    (evalMatrix X b).submatrix id e.symm * ((evalMatrix X b).submatrix id e.symm)ᴴ =
      (Fintype.card ι : ℂ) • (1 : Matrix ι ι ℂ) := by
  set M := (evalMatrix X b).submatrix id e.symm with hM
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- the columns of the square matrix are orthogonal
  have hcol : Mᴴ * M = (Fintype.card ι : ℂ) • (1 : Matrix ι ι ℂ) := by
    have h0 := conjTranspose_mul_evalMatrix_of_orthogonal X b h
    ext j j'
    have := congrFun (congrFun h0 (e.symm j)) (e.symm j')
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] at this ⊢
    rw [this]
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  have hleft : ((Fintype.card ι : ℂ)⁻¹ • Mᴴ) * M = 1 := by
    rw [Matrix.smul_mul, hcol, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hright : M * ((Fintype.card ι : ℂ)⁻¹ • Mᴴ) = 1 := mul_eq_one_comm.mp hleft
  rw [Matrix.mul_smul] at hright
  calc M * Mᴴ = (Fintype.card ι : ℂ) • ((Fintype.card ι : ℂ)⁻¹ • (M * Mᴴ)) := by
        rw [smul_smul, mul_inv_cancel₀ hN, one_smul]
    _ = (Fintype.card ι : ℂ) • (1 : Matrix ι ι ℂ) := by rw [hright]

/-- **Row orthogonality.** With exactly `N` frequencies whose pairwise differences have zero
amplitude, `∑_p conj (e^{πi (b p)·X k}) e^{πi (b p)·X l}` is `N` for `k = l` and `0` otherwise. -/
theorem sum_conj_phase_mul_phase_of_card_eq [Nonempty ι] (X : ι → Fin n → ℝ)
    (b : κ → Fin n → ℤ) (hcard : Fintype.card κ = Fintype.card ι)
    (h : ∀ p q, p ≠ q → amp X (b q - b p) = 0) (k l : ι) :
    ∑ p, conj (phase (b p) (X k)) * phase (b p) (X l) =
      if k = l then (Fintype.card ι : ℂ) else 0 := by
  let e : κ ≃ ι := Fintype.equivOfCardEq hcard
  have h1 := congrFun (congrFun (evalMatrix_mul_conjTranspose_of_card_eq X b e h) l) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id,
    evalMatrix_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, RCLike.star_def] at h1
  have h2 : ∑ p, conj (phase (b p) (X k)) * phase (b p) (X l) =
      ∑ j, phase (b (e.symm j)) (X l) * conj (phase (b (e.symm j)) (X k)) := by
    rw [← e.symm.sum_comp (fun p => conj (phase (b p) (X k)) * phase (b p) (X l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [h2, h1]
  by_cases hkl : k = l
  · simp [hkl]
  · simp [hkl, Ne.symm hkl]

end Stealth

end
