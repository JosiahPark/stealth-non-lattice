import Mathlib

/-!
# H4a. The index of an integer lattice is the absolute determinant

For an integer matrix `B` with `det B ≠ 0`, the subgroup `B ℤⁿ` of `ℤⁿ` has index `|det B|`.
This is the step "`|det A| = [L : Γ] / [L : ℤⁿ]`" of the proof of Proposition 7.1, in integer form
(H4c applies it to `B = 2A`). It is a direct consequence of Mathlib's `Submodule.natAbs_det_equiv`
(Smith normal form).

Proved here: `toLin'_injective_of_det_ne_zero`, `index_range_toLin'`, `index_range_two` (`2ℤⁿ` has
index `2ⁿ`).

What this file does NOT prove: the coset counting (H4b) or the integrality of the density (H4c).
-/

noncomputable section

namespace Stealth

variable {n : ℕ}

theorem toLin'_injective_of_det_ne_zero (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    Function.Injective (Matrix.toLin' B) := by
  intro x y hxy
  have h : B.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    have := hxy
    simp only [Matrix.toLin'_apply] at this
    rw [this, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hB h)

/-- **Index = determinant.** `[ℤⁿ : B ℤⁿ] = |det B|`. -/
theorem index_range_toLin' (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    (LinearMap.range (Matrix.toLin' B)).toAddSubgroup.index = B.det.natAbs := by
  set N := LinearMap.range (Matrix.toLin' B)
  let e : (Fin n → ℤ) ≃ₗ[ℤ] N := LinearEquiv.ofInjective _ (toLin'_injective_of_det_ne_zero B hB)
  have h := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → ℤ) →+ N) =
      Matrix.toLin' B :=
    LinearMap.ext fun x => rfl
  rw [hcomp, LinearMap.det_toLin'] at h
  rw [h]
  rfl

/-- `2ℤⁿ` has index `2ⁿ` in `ℤⁿ`. -/
theorem index_range_two :
    (LinearMap.range (Matrix.toLin' ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)))).toAddSubgroup.index =
      2 ^ n := by
  have hdet : ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).det = 2 ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [index_range_toLin' _ (by rw [hdet]; positivity), hdet, Int.natAbs_pow]
  rfl

end Stealth

end
