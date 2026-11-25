import StealthAudit.Basic

/-!
# F3a. The trace of `Q − 1` for `det Q = 1`

For a real symmetric positive definite matrix `Q` with `det Q = 1`, write `F = Q − 1` and
`‖F‖² = ∑ᵢⱼ Fᵢⱼ²` (`frobSq F`). Lemma 6.1 uses that `tr F = O(‖F‖²)`. Proved here, through the
eigenvalues `λᵢ > 0` of `Q` (`∏ λᵢ = 1`, so `∑ log λᵢ = 0`):

* `trace_mul_self_eq_sum_sq`: `tr(A²) = ∑ λᵢ²` for a real symmetric `A`;
* `frobSq_sub_one_eq`: `‖F‖² = ∑ (λᵢ − 1)²`;
* `trace_sub_one_eq`: `tr F = ∑ (λᵢ − 1)`;
* `trace_sub_one_nonneg`: `tr F ≥ 0` (from `log λ ≤ λ − 1`);
* `trace_sub_one_le_two_frobSq`: if `‖F‖² ≤ 1/4` then `tr F ≤ 2 ‖F‖²` (from `1 − 1/λ ≤ log λ`, the
  identity `λ − 1 = (1 − 1/λ) + (λ − 1)²/λ` and `λᵢ ≥ 1/2`).

What this file does NOT prove: the rest of Lemma 6.1 (items F3b, F3c).
-/

noncomputable section

open Finset Matrix

namespace Stealth

variable {n : ℕ}

/-- The squared Frobenius norm `∑ᵢⱼ Fᵢⱼ²`. -/
def frobSq (F : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, F i j ^ 2

/-- `tr(A²) = ∑ λᵢ²` for a real symmetric matrix. -/
theorem trace_mul_self_eq_sum_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  have h := hA.spectral_theorem
  set U := hA.eigenvectorUnitary
  set l := hA.eigenvalues
  clear_value U l
  subst h
  rw [← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

theorem frobSq_eq_trace_mul_self {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    frobSq F = (F * F).trace := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hF.apply j i
  simp only [star_trivial] at this
  rw [sq, this]

variable {Q : Matrix (Fin n) (Fin n) ℝ}

theorem trace_sub_one_eq (hQ : Q.PosDef) :
    (Q - 1).trace = ∑ i, (hQ.1.eigenvalues i - 1) := by
  rw [Matrix.trace_sub, hQ.1.trace_eq_sum_eigenvalues, Matrix.trace_one, Finset.sum_sub_distrib]
  simp

theorem frobSq_sub_one_eq (hQ : Q.PosDef) :
    frobSq (Q - 1) = ∑ i, (hQ.1.eigenvalues i - 1) ^ 2 := by
  have hF : (Q - 1).IsHermitian := hQ.1.sub isHermitian_one
  rw [frobSq_eq_trace_mul_self hF, sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, trace_mul_self_eq_sum_sq hQ.1,
    hQ.1.trace_eq_sum_eigenvalues, Matrix.trace_one]
  simp only [RCLike.ofReal_real_eq_id, id, Fintype.card_fin]
  have : ∑ i, (hQ.1.eigenvalues i - 1) ^ 2 =
      ∑ i, hQ.1.eigenvalues i ^ 2 - 2 * ∑ i, hQ.1.eigenvalues i + n := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, one_pow, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  rw [this]; ring

/-- `∑ log λᵢ = 0` when `det Q = 1`. -/
theorem sum_log_eigenvalues_eq_zero (hQ : Q.PosDef) (hdet : Q.det = 1) :
    ∑ i, Real.log (hQ.1.eigenvalues i) = 0 := by
  rw [← Real.log_prod (fun i _ => (hQ.eigenvalues_pos i).ne')]
  have h := hQ.1.det_eq_prod_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at h
  rw [← h, hdet, Real.log_one]

theorem trace_sub_one_nonneg (hQ : Q.PosDef) (hdet : Q.det = 1) : 0 ≤ (Q - 1).trace := by
  have h0 := sum_log_eigenvalues_eq_zero hQ hdet
  have h1 : ∑ i, Real.log (hQ.1.eigenvalues i) ≤ ∑ i, (hQ.1.eigenvalues i - 1) :=
    Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hQ.eigenvalues_pos i)
  rw [trace_sub_one_eq hQ]
  linarith

/-- `tr(Q − 1) ≤ 2 ‖Q − 1‖²` when `det Q = 1` and `‖Q − 1‖² ≤ 1/4`. -/
theorem trace_sub_one_le_two_frobSq (hQ : Q.PosDef) (hdet : Q.det = 1)
    (hsmall : frobSq (Q - 1) ≤ 1 / 4) : (Q - 1).trace ≤ 2 * frobSq (Q - 1) := by
  set l := hQ.1.eigenvalues with hl
  have hpos : ∀ i, 0 < l i := hQ.eigenvalues_pos
  rw [frobSq_sub_one_eq hQ] at hsmall ⊢
  rw [trace_sub_one_eq hQ]
  -- each eigenvalue is at least `1/2`
  have hhalf : ∀ i, 1 / 2 ≤ l i := fun i => by
    have h1 : (l i - 1) ^ 2 ≤ ∑ j, (l j - 1) ^ 2 :=
      Finset.single_le_sum (f := fun j => (l j - 1) ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
    nlinarith
  -- termwise: `λ − 1 ≤ log λ + 2 (λ − 1)²`
  have hterm : ∀ i, l i - 1 ≤ Real.log (l i) + 2 * (l i - 1) ^ 2 := fun i => by
    have hlog := Real.one_sub_inv_le_log_of_pos (hpos i)
    have hp := hpos i
    have hh := hhalf i
    have key : l i - 1 = (1 - (l i)⁻¹) + (l i - 1) ^ 2 / l i := by
      field_simp; ring
    have hdiv : (l i - 1) ^ 2 / l i ≤ 2 * (l i - 1) ^ 2 := by
      rw [div_le_iff₀ hp]
      nlinarith [sq_nonneg (l i - 1)]
    linarith
  calc ∑ i, (l i - 1) ≤ ∑ i, (Real.log (l i) + 2 * (l i - 1) ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * ∑ i, (l i - 1) ^ 2 := by
        rw [Finset.sum_add_distrib, sum_log_eigenvalues_eq_zero hQ hdet, zero_add, Finset.mul_sum]

end Stealth

end
