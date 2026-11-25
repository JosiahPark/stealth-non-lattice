import StealthAudit.TraceFreeConstant
import StealthAudit.DetOneTrace

/-!
# F3c. Lemma 6.1 (strict reciprocal-Gram maximum)

Let `n ≥ 4` and let `V` be the test vectors of §6 (F1). Then

* every `v ∈ V` has `vᵀ v = 4` (`quadForm_one_testVector`), so `min_{v ∈ V} vᵀ Q v = 4` at `Q = 1`;
* there is `δ > 0` such that every real symmetric positive definite `Q` with `det Q = 1` and
  `0 < ‖Q − 1‖² < δ` (with `‖F‖² = ∑ᵢⱼ Fᵢⱼ²`) has some `v ∈ V` with `vᵀ Q v < 4`; that is, the minimum over
  `V` drops strictly below `4`.

Proof. Write `F = Q − 1`, `t = tr F` and `E = F − (t/n) 1`, which is symmetric and trace-free. For
`v ∈ V`, `vᵀ Q v = 4 + vᵀ E v + 4t/n`. By F3b some `v ∈ V` has `vᵀ E v ≤ −c ‖E‖`. By F3a,
`0 ≤ t ≤ 2‖F‖²` when `‖F‖² ≤ 1/4`, and `‖E‖² = ‖F‖² − t²/n ≥ ‖F‖²/2`; so `4t/n ≤ 2‖F‖² < c ‖E‖` once
`‖F‖² < c²/8`.

Proved here: `quadForm_add`, `quadForm_one_testVector`, `frobSq_sub_smul_one`, `lemma_6_1`.

What this file does NOT prove: Theorem 1.3 (items F4, F5).
-/

noncomputable section

open Finset Matrix

namespace Stealth

variable {n : ℕ}

theorem quadForm_add (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℤ) :
    quadForm (A + B) v = quadForm A v + quadForm B v := by
  simp only [quadForm, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Every test vector has squared length `4`. -/
theorem quadForm_one_testVector {v : Fin n → ℤ} (hv : v ∈ testVectors n) : quadForm 1 v = 4 := by
  classical
  rw [quadForm_one]
  rcases hv with ⟨i, rfl⟩ | ⟨I, hcard, hI, hout⟩
  · simp [sqNorm, sq, Finset.sum_ite_eq']
  · have hsub : sqNorm v = ∑ j ∈ I, v j ^ 2 := by
      rw [sqNorm]
      exact (Finset.sum_subset (Finset.subset_univ I) (fun j _ hj => by simp [hout j hj])).symm
    have hone : ∑ j ∈ I, v j ^ 2 = ∑ j ∈ I, (1 : ℤ) :=
      Finset.sum_congr rfl fun j hj => by rcases hI j hj with h | h <;> rw [h] <;> norm_num
    rw [hsub, hone, Finset.sum_const, hcard]
    norm_num

theorem frobSq_sub_smul_one (F : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    frobSq (F - a • (1 : Matrix (Fin n) (Fin n) ℝ)) = frobSq F - 2 * a * F.trace + a ^ 2 * n := by
  classical
  simp only [frobSq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Matrix.trace, Matrix.diag]
  have h : ∀ i j : Fin n, (F i j - if i = j then a else 0) ^ 2 =
      F i j ^ 2 - 2 * a * (if i = j then F i j else 0) + (if i = j then a ^ 2 else 0) := by
    intro i j; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Lemma 6.1.** For `n ≥ 4`: every test vector has `vᵀ v = 4`, and there is `δ > 0` such that every
real symmetric positive definite `Q` with `det Q = 1` and `0 < ‖Q − 1‖² < δ` has a test vector with
`vᵀ Q v < 4`. -/
theorem lemma_6_1 (hn : 4 ≤ n) :
    (∀ v ∈ testVectors n, quadForm 1 v = 4) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef → Q.det = 1 →
        0 < frobSq (Q - 1) → frobSq (Q - 1) < δ → ∃ v ∈ testVectors n, quadForm Q v < 4 := by
  refine ⟨fun v hv => quadForm_one_testVector hv, ?_⟩
  obtain ⟨c, hc, hcE⟩ := exists_trace_free_constant hn
  refine ⟨min (1 / 4) (c ^ 2 / 8), by positivity, fun Q hQ hdet hpos hlt => ?_⟩
  have hlt1 : frobSq (Q - 1) < 1 / 4 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt2 : frobSq (Q - 1) < c ^ 2 / 8 := lt_of_lt_of_le hlt (min_le_right _ _)
  set F := Q - 1 with hF
  set s := frobSq F with hs
  set t := F.trace with ht
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set E := F - (t / n) • (1 : Matrix (Fin n) (Fin n) ℝ) with hE
  have hFsymm : ∀ i j, F i j = F j i := fun i j => by
    have := (hQ.1.sub isHermitian_one).apply j i
    simp only [star_trivial, Matrix.sub_apply] at this
    simp only [hF, Matrix.sub_apply]
    linarith
  have hEsymm : ∀ i j, E i j = E j i := fun i j => by
    simp only [hE, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hFsymm i j, eq_comm]
  have hEtr : E.trace = 0 := by
    rw [hE, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp
    ring
  obtain ⟨v, hv, hvE⟩ := hcE E hEsymm hEtr
  refine ⟨v, hv, ?_⟩
  -- `vᵀ Q v = 4 + vᵀ E v + 4 t / n`
  have hQdecomp : Q = 1 + E + (t / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hE, hF]; abel
  have hq : quadForm Q v = 4 + quadForm E v + t / n * 4 := by
    rw [hQdecomp, quadForm_add, quadForm_add, quadForm_smul, quadForm_one_testVector hv]
  -- the trace estimates
  have ht0 : 0 ≤ t := trace_sub_one_nonneg hQ hdet
  have ht2 : t ≤ 2 * s := trace_sub_one_le_two_frobSq hQ hdet hlt1.le
  have hfE : frobSq E = s - t ^ 2 / n := by
    rw [hE, frobSq_sub_smul_one]
    field_simp
    ring
  have hfE2 : s / 2 ≤ frobSq E := by
    rw [hfE]
    have : t ^ 2 / n ≤ t ^ 2 / 4 := div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) hnR
    nlinarith
  -- `4t/n ≤ 2s < c ‖E‖`
  have h4t : t / n * 4 ≤ 2 * s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    nlinarith
  have hcE' : 2 * s < c * Real.sqrt (frobSq E) := by
    have hs0 : 0 < s := hpos
    have hsq : (2 * s) ^ 2 < (c * Real.sqrt (frobSq E)) ^ 2 := by
      rw [show (c * Real.sqrt (frobSq E)) ^ 2 = c ^ 2 * frobSq E by
        rw [mul_pow, Real.sq_sqrt (by linarith)]]
      nlinarith [mul_le_mul_of_nonneg_left hfE2 (sq_nonneg c), mul_lt_mul_of_pos_right hlt2 hs0]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  linarith

end Stealth

end
