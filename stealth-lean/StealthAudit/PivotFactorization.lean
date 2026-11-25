import StealthAudit.CardinalityBound

/-!
# D5. The pivot factorization (4)

For two points `x y` write `wᵢ = e^{πi (yᵢ − xᵢ)} = phase (ind {i}) (y − x)`. For the pivot family
`B_j = {0, e_j} ∪ {e_i, e_i + e_j : i ≠ j}` of D3 (the frequencies `ind (pivotSet j p)`,
`p : Fin n × Bool`) the sum of the products of evaluation entries factors as in formula (4) of §4:

  `∑_{b ∈ B_j} conj (e^{πi b·x}) e^{πi b·y} = (1 + w_j) (1 + ∑_{i ≠ j} wᵢ)`.

Proved here:

* `dot_ind`: `ind S · z = ∑_{i ∈ S} zᵢ`;
* `phase_ind_eq_prod`: `phase (ind S) z = ∏_{i ∈ S} phase (ind {i}) z`;
* `conj_phase_mul_phase_eq`: `conj (phase u x) * phase u y = phase u (y − x)`;
* `sum_pivot_eq_mul`: the factorization (4).

What this file does NOT prove: the consequences of (4) for the equality case (items D6, D7).
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace Stealth

variable {n : ℕ}

theorem dot_ind (S : Finset (Fin n)) (z : Fin n → ℝ) : dot (ind S) z = ∑ i ∈ S, z i := by
  simp [dot, ind, ite_mul, Finset.sum_ite_mem]

/-- The phase of an indicator frequency is the product of the coordinate phases. -/
theorem phase_ind_eq_prod (S : Finset (Fin n)) (z : Fin n → ℝ) :
    phase (ind S) z = ∏ i ∈ S, phase (ind {i}) z := by
  simp only [phase, dot_ind, Finset.sum_singleton]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `conj (e^{πi u·x}) e^{πi u·y} = e^{πi u·(y − x)}`. -/
theorem conj_phase_mul_phase_eq (u : Fin n → ℤ) (x y : Fin n → ℝ) :
    conj (phase u x) * phase u y = phase u (y - x) := by
  have h : phase u y = phase u x * phase u (y - x) := by
    rw [← phase_add_right, add_sub_cancel]
  rw [h, ← mul_assoc, Complex.conj_mul', norm_phase]
  simp

/-- **Formula (4).** With `wᵢ = e^{πi (yᵢ − xᵢ)}`, the sum over the pivot family `B_j` factors as
`(1 + w_j) (1 + ∑_{i ≠ j} wᵢ)`. -/
theorem sum_pivot_eq_mul (x y : Fin n → ℝ) (j : Fin n) :
    ∑ p : Fin n × Bool, conj (phase (ind (pivotSet j p)) x) * phase (ind (pivotSet j p)) y =
      (1 + phase (ind {j}) (y - x)) *
        (1 + ∑ i ∈ univ.erase j, phase (ind {i}) (y - x)) := by
  set w : Fin n → ℂ := fun i => phase (ind {i}) (y - x) with hw
  have key : ∀ p : Fin n × Bool,
      conj (phase (ind (pivotSet j p)) x) * phase (ind (pivotSet j p)) y =
        ∏ i ∈ pivotSet j p, w i := fun p => by
    rw [conj_phase_mul_phase_eq, phase_ind_eq_prod]
  simp only [key]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  -- each coordinate contributes `(1 + w j) * (if i = j then 1 else w i)`
  have hi : ∀ i : Fin n, (∏ k ∈ pivotSet j (i, true), w k) + ∏ k ∈ pivotSet j (i, false), w k =
      (1 + w j) * (if i = j then 1 else w i) := fun i => by
    by_cases hij : i = j
    · subst hij
      simp [pivotSet]
      ring
    · have hji : j ∉ ({i} : Finset (Fin n)) := by simpa using Ne.symm hij
      have herase : ({i} : Finset (Fin n)).erase j = {i} :=
        Finset.erase_eq_of_notMem hji
      simp only [pivotSet, ite_true, Bool.false_eq_true, ite_false, herase,
        Finset.prod_insert hji, Finset.prod_singleton, hij]
      ring
  simp only [hi, ← Finset.mul_sum]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  exact congrArg₂ (· + ·) (by simp)
    (Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi])

end Stealth

end
