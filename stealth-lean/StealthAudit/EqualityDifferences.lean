import StealthAudit.RowOrthogonality
import StealthAudit.PivotFactorization
import StealthAudit.UnitRootSystem
import StealthAudit.BinaryMotif

/-!
# D7. Differences of points in the equality case of Theorem 1.2

Let `X` be a motif with `K(P) ≥ 1` (`GapAtLeast X 4`) and exactly `N = 2n` points, `n ≥ 3`. For every
pivot `j` the `2n` frequencies `B_j` of D3 have pairwise differences of squared norm at most `3`, so their
amplitudes vanish; there are exactly `N` of them, so by D4 the rows of the evaluation matrix are
orthogonal. By the pivot factorization (4) (D5), for two points `x = X k`, `y = X l` with `k ≠ l` and
`wᵢ = e^{πi (yᵢ − xᵢ)}`, this says `(1 + w_j)(1 + ∑_{i≠j} wᵢ) = 0` for every `j`, and D6 applies.

Proved here:

* `amp_pivot_sub_eq_zero`: the pivot family `B_j` is amplitude-orthogonal under `GapAtLeast X 4`;
* `pivot_relation`: `(1 + w_j)(1 + ∑_{i≠j} wᵢ) = 0` for `k ≠ l` and every `j`;
* `exists_int_of_exp_eq_one_or_neg_one`: `e^{πi d} = ±1` forces `d ∈ ℤ`;
* `equality_differences`: for `k ≠ l` every difference `X l i − X k i` is an integer `zᵢ`, and the
  number of odd `zᵢ` is `n` or `n/2` (`2 · #odd = n`);
* `distinctModPeriod_of_equality`: the points are pairwise distinct modulo `2ℤⁿ`;
* `even_of_equality`: `n` is even.

What this file does NOT prove: that the points form an antipodal Hadamard array (D8, D9).
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Under `K ≥ 1` the pivot family `B_j` has pairwise vanishing amplitude differences. -/
theorem amp_pivot_sub_eq_zero {X : ι → Fin n → ℝ} (hX : GapAtLeast X 4) (j : Fin n)
    (p q : Fin n × Bool) (hpq : p ≠ q) :
    amp X (ind (pivotSet j q) - ind (pivotSet j p)) = 0 := by
  refine hX _ (ind_sub_ind_ne_zero fun h => hpq (pivotSet_injective j h)) ?_
  rw [sqNorm_ind_sub_ind]
  have := card_sdiff_add_card_sdiff_le_three j (pivotSet j p) (pivotSet j q)
    (card_erase_pivotSet_le _ p) (card_erase_pivotSet_le _ q)
  exact_mod_cast Nat.lt_succ_of_le this

/-- The relation `(1 + w_j)(1 + ∑_{i ≠ j} wᵢ) = 0` in the equality case. -/
theorem pivot_relation {X : ι → Fin n → ℝ} (hX : GapAtLeast X 4)
    (hcard : Fintype.card ι = 2 * n) {k l : ι} (hkl : k ≠ l) (j : Fin n) :
    (1 + phase (ind {j}) (X l - X k)) *
      (1 + ∑ i ∈ univ.erase j, phase (ind {i}) (X l - X k)) = 0 := by
  classical
  have : Nonempty ι := ⟨k⟩
  have hc : Fintype.card (Fin n × Bool) = Fintype.card ι := by
    simp [hcard, mul_comm]
  have h := sum_conj_phase_mul_phase_of_card_eq X (fun p => ind (pivotSet j p)) hc
    (amp_pivot_sub_eq_zero hX j) k l
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' hkl), sum_pivot_eq_mul] at h
  exact h

/-- `phase (ind {i}) z = e^{πi zᵢ}`. -/
theorem phase_ind_singleton (i : Fin n) (z : Fin n → ℝ) :
    phase (ind {i}) z = Complex.exp (((Real.pi * z i : ℝ) : ℂ) * Complex.I) := by
  rw [phase, dot_ind, Finset.sum_singleton]

/-- `e^{πi d} = ±1` forces `d` to be an integer. -/
theorem exists_int_of_exp_eq_one_or_neg_one (d : ℝ)
    (h : Complex.exp (((Real.pi * d : ℝ) : ℂ) * Complex.I) = 1 ∨
      Complex.exp (((Real.pi * d : ℝ) : ℂ) * Complex.I) = -1) :
    ∃ m : ℤ, d = m := by
  -- reduce `-1` to `1` by shifting `d` by one
  have key : ∀ e : ℝ, Complex.exp (((Real.pi * e : ℝ) : ℂ) * Complex.I) = 1 → ∃ m : ℤ, e = 2 * m := by
    intro e he
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨m, ?_⟩
    have him := congrArg Complex.im hm
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.mul_re, sub_zero, Complex.re_ofNat, Complex.im_ofNat] at him
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have : Real.pi * e = Real.pi * (2 * m) := by linarith
    exact mul_left_cancel₀ hpi this
  rcases h with h | h
  · obtain ⟨m, hm⟩ := key d h
    exact ⟨2 * m, by rw [hm]; push_cast; ring⟩
  · have h1 : Complex.exp (((Real.pi * (d - 1) : ℝ) : ℂ) * Complex.I) = 1 := by
      have hsplit : (((Real.pi * d : ℝ) : ℂ) * Complex.I) =
          (((Real.pi * (d - 1) : ℝ) : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I] at h
      linear_combination -h
    obtain ⟨m, hm⟩ := key (d - 1) h1
    exact ⟨2 * m + 1, by push_cast; linarith⟩

/-- **Differences in the equality case.** If `K ≥ 1`, `N = 2n` and `n ≥ 3`, then for `k ≠ l` every
coordinate difference `X l i − X k i` is an integer `zᵢ`, and the number of odd `zᵢ` is `n` or `n/2`. -/
theorem equality_differences {X : ι → Fin n → ℝ} (hX : GapAtLeast X 4)
    (hcard : Fintype.card ι = 2 * n) (hn : 3 ≤ n) {k l : ι} (hkl : k ≠ l) :
    ∃ z : Fin n → ℤ, (∀ i, X l i - X k i = z i) ∧
      ((univ.filter fun i => z i % 2 = 1).card = n ∨
        2 * (univ.filter fun i => z i % 2 = 1).card = n) := by
  classical
  set w : Fin n → ℂ := fun i => phase (ind {i}) (X l - X k) with hw
  obtain ⟨hpm, hcase⟩ := unit_system hn w (fun i => norm_phase _ _)
    (fun j => pivot_relation hX hcard hkl j)
  have hwi : ∀ i, w i = Complex.exp (((Real.pi * (X l i - X k i) : ℝ) : ℂ) * Complex.I) :=
    fun i => by
      show phase (ind {i}) (X l - X k) = _
      rw [phase_ind_singleton]; rfl
  have hint : ∀ i, ∃ m : ℤ, X l i - X k i = m := fun i =>
    exists_int_of_exp_eq_one_or_neg_one _ (by rw [← hwi]; rcases hpm i with h | h <;> simp [h])
  choose z hz using hint
  refine ⟨z, hz, ?_⟩
  -- `w i = -1` exactly when `z i` is odd
  have hodd : ∀ i, w i = -1 ↔ z i % 2 = 1 := fun i => by
    rw [hwi, hz i, exp_pi_int]
    split_ifs with h
    · simp [h]
    · have hne : (1 : ℂ) ≠ -1 := by norm_num
      exact ⟨fun h' => absurd h' hne, fun h' => absurd h' h⟩
  have hF : (univ.filter fun i => z i % 2 = 1) = univ.filter fun i => w i = -1 := by
    ext i; simp [hodd i]
  rw [hF]
  rcases hcase with hall | hhalf
  · left
    rw [Finset.filter_true_of_mem (fun i _ => hall i), Finset.card_univ, Fintype.card_fin]
  · right
    have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i => w i = 1)
    have hnot : (univ.filter fun i => ¬ w i = 1) = univ.filter fun i => w i = -1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (hpm i).resolve_left h
      · intro h h1; rw [h1] at h; norm_num at h
    rw [hnot, Finset.card_univ, Fintype.card_fin] at hsplit
    omega

/-- In the equality case the points are pairwise distinct modulo `2ℤⁿ`. -/
theorem distinctModPeriod_of_equality {X : ι → Fin n → ℝ} (hX : GapAtLeast X 4)
    (hcard : Fintype.card ι = 2 * n) (hn : 3 ≤ n) : DistinctModPeriod X := by
  classical
  intro k l hkl ⟨z', hz'⟩
  obtain ⟨z, hz, hcount⟩ := equality_differences hX hcard hn (Ne.symm hkl)
  have hpos : 0 < (univ.filter fun i => z i % 2 = 1).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hzi : z i = 2 * z' i := by
    have : ((z i : ℤ) : ℝ) = ((2 * z' i : ℤ) : ℝ) := by rw [← hz i, hz' i]; push_cast; ring
    exact_mod_cast this
  have := (Finset.mem_filter.mp hi).2
  omega

/-- In the equality case `n` is even. -/
theorem even_of_equality {X : ι → Fin n → ℝ} (hX : GapAtLeast X 4)
    (hcard : Fintype.card ι = 2 * n) (hn : 3 ≤ n) : Even n := by
  classical
  let e : ι ≃ Fin (2 * n) := Fintype.equivFinOfCardEq hcard
  let a : ι := e.symm ⟨0, by omega⟩
  let b : ι := e.symm ⟨1, by omega⟩
  let c : ι := e.symm ⟨2, by omega⟩
  have hab : a ≠ b := fun h => by simpa [a, b] using congrArg (fun t => (e t).val) h
  have hbc : b ≠ c := fun h => by simpa [b, c] using congrArg (fun t => (e t).val) h
  have hac : a ≠ c := fun h => by simpa [a, c] using congrArg (fun t => (e t).val) h
  obtain ⟨z₁, hz₁, h₁⟩ := equality_differences hX hcard hn hab
  obtain ⟨z₂, hz₂, h₂⟩ := equality_differences hX hcard hn hbc
  obtain ⟨z₃, hz₃, h₃⟩ := equality_differences hX hcard hn hac
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · -- both pairs differ in every coordinate mod 2, so `a` and `c` agree mod 2
      exfalso
      have hall : ∀ (z : Fin n → ℤ), (univ.filter fun i => z i % 2 = 1).card = n →
          ∀ i, z i % 2 = 1 := fun z hz i => by
        have h := Finset.filter_card_eq (s := univ) (p := fun i => z i % 2 = 1)
          (by rw [hz, Finset.card_univ, Fintype.card_fin])
        exact h i (Finset.mem_univ i)
      have h3 : ∀ i, z₃ i = z₁ i + z₂ i := fun i => by
        have : ((z₃ i : ℤ) : ℝ) = ((z₁ i + z₂ i : ℤ) : ℝ) := by
          push_cast; rw [← hz₁, ← hz₂, ← hz₃]; ring
        exact_mod_cast this
      have hempty : (univ.filter fun i => z₃ i % 2 = 1) = ∅ := by
        refine Finset.filter_false_of_mem fun i _ => ?_
        have e1 := hall z₁ h₁ i
        have e2 := hall z₂ h₂ i
        rw [h3 i]
        omega
      rw [hempty, Finset.card_empty] at h₃
      omega
    · exact ⟨(univ.filter fun i => z₂ i % 2 = 1).card, by omega⟩
  · exact ⟨(univ.filter fun i => z₁ i % 2 = 1).card, by omega⟩

end Stealth

end
