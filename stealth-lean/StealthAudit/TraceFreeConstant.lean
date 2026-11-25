import StealthAudit.TraceFreeSign
import StealthAudit.DetOneTrace

/-!
# F3b. A uniform constant in the sign lemma

For `n ≥ 4` there is `c > 0` such that every real symmetric trace-free matrix `E` has a test vector `v`
(F1) with

  `vᵀ E v ≤ −c ‖E‖`,   `‖E‖ = (∑ᵢⱼ Eᵢⱼ²)^{1/2}`.

Proof: the test vectors form a finite set `T` (all entries lie in `[−2, 2]`), so
`h E = min_{v ∈ T} vᵀ E v` is continuous. On the compact set `S` of symmetric trace-free `E` with
`‖E‖ = 1`, `h < 0` by F1, so `max_S h = −c < 0`. For general `E ≠ 0` apply this to `E / ‖E‖` and use
that `vᵀ E v` is linear in `E`.

Proved here: `testFinset`, `mem_testFinset`, `testFinset_nonempty`, `quadForm_smul`, `frobSq_smul`,
`frobSq_pos`, `exists_trace_free_constant`.

What this file does NOT prove: Lemma 6.1 itself (item F3c).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

open Classical in
/-- The test vectors as a finite set. -/
def testFinset (n : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc (-2 : ℤ) 2).filter (· ∈ testVectors n)

theorem mem_testFinset {v : Fin n → ℤ} : v ∈ testFinset n ↔ v ∈ testVectors n := by
  classical
  unfold testFinset
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hv i
  rcases hv with ⟨k, rfl⟩ | ⟨I, -, hI, hout⟩
  · by_cases h : i = k <;> simp [h]
  · by_cases hi : i ∈ I
    · rcases hI i hi with h | h <;> rw [h] <;> norm_num
    · rw [hout i hi]; norm_num

theorem testFinset_nonempty (hn : 1 ≤ n) : (testFinset n).Nonempty :=
  ⟨_, mem_testFinset.mpr (Or.inl ⟨⟨0, hn⟩, rfl⟩)⟩

theorem quadForm_smul (a : ℝ) (E : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℤ) :
    quadForm (a • E) v = a * quadForm E v := by
  simp only [quadForm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem frobSq_smul (a : ℝ) (E : Matrix (Fin n) (Fin n) ℝ) : frobSq (a • E) = a ^ 2 * frobSq E := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem entry_sq_le_frobSq (E : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : E i j ^ 2 ≤ frobSq E :=
  (Finset.single_le_sum (f := fun j => E i j ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, E i j ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (mem_univ i))

theorem frobSq_pos {E : Matrix (Fin n) (Fin n) ℝ} (hE : E ≠ 0) : 0 < frobSq E := by
  obtain ⟨i, j, hij⟩ : ∃ i j, E i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Matrix.ext h)
  exact lt_of_lt_of_le (by positivity) (entry_sq_le_frobSq E i j)

theorem continuous_quadForm_left (v : Fin n → ℤ) :
    Continuous fun E : Matrix (Fin n) (Fin n) ℝ => quadForm E v := by
  unfold quadForm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.mul (continuous_id.matrix_elem i j)).mul continuous_const

/-- **The constant `c_n`.** For `n ≥ 4` some `c > 0` makes `vᵀ E v ≤ −c ‖E‖` for a test vector `v`, for
every real symmetric trace-free `E`. -/
theorem exists_trace_free_constant (hn : 4 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ E : Matrix (Fin n) (Fin n) ℝ, (∀ i j, E i j = E j i) → E.trace = 0 →
      ∃ v ∈ testVectors n, quadForm E v ≤ -c * Real.sqrt (frobSq E) := by
  classical
  have hT := testFinset_nonempty (by omega : 1 ≤ n)
  let h : Matrix (Fin n) (Fin n) ℝ → ℝ := fun E => (testFinset n).inf' hT fun v => quadForm E v
  have hcont : Continuous h :=
    Continuous.finset_inf'_apply hT fun v _ => continuous_quadForm_left v
  let S : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {E | (∀ i j, E i j = E j i) ∧ E.trace = 0 ∧ frobSq E = 1}
  -- `S` is compact
  have hentry : ∀ i j, Continuous fun E : Matrix (Fin n) (Fin n) ℝ => E i j :=
    fun i j => continuous_id.matrix_elem i j
  have hSeq : S = (⋂ i, ⋂ j, {E : Matrix (Fin n) (Fin n) ℝ | E i j = E j i}) ∩
      ({E | E.trace = 0} ∩ {E | frobSq E = 1}) := by
    ext E; simp [S, Set.mem_iInter]
  have hclosed : IsClosed S := by
    rw [hSeq]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hentry i j) (hentry j i)) (IsClosed.inter ?_ ?_)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => hentry i i) continuous_const
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (hentry i j).pow 2) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : S ⊆ Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Set.Icc (-1 : ℝ) 1 := by
    intro E hE i _ j _
    have h1 := entry_sq_le_frobSq E i j
    rw [hE.2.2] at h1
    exact abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (by nlinarith))
  have hcomp : IsCompact S := hbox.of_isClosed_subset hclosed hsub
  -- `h < 0` on `S`
  have hneg : ∀ E ∈ S, h E < 0 := by
    intro E hE
    have hE0 : E ≠ 0 := fun h0 => by
      have := hE.2.2; rw [h0] at this; simp [frobSq] at this
    obtain ⟨v, hv, hq⟩ := exists_testVector_quadForm_neg hn E hE.1 hE.2.1 hE0
    exact lt_of_le_of_lt (Finset.inf'_le _ (mem_testFinset.mpr hv)) hq
  by_cases hS : S.Nonempty
  · obtain ⟨E₁, hE₁, hmax⟩ := hcomp.exists_isMaxOn hS hcont.continuousOn
    refine ⟨-h E₁, by linarith [hneg E₁ hE₁], fun E hsymm htr => ?_⟩
    rcases eq_or_ne E 0 with rfl | hE0
    · refine ⟨_, Or.inl ⟨⟨0, by omega⟩, rfl⟩, ?_⟩
      simp [quadForm, frobSq]
    set r := Real.sqrt (frobSq E) with hr
    have hpos := frobSq_pos hE0
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = frobSq E := Real.sq_sqrt hpos.le
    set E' := r⁻¹ • E with hE'
    have hE'S : E' ∈ S := by
      refine ⟨fun i j => by simp [hE', hsymm i j], by simp [hE', Matrix.trace_smul, htr], ?_⟩
      rw [hE', frobSq_smul, ← hr2]
      field_simp
    obtain ⟨v, hvT, hveq⟩ := Finset.exists_mem_eq_inf' hT fun v => quadForm E' v
    have hle : quadForm E' v ≤ h E₁ := by
      have := hmax hE'S
      simp only [Set.mem_ofPred_eq, h] at this
      rw [hveq] at this
      exact this
    have hEeq : E = r • E' := by
      rw [hE', smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    refine ⟨v, mem_testFinset.mp hvT, ?_⟩
    rw [hEeq, quadForm_smul]
    nlinarith [mul_le_mul_of_nonneg_left hle hrpos.le]
  · refine ⟨1, one_pos, fun E hsymm htr => ?_⟩
    rcases eq_or_ne E 0 with rfl | hE0
    · refine ⟨_, Or.inl ⟨⟨0, by omega⟩, rfl⟩, ?_⟩
      simp [quadForm, frobSq]
    exfalso
    apply hS
    have hpos := frobSq_pos hE0
    set r := Real.sqrt (frobSq E)
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = frobSq E := Real.sq_sqrt hpos.le
    refine ⟨r⁻¹ • E, fun i j => by simp [hsymm i j], by simp [Matrix.trace_smul, htr], ?_⟩
    rw [frobSq_smul, ← hr2]
    field_simp

end Stealth

end
