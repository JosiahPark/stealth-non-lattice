import StealthAudit.StealthRadius

/-!
# A3. General marked period: formula (3) in terms of a shape matrix `Q`

For a real matrix `Q` (positive definite where needed) this file defines

* `quadForm Q u = ∑ i j, uᵢ Q_ij u_j` for an integer frequency `u`;
* `gapQ X Q`: the infimum in `ℝ` of `quadForm Q u` over surviving frequencies `u` (nonzero, with
  `a_X(u) ≠ 0`); it is `0` by convention when nothing survives (`sInf ∅ = 0` in `ℝ`);
* `centerDensityQ X Q = (gapQ X Q / 4) ^ (n / 2) / N`, the right side of formula (3) of the paper with
  `Q = Q_B`.

and proves

* `exists_coercive`: a positive definite `Q` satisfies `c ‖w‖² ≤ quadForm Q w` for some `c > 0`
  (sup norm on `Fin n → ℝ`), for `n ≥ 1`;
* `isLeast_gapQ`, `exists_survives_quadForm_eq_gapQ`, `gapQ_le_of_survives`, `gapQ_pos`: for `Q` positive definite,
  `n ≥ 1` and `ι` nonempty, the infimum `gapQ X Q` is attained by a surviving frequency, is a lower
  bound for `quadForm Q` on survivors, and is positive (only finitely many integer vectors lie below
  any level of `quadForm Q`);
* `quadForm_one`, `gapQ_one`, `centerDensityQ_one`: with `Q = 1` (the cube `2ℤⁿ`),
  `quadForm 1 u = ‖u‖²`, `gapQ X 1 = gapSq X` and `centerDensityQ X 1 = centerDensity X`.

What this file does NOT prove: the derivation of (3) from a period matrix `B`. For a period lattice
`B(2ℤⁿ)` with `|det B|` normalizing the density, the paper sets `Q_B = |det B|^{2/n} B⁻¹ B⁻ᵀ`, notes
that the density of `B(X + 2ℤⁿ)` is `N / (2ⁿ |det B|)`, and that the dual-lattice point of `B(X + 2ℤⁿ)`
paired with `u` has squared length `uᵀ B⁻¹ B⁻ᵀ u / 4`, so that `Δ_st` of the linear image is
`centerDensityQ X Q_B`. That is a statement about the linear image of the periodic set and its dual
lattice, neither of which is defined in this library; it is recorded here as a remark only.
Nothing here uses that `Q` is symmetric; positive definiteness is `Matrix.PosDef`, which includes it.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The quadratic form `wᵀ Q w = ∑ i j, wᵢ Q_ij w_j` on real vectors. -/
def quadFormR (Q : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : ℝ := ∑ i, ∑ j, w i * Q i j * w j

/-- The quadratic form `uᵀ Q u` at an integer frequency `u`. -/
def quadForm (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℤ) : ℝ :=
  ∑ i, ∑ j, (u i : ℝ) * Q i j * (u j : ℝ)

/-- `4 K(P)²` for the marked period of shape `Q`: the infimum of `uᵀ Q u` over surviving
frequencies (`0` if none survives). -/
def gapQ (X : ι → Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin n → ℤ, Survives X u ∧ quadForm Q u = r}

/-- The right side of formula (3): `(gapQ X Q / 4) ^ (n / 2) / N`. -/
def centerDensityQ (X : ι → Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (gapQ X Q / 4) ^ ((n : ℝ) / 2) / (Fintype.card ι : ℝ)

theorem quadForm_eq_quadFormR (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℤ) :
    quadForm Q u = quadFormR Q (fun i => (u i : ℝ)) := rfl

theorem quadFormR_smul (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (w : Fin n → ℝ) :
    quadFormR Q (a • w) = a ^ 2 * quadFormR Q w := by
  unfold quadFormR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem quadFormR_zero (Q : Matrix (Fin n) (Fin n) ℝ) : quadFormR Q 0 = 0 := by
  simp [quadFormR]

theorem continuous_quadFormR (Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadFormR Q) := by
  unfold quadFormR
  fun_prop

/-- For a positive definite `Q`, `quadFormR Q` is positive away from `0`. -/
theorem quadFormR_pos {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) :
    0 < quadFormR Q w := by
  have h := hQ.dotProduct_mulVec_pos hw
  have : dotProduct (star w) (Q.mulVec w) = quadFormR Q w := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, quadFormR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [this] at h

/-- Coercivity: a positive definite form is bounded below by `c ‖w‖²` with `c > 0`
(sup norm on `Fin n → ℝ`). -/
theorem exists_coercive {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin n → ℝ, c * ‖w‖ ^ 2 ≤ quadFormR Q w := by
  have : NeZero n := ⟨hn.ne'⟩
  have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨v₀, hv₀, hmin⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne (continuous_quadFormR Q).continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    rintro rfl
    simp at hv₀
  refine ⟨quadFormR Q v₀, quadFormR_pos hQ hv₀ne, fun w => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp [quadFormR_zero]
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hv : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
  have h1 := hmin hv
  calc quadFormR Q v₀ * ‖w‖ ^ 2 ≤ quadFormR Q (‖w‖⁻¹ • w) * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = quadFormR Q w := by
        rw [quadFormR_smul]
        field_simp

/-- The set of integer frequencies with all coordinates in `[-M, M]`. -/
private def box (M : ℤ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-M) M

/-- For `Q` positive definite, `n ≥ 1` and `ι` nonempty, some surviving frequency minimizes
`quadForm Q` over all surviving frequencies. -/
theorem exists_survives_isMin [Nonempty ι] {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef)
    (hn : 0 < n) (X : ι → Fin n → ℝ) :
    ∃ u, Survives X u ∧ ∀ v, Survives X v → quadForm Q u ≤ quadForm Q v := by
  classical
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hQ hn
  obtain ⟨u₀, hu₀⟩ := exists_survives hn X
  set C := quadForm Q u₀ with hC
  set M : ℤ := ⌈C / c⌉ + 1 with hM
  -- every frequency with `quadForm Q v ≤ C` lies in the box of half-width `M`
  have hbox : ∀ v : Fin n → ℤ, quadForm Q v ≤ C → v ∈ box M := by
    intro v hv
    simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 : c * ‖(fun j => (v j : ℝ))‖ ^ 2 ≤ C := (hcoer _).trans hv
    have h2 : |(v i : ℝ)| ≤ ‖(fun j => (v j : ℝ))‖ := by
      have := norm_le_pi_norm (fun j => (v j : ℝ)) i
      simpa [Real.norm_eq_abs] using this
    have h3 : (v i : ℝ) ^ 2 ≤ C / c := by
      rw [le_div_iff₀ hc]
      have : |(v i : ℝ)| ^ 2 ≤ ‖(fun j => (v j : ℝ))‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
      rw [sq_abs] at this
      nlinarith
    have h4 : |(v i : ℝ)| ≤ (v i : ℝ) ^ 2 + 1 := by
      rcases le_or_gt |(v i : ℝ)| 1 with h | h
      · nlinarith [sq_nonneg (v i : ℝ)]
      · have : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by nlinarith
        rw [sq_abs] at this
        linarith
    have h5 : |(v i : ℝ)| ≤ (M : ℝ) := by
      rw [hM]
      push_cast
      linarith [Int.le_ceil (C / c)]
    have h6 : |v i| ≤ M := by exact_mod_cast h5
    exact abs_le.mp h6
  set F := (box M).filter fun v => Survives X v ∧ quadForm Q v ≤ C
  have hF : F.Nonempty := ⟨u₀, Finset.mem_filter.mpr ⟨hbox u₀ le_rfl, hu₀, le_rfl⟩⟩
  obtain ⟨u, huF, humin⟩ := F.exists_min_image (quadForm Q) hF
  have hu := (Finset.mem_filter.mp huF).2
  refine ⟨u, hu.1, fun v hv => ?_⟩
  by_cases hvC : quadForm Q v ≤ C
  · exact humin v (Finset.mem_filter.mpr ⟨hbox v hvC, hv, hvC⟩)
  · exact hu.2.trans (le_of_lt (not_le.mp hvC))

/-- `gapQ X Q` is the least value of `quadForm Q` over surviving frequencies. -/
theorem isLeast_gapQ [Nonempty ι] {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hn : 0 < n)
    (X : ι → Fin n → ℝ) :
    IsLeast {r : ℝ | ∃ u : Fin n → ℤ, Survives X u ∧ quadForm Q u = r} (gapQ X Q) := by
  obtain ⟨u, hu, hmin⟩ := exists_survives_isMin hQ hn X
  have hleast : IsLeast {r : ℝ | ∃ u : Fin n → ℤ, Survives X u ∧ quadForm Q u = r}
      (quadForm Q u) :=
    ⟨⟨u, hu, rfl⟩, by rintro r ⟨v, hv, rfl⟩; exact hmin v hv⟩
  unfold gapQ
  rwa [hleast.csInf_eq]

/-- The infimum `gapQ X Q` is attained by a surviving frequency. -/
theorem exists_survives_quadForm_eq_gapQ [Nonempty ι] {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) (hn : 0 < n) (X : ι → Fin n → ℝ) :
    ∃ u, Survives X u ∧ quadForm Q u = gapQ X Q :=
  (isLeast_gapQ hQ hn X).1

/-- Every surviving frequency has `quadForm Q v ≥ gapQ X Q`. -/
theorem gapQ_le_of_survives [Nonempty ι] {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef)
    (hn : 0 < n) {X : ι → Fin n → ℝ} {v : Fin n → ℤ} (hv : Survives X v) :
    gapQ X Q ≤ quadForm Q v :=
  (isLeast_gapQ hQ hn X).2 ⟨v, hv, rfl⟩

theorem gapQ_pos [Nonempty ι] {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hn : 0 < n)
    (X : ι → Fin n → ℝ) : 0 < gapQ X Q := by
  obtain ⟨u, hu, heq⟩ := exists_survives_quadForm_eq_gapQ hQ hn X
  rw [← heq, quadForm_eq_quadFormR]
  refine quadFormR_pos hQ fun h => hu.1 ?_
  funext i
  have := congrFun h i
  simpa using this

/-- With `Q = 1` the quadratic form is the squared Euclidean norm. -/
theorem quadForm_one (u : Fin n → ℤ) : quadForm 1 u = (sqNorm u : ℝ) := by
  unfold quadForm sqNorm
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j _ hji
    simp [Matrix.one_apply_ne' hji]
  · simp

/-- For the cube `2ℤⁿ` (`Q = 1`), `gapQ` is `gapSq`. No hypothesis on `n` or `ι` is needed: both sides
are `0` when nothing survives. -/
theorem gapQ_one (X : ι → Fin n → ℝ) : gapQ X 1 = (gapSq X : ℝ) := by
  unfold gapQ gapSq
  set S := {s : ℕ | ∃ u : Fin n → ℤ, Survives X u ∧ sqNorm u = (s : ℤ)} with hS
  have hset : {r : ℝ | ∃ u : Fin n → ℤ, Survives X u ∧ quadForm 1 u = r} =
      (fun s : ℕ => (s : ℝ)) '' S := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_image, hS, quadForm_one]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(sqNorm u).toNat, ⟨u, hu, (Int.toNat_of_nonneg (sqNorm_nonneg u)).symm⟩, ?_⟩
      have := Int.toNat_of_nonneg (sqNorm_nonneg u)
      exact_mod_cast this
    · rintro ⟨s, ⟨u, hu, hs⟩, rfl⟩
      exact ⟨u, hu, by exact_mod_cast hs⟩
  rw [hset]
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Set.image_empty, Real.sInf_empty, Nat.sInf_empty, Nat.cast_zero]
  · have hleast : IsLeast ((fun s : ℕ => (s : ℝ)) '' S) ((sInf S : ℕ) : ℝ) := by
      refine ⟨⟨sInf S, Nat.sInf_mem hne, rfl⟩, ?_⟩
      rintro r ⟨s, hs, rfl⟩
      show ((sInf S : ℕ) : ℝ) ≤ (s : ℝ)
      exact_mod_cast Nat.sInf_le hs
    exact hleast.csInf_eq

/-- For the cube `2ℤⁿ` (`Q = 1`), the right side of (3) is the stealth center density (1). -/
theorem centerDensityQ_one (X : ι → Fin n → ℝ) : centerDensityQ X 1 = centerDensity X := by
  rw [centerDensity_eq, centerDensityQ, gapQ_one]
  congr 1
  unfold stealthRadius
  have hg : (0 : ℝ) ≤ (gapSq X : ℝ) / 4 := by positivity
  rw [show ((n : ℝ) / 2) = (1 / 2 : ℝ) * n by ring, Real.rpow_mul hg, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

end Stealth

end
