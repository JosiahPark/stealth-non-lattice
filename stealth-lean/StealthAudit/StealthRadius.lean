import StealthAudit.CardinalityBound

/-!
# A2. The stealth radius is well defined, and Theorem 1.2 / Lemma 4.1 in terms of it

`gapSq X` (that is, `4 K(P)²`) is defined in `Basic.lean` as an infimum over surviving
frequencies, with the value `0` if there is none. For a nonempty motif in dimension `n ≥ 1`
this file shows that a frequency always survives, so the infimum is a minimum, and it relates
`GapAtLeast`, `gapSq`, `stealthRadius` and `centerDensity`:

* `sqNorm_eq_zero_iff`, `sqNorm_pos`;
* `exists_survives`: some nonzero frequency has nonzero amplitude (the rank principle D1 applied
  to the `N + 1` frequencies `0, e₁, 2e₁, …, N e₁`);
* `exists_survives_sqNorm_eq_gapSq`, `gapSq_le_of_survives`, `gapSq_pos`: `gapSq X` is the least
  squared norm of a surviving frequency, and it is positive;
* `gapAtLeast_iff_le_gapSq`: `GapAtLeast X s ↔ s ≤ gapSq X`;
* `one_le_stealthRadius_iff`: `K(P) ≥ 1 ↔ GapAtLeast X 4`;
  `one_lt_stealthRadius_iff`: `K(P) > 1 ↔ GapAtLeast X 5`;
* `four_mul_stealthRadius_sq`: `4 K(P)² = gapSq X`;
* `centerDensity_eq`: `Δ_st(P) = K(P)ⁿ / N` for the cubic period `2ℤⁿ`;
* `gapSq_translate`, `stealthRadius_translate`, `centerDensity_translate`: invariance under a
  common translation of the motif;
* `two_mul_le_card_of_one_le_stealthRadius`: **Theorem 1.2, the bound**: `K(P) ≥ 1 → N ≥ 2n`;
* `rank_obstruction_of_one_lt_stealthRadius`: **Lemma 4.1**: `K(P) > 1 → N ≥ 1 + n + n(n-1)/2`.

What this file does NOT prove: that `stealthRadius` agrees with a radius defined through the
diffraction measure of `X + 2ℤⁿ` (formula (2) of the paper is the definition used here), and
nothing about the equality case of Theorem 1.2.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem sqNorm_eq_zero_iff (u : Fin n → ℤ) : sqNorm u = 0 ↔ u = 0 := by
  unfold sqNorm
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  constructor
  · intro h
    ext i
    simpa using h i (Finset.mem_univ i)
  · rintro rfl
    simp

theorem sqNorm_pos {u : Fin n → ℤ} (hu : u ≠ 0) : 0 < sqNorm u :=
  lt_of_le_of_ne (sqNorm_nonneg u) fun h => hu ((sqNorm_eq_zero_iff u).mp h.symm)

/-- For a nonempty motif in dimension `n ≥ 1`, some nonzero frequency has nonzero amplitude. -/
theorem exists_survives [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) : ∃ u, Survives X u := by
  by_contra hne
  have h0 : ∀ u : Fin n → ℤ, u ≠ 0 → amp X u = 0 := by
    intro u hu
    by_contra h
    exact hne ⟨u, hu, h⟩
  have hle := card_le_card_of_orthogonal X
    (fun (p : Fin (Fintype.card ι + 1)) (i : Fin n) => if i = ⟨0, hn⟩ then ((p : ℕ) : ℤ) else 0)
    (by
      intro p q hpq
      apply h0
      intro h
      have h1 := congrFun h ⟨0, hn⟩
      simp only [Pi.sub_apply, ite_true, Pi.zero_apply] at h1
      apply hpq
      apply Fin.ext
      omega)
  simp at hle

theorem gapSq_set_nonempty [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) :
    {s : ℕ | ∃ u : Fin n → ℤ, Survives X u ∧ sqNorm u = (s : ℤ)}.Nonempty := by
  obtain ⟨u, hu⟩ := exists_survives hn X
  exact ⟨(sqNorm u).toNat, u, hu, (Int.toNat_of_nonneg (sqNorm_nonneg u)).symm⟩

/-- The infimum defining `gapSq X` is attained by a surviving frequency. -/
theorem exists_survives_sqNorm_eq_gapSq [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) :
    ∃ u, Survives X u ∧ sqNorm u = (gapSq X : ℤ) :=
  Nat.sInf_mem (gapSq_set_nonempty hn X)

/-- Every surviving frequency has squared norm at least `gapSq X`. -/
theorem gapSq_le_of_survives {X : ι → Fin n → ℝ} {u : Fin n → ℤ} (hu : Survives X u) :
    (gapSq X : ℤ) ≤ sqNorm u := by
  have h1 : gapSq X ≤ (sqNorm u).toNat :=
    Nat.sInf_le ⟨u, hu, (Int.toNat_of_nonneg (sqNorm_nonneg u)).symm⟩
  have h2 := Int.toNat_of_nonneg (sqNorm_nonneg u)
  omega

/-- `GapAtLeast X s` says exactly that `s ≤ 4 K(P)²`. -/
theorem gapAtLeast_iff_le_gapSq [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) (s : ℤ) :
    GapAtLeast X s ↔ s ≤ (gapSq X : ℤ) := by
  constructor
  · intro h
    obtain ⟨u, hu, hs⟩ := exists_survives_sqNorm_eq_gapSq hn X
    by_contra hlt
    exact hu.2 (h u hu.1 (by rw [hs]; exact not_le.mp hlt))
  · intro h u hu hlt
    by_contra hamp
    have := gapSq_le_of_survives (X := X) ⟨hu, hamp⟩
    omega

theorem gapSq_pos [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) : 0 < gapSq X := by
  obtain ⟨u, hu, hs⟩ := exists_survives_sqNorm_eq_gapSq hn X
  have := sqNorm_pos hu.1
  omega

/-- `4 K(P)² = gapSq X`. -/
theorem four_mul_stealthRadius_sq (X : ι → Fin n → ℝ) :
    4 * stealthRadius X ^ 2 = (gapSq X : ℝ) := by
  unfold stealthRadius
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

/-- `K(P) ≥ 1` exactly when every nonzero frequency of squared norm less than `4` has zero
amplitude. -/
theorem one_le_stealthRadius_iff [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) :
    1 ≤ stealthRadius X ↔ GapAtLeast X 4 := by
  rw [gapAtLeast_iff_le_gapSq hn X]
  unfold stealthRadius
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), one_mul, Real.le_sqrt' (by norm_num)]
  constructor
  · intro h
    have h' : ((4 : ℕ) : ℝ) ≤ (gapSq X : ℝ) := by norm_num at h ⊢; exact h
    exact_mod_cast h'
  · intro h
    have h' : ((4 : ℕ) : ℝ) ≤ (gapSq X : ℝ) := by exact_mod_cast h
    norm_num at h' ⊢
    exact h'

/-- `K(P) > 1` exactly when every nonzero frequency of squared norm at most `4` has zero
amplitude. -/
theorem one_lt_stealthRadius_iff [Nonempty ι] (hn : 0 < n) (X : ι → Fin n → ℝ) :
    1 < stealthRadius X ↔ GapAtLeast X 5 := by
  rw [gapAtLeast_iff_le_gapSq hn X]
  unfold stealthRadius
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), one_mul, Real.lt_sqrt (by norm_num)]
  constructor
  · intro h
    have h' : ((4 : ℕ) : ℝ) < (gapSq X : ℝ) := by norm_num at h ⊢; exact h
    have h'' : 4 < gapSq X := by exact_mod_cast h'
    omega
  · intro h
    have h'' : 4 < gapSq X := by omega
    have h' : ((4 : ℕ) : ℝ) < (gapSq X : ℝ) := by exact_mod_cast h''
    norm_num at h' ⊢
    exact h'

/-- In dimension `0` there is no nonzero frequency, and the radius is `0` by convention. -/
theorem stealthRadius_dim_zero (X : ι → Fin 0 → ℝ) : stealthRadius X = 0 := by
  have h : gapSq X = 0 := by
    unfold gapSq
    have hempty : {s : ℕ | ∃ u : Fin 0 → ℤ, Survives X u ∧ sqNorm u = (s : ℤ)} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro s ⟨u, hu, -⟩
      exact hu.1 (Subsingleton.elim u 0)
    rw [hempty, Nat.sInf_empty]
  simp [stealthRadius, h]

/-- For the cubic period `2ℤⁿ`, `Δ_st(P) = K(P)ⁿ / N`. -/
theorem centerDensity_eq (X : ι → Fin n → ℝ) :
    centerDensity X = stealthRadius X ^ n / (Fintype.card ι : ℝ) := by
  unfold centerDensity density
  rw [div_pow]
  exact div_div_div_cancel_right₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)) _ _

/-- `4 K(P)²` does not change under a common translation of the motif. -/
theorem gapSq_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) :
    gapSq (fun k => X k + t) = gapSq X := by
  unfold gapSq
  simp only [survives_translate]

/-- `K(P)` does not change under a common translation of the motif. -/
theorem stealthRadius_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) :
    stealthRadius (fun k => X k + t) = stealthRadius X := by
  unfold stealthRadius
  rw [gapSq_translate]

/-- `Δ_st(P)` does not change under a common translation of the motif. -/
theorem centerDensity_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) :
    centerDensity (fun k => X k + t) = centerDensity X := by
  unfold centerDensity density
  rw [stealthRadius_translate]

/-- **Theorem 1.2, the cardinality bound**, in terms of the stealth radius: if `K(P) ≥ 1` for
`P = X + 2ℤⁿ` with `N` points in the cell (at arbitrary real positions), then `N ≥ 2n`. -/
theorem two_mul_le_card_of_one_le_stealthRadius [Nonempty ι] (X : ι → Fin n → ℝ)
    (h : 1 ≤ stealthRadius X) : 2 * n ≤ Fintype.card ι := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact two_mul_le_card_of_gapAtLeast_four X ((one_le_stealthRadius_iff hn X).mp h)

/-- **Lemma 4.1**, in terms of the stealth radius: if `K(P) > 1` for `P = X + 2ℤⁿ`, then
`N ≥ D_n = 1 + n + n(n-1)/2`. -/
theorem rank_obstruction_of_one_lt_stealthRadius [Nonempty ι] (X : ι → Fin n → ℝ)
    (h : 1 < stealthRadius X) : 1 + n + n.choose 2 ≤ Fintype.card ι := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [stealthRadius_dim_zero] at h
    norm_num at h
  · exact rank_obstruction X ((one_lt_stealthRadius_iff hn X).mp h)

end Stealth

end
