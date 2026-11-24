import StealthAudit.StealthRadius

/-!
# B1. Binary motifs: the exact Fourier gap (Proposition 3.1, gap form)

For a binary motif `X` (every coordinate of every point is `0` or `1`), with `charSum`,
`HasStrength`, `oddSupp` of `Basic.lean`:

* `exp_pi_int`: `e^{πi u} = -1` for odd `u` and `1` for even `u`;
* `phase_of_binary`, `amp_of_isBinary`: `a_X(u) = ∑_x ∏_{i : uᵢ odd} (1 - 2xᵢ)`, so the amplitude
  depends only on `u mod 2` and is the binary character sum of the odd support of `u`;
* `card_oddSupp_le_sqNorm`, `four_le_sqNorm_of_oddSupp_eq_empty`, `oddSupp_ind`: the shortest
  integer vector in a nonzero parity class has squared length its Hamming weight, and a nonzero
  vector of the zero class has squared length at least `4` (the proof of Proposition 3.1);
* `gapAtLeast_iff_hasStrength`: for `t ≤ 3`, `4 K(P)² ≥ t + 1` exactly when all character sums
  of weights `1, …, t` vanish;
* `amp_two_mul_single`, `not_gapAtLeast_five`, `gapSq_le_four`: `a_X(2eᵢ) = N`, hence
  `4 K(P)² ≤ 4`, that is `K(P) ≤ 1`, for every binary motif;
* `le_gapSq_iff_hasStrength`, `gapSq_eq_four_iff_hasStrength`, `stealthRadius_eq_one_iff`,
  `centerDensity_of_hasStrength_three`: `K(P) = 1` exactly for strength three, and then
  `Δ_st(P) = 1 / N`.

Together these say `4 K(P)² = min {4, d⊥}` where `d⊥` is the least weight of a nonvanishing
character sum; the formula with `min` and the general value of `Δ_st` are not stated here as
single equations (roadmap item B2).

What this file does NOT prove: anything about motifs that are not binary, and no existence of a
strength-three array (that is section C).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-! ### Phases of binary points -/

/-- `e^{πi u} = (-1)^u`. -/
theorem exp_pi_int (u : ℤ) :
    Complex.exp (((Real.pi * (u : ℝ) : ℝ) : ℂ) * Complex.I) = if u % 2 = 1 then -1 else 1 := by
  have h : (((Real.pi * (u : ℝ) : ℝ) : ℂ) * Complex.I) = (u : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.emod_two_eq_zero_or_one u with h0 | h1
  · have hne : ¬ u % 2 = 1 := by omega
    simp only [hne, ↓reduceIte]
    exact Even.neg_one_zpow (Int.even_iff.mpr h0)
  · simp only [h1, ↓reduceIte]
    exact Odd.neg_one_zpow (Int.odd_iff.mpr h1)

theorem phase_eq_prod (u : Fin n → ℤ) (x : Fin n → ℝ) :
    phase u x = ∏ i, Complex.exp (((Real.pi * ((u i : ℝ) * x i) : ℝ) : ℂ) * Complex.I) := by
  rw [phase, ← Complex.exp_sum]
  congr 1
  simp only [dot]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The phase of a `0/1` point is the sign character of the odd support of the frequency. -/
theorem phase_of_binary (u : Fin n → ℤ) (x : Fin n → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    phase u x = ((∏ i ∈ oddSupp u, (1 - 2 * x i) : ℝ) : ℂ) := by
  rw [phase_eq_prod, oddSupp, Finset.prod_filter, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases hx i with h | h
  · simp [h]
  · rw [h, mul_one, exp_pi_int]
    split_ifs <;> norm_num

section Motif

variable {ι : Type*} [Fintype ι] {X : ι → Fin n → ℝ}

/-- For a binary motif, `a_X(u)` is the binary character sum of the odd support of `u`. -/
theorem amp_of_isBinary (hX : IsBinary X) (u : Fin n → ℤ) :
    amp X u = ((charSum X (oddSupp u) : ℝ) : ℂ) := by
  simp only [amp, charSum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [phase_of_binary u (X k) (hX k)]
  push_cast
  rfl

end Motif

/-! ### Shortest vectors in a parity class -/

/-- The number of odd coordinates of `u` is at most `‖u‖²`. -/
theorem card_oddSupp_le_sqNorm (u : Fin n → ℤ) : ((oddSupp u).card : ℤ) ≤ sqNorm u := by
  have h : ∀ i, (if u i % 2 = 1 then (1 : ℤ) else 0) ≤ u i ^ 2 := by
    intro i
    split_ifs with h
    · have hne : u i ≠ 0 := by
        intro h0
        rw [h0] at h
        norm_num at h
      have h1 := Int.one_le_abs hne
      nlinarith [sq_abs (u i), abs_nonneg (u i)]
    · positivity
  calc ((oddSupp u).card : ℤ) = ∑ i, (if u i % 2 = 1 then (1 : ℤ) else 0) := by
        simp [oddSupp]
    _ ≤ ∑ i, u i ^ 2 := Finset.sum_le_sum fun i _ => h i

/-- A nonzero integer vector with all coordinates even has squared norm at least `4`. -/
theorem four_le_sqNorm_of_oddSupp_eq_empty {u : Fin n → ℤ} (hu : u ≠ 0) (h : oddSupp u = ∅) :
    4 ≤ sqNorm u := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hne
    exact hu (funext fun i => by_contra fun hi => hne ⟨i, hi⟩)
  have heven : u i % 2 = 0 := by
    have hmem : i ∉ oddSupp u := by simp [h]
    rw [mem_oddSupp] at hmem
    omega
  have h4 : 4 ≤ u i ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, u i = 2 * k := ⟨u i / 2, by omega⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hi (by simpa using hk)
    have h1 := Int.one_le_abs hk0
    have h2 : 1 ≤ k ^ 2 := by nlinarith [sq_abs k, abs_nonneg k]
    rw [hk]
    nlinarith
  exact h4.trans
    (Finset.single_le_sum (f := fun i => u i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- The odd support of an indicator frequency is its set. -/
theorem oddSupp_ind (S : Finset (Fin n)) : oddSupp (ind S) = S := by
  ext i
  by_cases hS : i ∈ S <;> simp [hS]

theorem ind_ne_zero {S : Finset (Fin n)} (hS : S.Nonempty) : ind S ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  intro h0
  have := congrFun h0 i
  simp [hi] at this

/-! ### The gap of a binary motif -/

section Gap

variable {ι : Type*} [Fintype ι] {X : ι → Fin n → ℝ}

theorem hasStrength_of_gapAtLeast (hX : IsBinary X) (t : ℕ) (h : GapAtLeast X (t + 1)) :
    HasStrength X t := by
  intro S hS hcard
  have h0 := h (ind S) (ind_ne_zero hS) (by rw [sqNorm_ind]; omega)
  rw [amp_of_isBinary hX, oddSupp_ind] at h0
  exact_mod_cast h0

theorem gapAtLeast_of_hasStrength (hX : IsBinary X) (t : ℕ) (ht : t ≤ 3) (h : HasStrength X t) :
    GapAtLeast X (t + 1) := by
  intro u hu hlt
  rw [amp_of_isBinary hX]
  have hcard := card_oddSupp_le_sqNorm u
  have hne : (oddSupp u).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := four_le_sqNorm_of_oddSupp_eq_empty hu hempty
    omega
  rw [h (oddSupp u) hne (by omega)]
  simp

/-- **Proposition 3.1, gap form.** For a binary motif and `t ≤ 3`: `4 K(P)² ≥ t + 1` exactly when
all binary character sums of weights `1, …, t` vanish. -/
theorem gapAtLeast_iff_hasStrength (hX : IsBinary X) (t : ℕ) (ht : t ≤ 3) :
    GapAtLeast X (t + 1) ↔ HasStrength X t :=
  ⟨hasStrength_of_gapAtLeast hX t, gapAtLeast_of_hasStrength hX t ht⟩

/-- `a_X(2eᵢ) = N` for a binary motif. -/
theorem amp_two_mul_single (hX : IsBinary X) (i : Fin n) :
    amp X (fun j => if j = i then 2 else 0) = (Fintype.card ι : ℂ) := by
  rw [amp_of_isBinary hX]
  have h : oddSupp (fun j : Fin n => if j = i then (2 : ℤ) else 0) = ∅ := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  simp [charSum]

/-- A nonempty binary motif in dimension `n ≥ 1` never has `K(P) > 1`. -/
theorem not_gapAtLeast_five [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) : ¬ GapAtLeast X 5 := by
  intro h
  have h0 := h (fun j => if j = ⟨0, hn⟩ then 2 else 0)
    (by
      intro h0
      have := congrFun h0 ⟨0, hn⟩
      simp at this)
    (by
      have hs : sqNorm (fun j : Fin n => if j = ⟨0, hn⟩ then (2 : ℤ) else 0) = 4 := by
        simp [sqNorm, ite_pow]
      rw [hs]
      norm_num)
  rw [amp_two_mul_single hX] at h0
  exact (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℂ) ≠ 0) h0

/-- `4 K(P)² ≤ 4` for a nonempty binary motif in dimension `n ≥ 1`. -/
theorem gapSq_le_four [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) : gapSq X ≤ 4 := by
  by_contra h
  exact not_gapAtLeast_five hn hX ((gapAtLeast_iff_le_gapSq hn X 5).mpr (by omega))

/-- **Proposition 3.1, gap form**, in terms of `gapSq`: for `t ≤ 3`, `t + 1 ≤ 4 K(P)²` exactly
when the binary motif has strength `t`. -/
theorem le_gapSq_iff_hasStrength [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) (t : ℕ)
    (ht : t ≤ 3) : t + 1 ≤ gapSq X ↔ HasStrength X t := by
  rw [← gapAtLeast_iff_hasStrength hX t ht, gapAtLeast_iff_le_gapSq hn X]
  norm_cast

theorem gapSq_eq_four_iff_hasStrength [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    gapSq X = 4 ↔ HasStrength X 3 := by
  rw [← le_gapSq_iff_hasStrength hn hX 3 le_rfl]
  have := gapSq_le_four hn hX
  omega

/-- A nonempty binary motif in dimension `n ≥ 1` has `K(P) = 1` exactly when it has strength
three. -/
theorem stealthRadius_eq_one_iff [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    stealthRadius X = 1 ↔ HasStrength X 3 := by
  rw [← gapSq_eq_four_iff_hasStrength hn hX]
  have h4 := four_mul_stealthRadius_sq X
  have hnn : 0 ≤ stealthRadius X := by
    unfold stealthRadius
    positivity
  constructor
  · intro h
    rw [h] at h4
    have : (gapSq X : ℝ) = ((4 : ℕ) : ℝ) := by rw [← h4]; norm_num
    exact_mod_cast this
  · intro h
    rw [h] at h4
    have h1 : stealthRadius X ^ 2 = 1 := by
      have : (4 : ℝ) * stealthRadius X ^ 2 = 4 := by rw [h4]; norm_num
      linarith
    nlinarith [sq_nonneg (stealthRadius X - 1)]

/-- A binary motif of strength three has `Δ_st(P) = 1 / N` (dimension `n ≥ 1`). -/
theorem centerDensity_of_hasStrength_three [Nonempty ι] (hn : 0 < n) (hX : IsBinary X)
    (h : HasStrength X 3) : centerDensity X = 1 / (Fintype.card ι : ℝ) := by
  rw [centerDensity_eq, (stealthRadius_eq_one_iff hn hX).mpr h, one_pow]

end Gap

end Stealth

end
