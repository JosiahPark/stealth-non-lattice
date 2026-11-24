import StealthAudit.BinaryMotif
import StealthAudit.Hadamard

/-!
# C2. Antipodal Hadamard arrays have strength three and stealth radius one

For a Hadamard matrix `H` indexed by `α` (`m = |α|`) and `n` distinct columns `c : Fin n → α`,
`antipodalMotif H c` (see `Basic.lean`) is the binary array of the `2m` sign rows of `H` and
`-H`, projected onto the chosen columns. Proved here:

* `isBinary_antipodalMotif`: its points are `0/1` vectors;
* `charSum_antipodalMotif`: its character sum on a set `S` of coordinates is
  `(1 + (-1)^{|S|}) ∑_r ∏_{i ∈ S} H r (c i)` ("antipodal pairing kills odd weights");
* `hasStrength_three_antipodalMotif`: all character sums of weights `1, 2, 3` vanish (weight two
  by column orthogonality), so it is a strength-three orthogonal array in Fourier form;
* `gapAtLeast_four_antipodalMotif`, `stealthRadius_antipodalMotif`: `K(P) = 1`. With `n = m` and
  `c` a bijection this is the converse half of Theorem 1.2;
* `density_antipodalMotif`: `ρ(P) = 2m / 2ⁿ` (points counted with multiplicity);
* `centerDensity_antipodalMotif`: `Δ_st(P) = 1 / (2m)`.

What this file does NOT prove: that the `2m` projected rows are pairwise distinct modulo `2ℤⁿ`
(roadmap item C4; without it `ρ` counts points with multiplicity), that the configuration is not
a translate of a lattice (C6), or that a Hadamard matrix of order 12 exists (`Paley12.lean`).
-/

noncomputable section

open Finset

namespace Stealth

variable {α : Type*} [Fintype α] [DecidableEq α] {H : Matrix α α ℤ} {n : ℕ}

theorem isBinary_antipodalMotif (hH : IsHadamard H) (c : Fin n → α) :
    IsBinary (antipodalMotif H c) := by
  rintro ⟨r, b⟩ i
  rcases hH.entry r (c i) with h | h <;> cases b <;> simp [antipodalMotif, h]

omit [Fintype α] [DecidableEq α] in
theorem one_sub_two_mul_antipodalMotif (H : Matrix α α ℤ) (c : Fin n → α) (p : α × Bool)
    (i : Fin n) :
    1 - 2 * antipodalMotif H c p i = (if p.2 then -1 else 1) * (H p.1 (c i) : ℝ) := by
  simp only [antipodalMotif]
  ring

omit [DecidableEq α] in
/-- The character sums of an antipodal array: the two rows `±r` contribute
`(1 + (-1)^{|S|}) ∏_{i ∈ S} H r (c i)`. -/
theorem charSum_antipodalMotif (H : Matrix α α ℤ) (c : Fin n → α) (S : Finset (Fin n)) :
    charSum (antipodalMotif H c) S
      = (1 + (-1) ^ S.card) * ∑ r, ∏ i ∈ S, (H r (c i) : ℝ) := by
  simp only [charSum, one_sub_two_mul_antipodalMotif, Finset.prod_mul_distrib,
    Finset.prod_const, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_pow, one_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- An antipodal Hadamard array on distinct columns is a strength-three orthogonal array, in
Fourier form: its character sums of weights `1, 2, 3` vanish. -/
theorem hasStrength_three_antipodalMotif (hH : IsHadamard H) {c : Fin n → α}
    (hc : Function.Injective c) : HasStrength (antipodalMotif H c) 3 := by
  intro S hS hcard
  rw [charSum_antipodalMotif]
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  obtain h | h | h : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  · simp [h]
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hcol := hH.col_orthogonal (c a) (c b)
    have hne : c a ≠ c b := fun h' => hab (hc h')
    simp only [hne, ite_false] at hcol
    have h0 : ∑ r, ∏ i ∈ ({a, b} : Finset (Fin n)), (H r (c i) : ℝ) = 0 := by
      simp only [Finset.prod_pair hab]
      exact_mod_cast hcol
    rw [h0, mul_zero]
  · simp [h]
    norm_num

/-- `K(P) ≥ 1` for an antipodal Hadamard array on distinct columns. -/
theorem gapAtLeast_four_antipodalMotif (hH : IsHadamard H) {c : Fin n → α}
    (hc : Function.Injective c) : GapAtLeast (antipodalMotif H c) 4 :=
  gapAtLeast_of_hasStrength (isBinary_antipodalMotif hH c) 3 le_rfl
    (hasStrength_three_antipodalMotif hH hc)

/-- `K(P) = 1` for an antipodal Hadamard array on `n ≥ 1` distinct columns. -/
theorem stealthRadius_antipodalMotif [Nonempty α] (hn : 0 < n) (hH : IsHadamard H)
    {c : Fin n → α} (hc : Function.Injective c) : stealthRadius (antipodalMotif H c) = 1 :=
  (stealthRadius_eq_one_iff hn (isBinary_antipodalMotif hH c)).mpr
    (hasStrength_three_antipodalMotif hH hc)

omit [DecidableEq α] in
/-- `ρ(P) = 2m / 2ⁿ` for an antipodal array of a matrix of order `m` (with multiplicity). -/
theorem density_antipodalMotif (H : Matrix α α ℤ) (c : Fin n → α) :
    density (antipodalMotif H c) = 2 * (Fintype.card α : ℝ) / 2 ^ n := by
  simp [density, mul_comm]

/-- `Δ_st(P) = 1 / (2m)` for an antipodal Hadamard array of order `m` on `n ≥ 1` distinct
columns. -/
theorem centerDensity_antipodalMotif [Nonempty α] (hn : 0 < n) (hH : IsHadamard H)
    {c : Fin n → α} (hc : Function.Injective c) :
    centerDensity (antipodalMotif H c) = 1 / (2 * (Fintype.card α : ℝ)) := by
  rw [centerDensity_of_hasStrength_three hn (isBinary_antipodalMotif hH c)
    (hasStrength_three_antipodalMotif hH hc)]
  simp [mul_comm]

end Stealth

end
