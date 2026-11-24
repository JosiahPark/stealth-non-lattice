import StealthAudit.BinaryMotif

/-!
# B3. Marginals of a binary motif: strength `t` forces `2^t ∣ N`

For a binary motif `X` and a set `T` of coordinates, Fourier inversion on `T` counts the points
that vanish on `T`:

* `prod_one_add_sign`: for a `0/1` point `x`, `∏_{i ∈ T} (1 + (1 - 2xᵢ))` is `2^{|T|}` if `x`
  vanishes on `T` and `0` otherwise;
* `two_pow_mul_card_zeros`: `2^{|T|} · #{x ∈ X : x = 0 on T} = ∑_{S ⊆ T} charSum X S`;
* `two_pow_mul_card_zeros_of_hasStrength`: if `X` has strength `t` and `|T| ≤ t`, that number of
  points is `N / 2^{|T|}`, in the form `2^{|T|} · #{…} = N` (the all-zero pattern of "all
  `t`-coordinate projections are uniform");
* `two_pow_dvd_card_of_hasStrength`: if `X` has strength `t ≤ n`, then `2^t ∣ N`; for `t = 3`
  this is "uniformity on any three coordinates forces `8 ∣ |C|`" in the proof of Theorem 5.3;
* `charSum_ne_zero_of_card_mod_sixteen`: if `X` has strength three and `N ≡ 8 (mod 16)`, then
  every character sum of weight four is nonzero (the first step of the proof of Theorem 1.3).

What this file does NOT prove: uniformity for patterns other than the all-zero one (not needed
for the two divisibility statements), and nothing about non-binary motifs.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-- For a `0/1` point, `∏_{i ∈ T} (1 + (1 - 2xᵢ))` is `2^{|T|}` if `x` vanishes on `T`, else `0`. -/
theorem prod_one_add_sign (x : Fin n → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) (T : Finset (Fin n)) :
    ∏ i ∈ T, (1 + (1 - 2 * x i)) = 2 ^ T.card * (if ∀ i ∈ T, x i = 0 then (1 : ℝ) else 0) := by
  have h : ∀ i ∈ T, (1 + (1 - 2 * x i)) = 2 * (if x i = 0 then (1 : ℝ) else 0) := by
    intro i _
    rcases hx i with h | h <;> simp [h] <;> norm_num
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_zero,
    Finset.prod_const_one]
  congr

section Motif

variable {ι : Type*} [Fintype ι] {X : ι → Fin n → ℝ}

/-- Fourier inversion on `T`: `2^{|T|} · #{x ∈ X : x = 0 on T} = ∑_{S ⊆ T} charSum X S`. -/
theorem two_pow_mul_card_zeros (hX : IsBinary X) (T : Finset (Fin n)) :
    (2 : ℝ) ^ T.card * ((univ.filter fun k => ∀ i ∈ T, X k i = 0).card : ℝ)
      = ∑ S ∈ T.powerset, charSum X S := by
  have h1 : ∑ S ∈ T.powerset, charSum X S = ∑ k, ∏ i ∈ T, (1 + (1 - 2 * X k i)) := by
    simp only [charSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_one_add]
  rw [h1, Finset.sum_congr rfl fun k _ => prod_one_add_sign (X k) (hX k) T, ← Finset.mul_sum,
    Finset.sum_boole]

/-- If a binary motif has strength `t` and `|T| ≤ t`, exactly `N / 2^{|T|}` of its points vanish
on `T`. -/
theorem two_pow_mul_card_zeros_of_hasStrength (hX : IsBinary X) {t : ℕ} (hs : HasStrength X t)
    (T : Finset (Fin n)) (hT : T.card ≤ t) :
    2 ^ T.card * (univ.filter fun k => ∀ i ∈ T, X k i = 0).card = Fintype.card ι := by
  have h := two_pow_mul_card_zeros hX T
  have hsum : ∑ S ∈ T.powerset, charSum X S = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp [charSum]
    · intro S hS hne
      exact hs S (Finset.nonempty_iff_ne_empty.mpr hne)
        ((Finset.card_le_card (Finset.mem_powerset.mp hS)).trans hT)
    · intro h0
      exact absurd (Finset.empty_mem_powerset T) h0
  rw [hsum] at h
  exact_mod_cast h

/-- A binary motif of strength `t ≤ n` has a number of points divisible by `2^t`. -/
theorem two_pow_dvd_card_of_hasStrength (hX : IsBinary X) {t : ℕ} (hs : HasStrength X t)
    (ht : t ≤ n) : 2 ^ t ∣ Fintype.card ι := by
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := t)
    (by simpa using ht)
  have h := two_pow_mul_card_zeros_of_hasStrength hX hs T hT.le
  rw [hT] at h
  exact ⟨_, h.symm⟩

/-- For a binary motif of strength three with `N ≡ 8 (mod 16)`, every character sum of weight
four is nonzero. -/
theorem charSum_ne_zero_of_card_mod_sixteen (hX : IsBinary X) (hs : HasStrength X 3)
    (hN : Fintype.card ι % 16 = 8) (T : Finset (Fin n)) (hT : T.card = 4) : charSum X T ≠ 0 := by
  intro h0
  have h := two_pow_mul_card_zeros hX T
  have hsum : ∑ S ∈ T.powerset, charSum X S = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp [charSum]
    · intro S hS hne
      have hsub := Finset.mem_powerset.mp hS
      by_cases hST : S = T
      · rw [hST, h0]
      · have hlt : S.card < T.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hST⟩)
        exact hs S (Finset.nonempty_iff_ne_empty.mpr hne) (by omega)
    · intro h0'
      exact absurd (Finset.empty_mem_powerset T) h0'
  rw [hsum, hT] at h
  have h' : 2 ^ 4 * (univ.filter fun k => ∀ i ∈ T, X k i = 0).card = Fintype.card ι := by
    exact_mod_cast h
  omega

end Motif

end Stealth

end
