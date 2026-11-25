import StealthAudit.Basic

/-!
# D6. The unit-modulus system of §4

Let `n ≥ 3` and `w : Fin n → ℂ` with `‖wᵢ‖ = 1` for all `i`, and suppose that for every `j`

  `(1 + w_j) (1 + ∑_{i ≠ j} wᵢ) = 0`

(the right side of the pivot factorization (4), D5, vanishing for all pivots `j`). Then every `wᵢ` is
`1` or `−1`, and either all `wᵢ = −1` or exactly half of them equal `1`.

The proof is the one of §4: with `W = 1 + ∑ᵢ wᵢ` each `w_j` is `−1` or `W`. If `s ≥ 1` of them equal
`W ≠ −1` and the other `m = n − s` equal `−1`, then `(s − 1) W = m − 1`; `s = 1` forces `n = 2`; for
`s ≥ 2`, `W` is real of modulus one and not `−1`, so `W = 1` and `s = m`.

Proved here: `eq_neg_one_or_eq_of_unit_system` (each `w_j` is `−1` or `W`) and `unit_system` (the
conclusion above).

What this file does NOT prove: anything about point configurations; the application to the equality
case of Theorem 1.2 is item D7.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-- Each `w_j` is `−1` or `W = 1 + ∑ᵢ wᵢ`. -/
theorem eq_neg_one_or_eq_of_unit_system (w : Fin n → ℂ)
    (h : ∀ j, (1 + w j) * (1 + ∑ i ∈ univ.erase j, w i) = 0) (j : Fin n) :
    w j = -1 ∨ w j = 1 + ∑ i, w i := by
  have hsum : ∑ i, w i = w j + ∑ i ∈ univ.erase j, w i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rcases mul_eq_zero.mp (h j) with h1 | h1
  · left
    linear_combination h1
  · right
    rw [hsum]
    linear_combination -h1

/-- **The unit-modulus system.** For `n ≥ 3`, unit complex numbers `wᵢ` with
`(1 + w_j)(1 + ∑_{i ≠ j} wᵢ) = 0` for all `j` are all `±1`, and either all equal `−1` or exactly half
of them equal `1`. -/
theorem unit_system (hn : 3 ≤ n) (w : Fin n → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    (h : ∀ j, (1 + w j) * (1 + ∑ i ∈ univ.erase j, w i) = 0) :
    (∀ i, w i = 1 ∨ w i = -1) ∧
      ((∀ i, w i = -1) ∨ 2 * (univ.filter fun i => w i = 1).card = n) := by
  classical
  set W := 1 + ∑ i, w i with hWdef
  have hdich := eq_neg_one_or_eq_of_unit_system w h
  by_cases hall : ∀ i, w i = -1
  · exact ⟨fun i => Or.inr (hall i), Or.inl hall⟩
  push Not at hall
  obtain ⟨j₀, hj₀⟩ := hall
  have hWj₀ : w j₀ = W := (hdich j₀).resolve_left hj₀
  have hWne : W ≠ -1 := hWj₀ ▸ hj₀
  have hWnorm : ‖W‖ = 1 := hWj₀ ▸ hw j₀
  -- split the sum according to `w i = W` or `w i = -1`
  set F := univ.filter fun i => w i = W with hF
  set G := univ.filter fun i => ¬ w i = W with hG
  have hsplit : ∑ i, w i = (F.card : ℂ) * W - (G.card : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => w i = W)]
    have h1 : ∑ i ∈ F, w i = ∑ i ∈ F, W :=
      Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
    have h2 : ∑ i ∈ G, w i = ∑ i ∈ G, (-1 : ℂ) :=
      Finset.sum_congr rfl fun i hi =>
        (hdich i).resolve_right (Finset.mem_filter.mp hi).2
    rw [h1, h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hcard : F.card + G.card = n := by
    rw [hF, hG, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hFpos : 1 ≤ F.card := Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨mem_univ _, hWj₀⟩⟩
  -- the relation `(s - 1) W = m - 1`
  have hrel : ((F.card : ℂ) - 1) * W = (G.card : ℂ) - 1 := by
    have h0 : W = 1 + ∑ i, w i := hWdef
    rw [hsplit] at h0
    linear_combination -h0
  -- `s = 1` is impossible
  have hF2 : 2 ≤ F.card := by
    by_contra hlt
    have hF1 : F.card = 1 := by omega
    rw [hF1, Nat.cast_one, sub_self, zero_mul] at hrel
    have hG1 : (G.card : ℂ) = 1 := by linear_combination -hrel
    have : G.card = 1 := by exact_mod_cast hG1
    omega
  -- `W` is the real number `(m - 1)/(s - 1)`
  have hden : ((F.card : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ F.card := by exact_mod_cast hF2
    linarith
  set x : ℝ := ((G.card : ℝ) - 1) / ((F.card : ℝ) - 1) with hx
  have hWx : W = (x : ℂ) := by
    have hden' : ((F.card : ℂ) - 1) ≠ 0 := by exact_mod_cast hden
    rw [hx]
    push_cast
    field_simp
    linear_combination hrel
  have hxabs : |x| = 1 := by
    rw [hWx, Complex.norm_real, Real.norm_eq_abs] at hWnorm
    exact hWnorm
  have hx1 : x = 1 := by
    rcases abs_eq (zero_le_one) |>.mp hxabs with h1 | h1
    · exact h1
    · exact absurd (by rw [hWx, h1]; push_cast; ring) hWne
  have hW1 : W = 1 := by rw [hWx, hx1]; simp
  -- conclusions
  have hpm : ∀ i, w i = 1 ∨ w i = -1 := fun i => by
    rcases hdich i with h1 | h1
    · exact Or.inr h1
    · exact Or.inl (h1.trans hW1)
  refine ⟨hpm, Or.inr ?_⟩
  have hFeq : (univ.filter fun i => w i = 1) = F := by
    rw [hF, hW1]
  rw [hFeq]
  rw [hW1, mul_one] at hrel
  have hFG : (F.card : ℂ) = G.card := by linear_combination hrel
  have : F.card = G.card := by exact_mod_cast hFG
  omega

end Stealth

end
