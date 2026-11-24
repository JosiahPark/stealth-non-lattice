import StealthAudit.RankPrinciple

/-!
# D2. Indicator frequencies

The frequencies used in §4–§5 of the paper (`0`, `eᵢ`, `eᵢ + eⱼ`) are indicator vectors
`ind S = ∑_{i ∈ S} eᵢ` of sets of coordinates. Proved here:

* `sqNorm_nonneg`: `0 ≤ ‖u‖²`;
* `sqNorm_ind`: `‖ind S‖² = |S|`;
* `sqNorm_ind_sub_ind`: `‖ind T - ind S‖² = |S \ T| + |T \ S|`;
* `ind_injective`, `ind_sub_ind_ne_zero`: distinct sets give distinct frequencies;
* `card_le_card_of_gapAtLeast_ind`: the rank principle (D1) for an injective family of sets
  `φ : κ → Finset (Fin n)` whose pairwise symmetric differences have fewer than `s` elements:
  if `4 K(P)² ≥ s` then `|κ| ≤ N`.

What this file does NOT prove: any specific bound on `N`; the families of sets are chosen in
`CardinalityBound.lean`.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-- `0 ≤ ‖u‖²`. -/
theorem sqNorm_nonneg (u : Fin n → ℤ) : 0 ≤ sqNorm u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `‖ind T - ind S‖² = |S \ T| + |T \ S|`. -/
theorem sqNorm_ind_sub_ind (S T : Finset (Fin n)) :
    sqNorm (ind T - ind S) = (((S \ T).card + (T \ S).card : ℕ) : ℤ) := by
  have h : ∀ i, (ind T i - ind S i) ^ 2
      = (if i ∈ S \ T then (1 : ℤ) else 0) + (if i ∈ T \ S then 1 else 0) := by
    intro i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  simp only [sqNorm, Pi.sub_apply, h, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  push_cast
  rfl

/-- `‖ind S‖² = |S|`. -/
theorem sqNorm_ind (S : Finset (Fin n)) : sqNorm (ind S) = (S.card : ℤ) := by
  have h : ∀ i, ind S i ^ 2 = (if i ∈ S then (1 : ℤ) else 0) := by
    intro i
    by_cases hS : i ∈ S <;> simp [hS]
  simp only [sqNorm, h, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Distinct sets of coordinates have distinct indicator frequencies. -/
theorem ind_injective : Function.Injective (ind : Finset (Fin n) → Fin n → ℤ) := by
  intro S T h
  ext i
  have hi := congrFun h i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

theorem ind_sub_ind_ne_zero {S T : Finset (Fin n)} (h : S ≠ T) : ind T - ind S ≠ 0 := fun h0 =>
  h (ind_injective (sub_eq_zero.mp h0)).symm

/-- The rank principle for indicator frequencies: an injective family of sets of coordinates
whose pairwise symmetric differences have fewer than `s` elements has at most `N` members when
`4 K(P)² ≥ s`. -/
theorem card_le_card_of_gapAtLeast_ind {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (X : ι → Fin n → ℝ) (s : ℤ) (hX : GapAtLeast X s) (φ : κ → Finset (Fin n))
    (hφ : Function.Injective φ)
    (hs : ∀ p q, p ≠ q → ((((φ p \ φ q).card + (φ q \ φ p).card : ℕ) : ℤ)) < s) :
    Fintype.card κ ≤ Fintype.card ι := by
  refine card_le_card_of_gapAtLeast X s hX (fun p => ind (φ p)) fun p q hpq => ⟨?_, ?_⟩
  · exact ind_sub_ind_ne_zero fun h => hpq (hφ h)
  · rw [sqNorm_ind_sub_ind]
    exact hs p q hpq

end Stealth

end
