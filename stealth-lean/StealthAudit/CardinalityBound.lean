import StealthAudit.Indicator

/-!
# D3. Cardinality bounds from the stealth gap (Theorem 1.2, first part; Lemma 4.1)

For a nonempty motif `X : ι → Fin n → ℝ` with marked period `2ℤⁿ`, `N = Fintype.card ι`, at
arbitrary real positions (repeated points allowed). Recall that `GapAtLeast X s` is `4 K(P)² ≥ s`.

* `two_le_card_of_gapAtLeast_two`: if `4 K² ≥ 2` and `n ≥ 1`, then `N ≥ 2` (frequencies `0, e₁`);
* `succ_le_card_of_gapAtLeast_three`: if `4 K² ≥ 3`, then `N ≥ n + 1` (frequencies `0, eᵢ`);
* `two_mul_le_card_of_gapAtLeast_four`: **Theorem 1.2, the bound.** If `K(P) ≥ 1`, then
  `N ≥ 2n` (the frequencies `B_j = {0, e_j} ∪ {e_i, e_i + e_j : i ≠ j}` of §4);
* `rank_obstruction`: **Lemma 4.1.** If `K(P) > 1`, then `N ≥ 1 + n + n(n-1)/2` (frequencies
  `0, eᵢ, eᵢ + eⱼ`).

The paper states Theorem 1.2 for `n ≥ 3`; the bound `N ≥ 2n` proved here holds for every `n`.

What this file does NOT prove: the equality case of Theorem 1.2 (that `N = 2n` forces an
antipodal Hadamard array) and its converse; and the statements are in terms of `GapAtLeast`, not
of `stealthRadius` (the translation between the two is roadmap item A2, `StealthRadius.lean`).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-! ### Symmetric differences of small sets -/

theorem card_sdiff_add_card_sdiff_le (S T : Finset (Fin n)) :
    (S \ T).card + (T \ S).card ≤ S.card + T.card :=
  Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
    (Finset.card_le_card Finset.sdiff_subset)

/-- Two sets that each have at most one element besides `j` differ in at most three places. -/
theorem card_sdiff_add_card_sdiff_le_three (j : Fin n) (S T : Finset (Fin n))
    (hS : (S.erase j).card ≤ 1) (hT : (T.erase j).card ≤ 1) :
    (S \ T).card + (T \ S).card ≤ 3 := by
  have hsub : (S \ T) ∪ (T \ S) ⊆ (S.erase j ∪ T.erase j) ∪ {j} := by
    intro x hx
    simp only [mem_union, mem_sdiff, mem_erase, mem_singleton] at hx ⊢
    by_cases hxj : x = j <;> tauto
  have hdisj : Disjoint (S \ T) (T \ S) := disjoint_sdiff_sdiff
  have h1 : ((S.erase j ∪ T.erase j) ∪ {j}).card ≤ (S.erase j ∪ T.erase j).card + 1 := by
    simpa using Finset.card_union_le (S.erase j ∪ T.erase j) {j}
  have h2 : (S.erase j ∪ T.erase j).card ≤ (S.erase j).card + (T.erase j).card :=
    Finset.card_union_le _ _
  have h3 : ((S \ T) ∪ (T \ S)).card ≤ ((S.erase j ∪ T.erase j) ∪ {j}).card :=
    Finset.card_le_card hsub
  rw [← Finset.card_union_of_disjoint hdisj]
  omega

/-! ### The frequencies `B_j` of §4 as sets of coordinates -/

/-- The sets of coordinates of `B_j = {0, e_j} ∪ {e_i, e_i + e_j : i ≠ j}`: the index `(i, false)`
gives `{i}` for `i ≠ j` and `∅` for `i = j`; the index `(i, true)` adds `j`. -/
def pivotSet (j : Fin n) (p : Fin n × Bool) : Finset (Fin n) :=
  if p.2 then insert j {p.1} else ({p.1} : Finset (Fin n)).erase j

theorem erase_pivotSet (j : Fin n) (p : Fin n × Bool) :
    (pivotSet j p).erase j = ({p.1} : Finset (Fin n)).erase j := by
  rcases p with ⟨i, c⟩
  cases c <;> simp [pivotSet]

theorem mem_pivotSet_self (j : Fin n) (p : Fin n × Bool) : j ∈ pivotSet j p ↔ p.2 = true := by
  rcases p with ⟨i, c⟩
  cases c <;> simp [pivotSet]

theorem card_erase_pivotSet_le (j : Fin n) (p : Fin n × Bool) :
    ((pivotSet j p).erase j).card ≤ 1 := by
  rw [erase_pivotSet]
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (by simp)

theorem pivotSet_injective (j : Fin n) : Function.Injective (pivotSet j) := by
  rintro ⟨i, c⟩ ⟨i', c'⟩ h
  have hc : c = c' := by
    have h1 := mem_pivotSet_self j (i, c)
    have h2 := mem_pivotSet_self j (i', c')
    rw [h] at h1
    cases c <;> cases c' <;> simp_all
  have he : ({i} : Finset (Fin n)).erase j = ({i'} : Finset (Fin n)).erase j := by
    rw [← erase_pivotSet j (i, c), ← erase_pivotSet j (i', c'), h]
  have hi : i = i' := by
    by_cases hij : i = j
    · by_contra hne
      have hmem : i' ∈ ({i'} : Finset (Fin n)).erase j := by
        simp only [mem_erase, mem_singleton, and_true]
        exact fun h' => hne (hij.trans h'.symm)
      rw [← he] at hmem
      simp only [mem_erase, mem_singleton] at hmem
      exact hne hmem.2.symm
    · have hmem : i ∈ ({i} : Finset (Fin n)).erase j := by simp [hij]
      rw [he] at hmem
      simp only [mem_erase, mem_singleton] at hmem
      exact hmem.2
  rw [hi, hc]

/-! ### The bounds -/

section Bounds

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- If `4 K(P)² ≥ 2` and `n ≥ 1`, then `N ≥ 2`. -/
theorem two_le_card_of_gapAtLeast_two (hn : 0 < n) (X : ι → Fin n → ℝ) (hX : GapAtLeast X 2) :
    2 ≤ Fintype.card ι := by
  have h := card_le_card_of_gapAtLeast_ind X 2 hX
    (fun c : Bool => if c then ({⟨0, hn⟩} : Finset (Fin n)) else ∅)
    (by intro c c' h; cases c <;> cases c' <;> simp_all)
    (by
      intro p q hpq
      cases p <;> cases q <;> simp_all)
  simpa using h

/-- The sets of coordinates of the frequencies `0, e₁, …, eₙ`. -/
def optSet (o : Option (Fin n)) : Finset (Fin n) := o.elim ∅ fun i => {i}

theorem card_optSet_le (o : Option (Fin n)) : (optSet o).card ≤ 1 := by
  cases o <;> simp [optSet]

theorem optSet_injective : Function.Injective (optSet : Option (Fin n) → Finset (Fin n)) := by
  intro o o' h
  cases o <;> cases o' <;> simp_all [optSet]

/-- If `4 K(P)² ≥ 3`, then `N ≥ n + 1`. -/
theorem succ_le_card_of_gapAtLeast_three (X : ι → Fin n → ℝ) (hX : GapAtLeast X 3) :
    n + 1 ≤ Fintype.card ι := by
  have h := card_le_card_of_gapAtLeast_ind X 3 hX optSet optSet_injective (by
    intro p q _
    have hle := card_sdiff_add_card_sdiff_le (optSet p) (optSet q)
    have hp := card_optSet_le p
    have hq := card_optSet_le q
    have h2 : (optSet p \ optSet q).card + (optSet q \ optSet p).card ≤ 2 := by omega
    exact_mod_cast Nat.lt_succ_of_le h2)
  simpa using h

/-- **Theorem 1.2, the cardinality bound.** If `K(P) ≥ 1` for `P = X + 2ℤⁿ`, then `N ≥ 2n`. -/
theorem two_mul_le_card_of_gapAtLeast_four (X : ι → Fin n → ℝ) (hX : GapAtLeast X 4) :
    2 * n ≤ Fintype.card ι := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := card_le_card_of_gapAtLeast_ind X 4 hX (pivotSet ⟨0, hn⟩)
      (pivotSet_injective ⟨0, hn⟩) (by
        intro p q _
        have := card_sdiff_add_card_sdiff_le_three ⟨0, hn⟩ (pivotSet ⟨0, hn⟩ p)
          (pivotSet ⟨0, hn⟩ q) (card_erase_pivotSet_le _ p) (card_erase_pivotSet_le _ q)
        exact_mod_cast Nat.lt_succ_of_le this)
    simpa [mul_comm] using h

/-- **Lemma 4.1 (rank obstruction).** If `K(P) > 1` for `P = X + 2ℤⁿ`, then
`N ≥ D_n = 1 + n + n(n-1)/2`. -/
theorem rank_obstruction (X : ι → Fin n → ℝ) (hX : GapAtLeast X 5) :
    1 + n + n.choose 2 ≤ Fintype.card ι := by
  have h := card_le_card_of_gapAtLeast_ind X 5 hX
    (fun p : (k : Fin 3) × {S : Finset (Fin n) // S ∈ powersetCard (k : ℕ) univ} => (p.2 : Finset (Fin n)))
    (by
      rintro ⟨k, S, hS⟩ ⟨k', S', hS'⟩ h
      simp only at h
      subst h
      have hk : k = k' := by
        apply Fin.ext
        rw [← (Finset.mem_powersetCard.mp hS).2, ← (Finset.mem_powersetCard.mp hS').2]
      subst hk
      rfl)
    (by
      rintro ⟨k, S, hS⟩ ⟨k', S', hS'⟩ _
      have hle := card_sdiff_add_card_sdiff_le S S'
      have h1 : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have h2 : S'.card = k' := (Finset.mem_powersetCard.mp hS').2
      have hk := k.isLt
      have hk' := k'.isLt
      have : (S \ S').card + (S' \ S).card ≤ 4 := by omega
      exact_mod_cast Nat.lt_succ_of_le this)
  have hcard : Fintype.card ((k : Fin 3) × {S : Finset (Fin n) // S ∈ powersetCard (k : ℕ) univ})
      = 1 + n + n.choose 2 := by
    simp [Fintype.card_sigma, Fin.sum_univ_three]
  rw [hcard] at h
  exact h

end Bounds

end Stealth

end
