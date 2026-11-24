import StealthAudit.AntipodalArray

/-!
# C4. The projected rows of an antipodal Hadamard array are distinct

For a Hadamard matrix `H` of order `m = |α|` and `n` distinct columns `c : Fin n → α` with
`m < 2n` (fewer than `m / 2` columns deleted), the `2m` points of `antipodalMotif H c` are
pairwise distinct modulo the period `2ℤⁿ`. This is the step "distinct nonantipodal sign rows of
`H` are at Hamming distance `m / 2` (the antipodal pairs have distance `m`); deletion of fewer
than `m / 2` columns cannot identify them" in the proof of Theorem 1.1. For `m = 12` it covers
`n = 7, …, 12`, in particular the paper's `n = 10, 11, 12`.

* `exists_col_mem_of_card_lt`: a set of more than `m - n` columns meets the `n` chosen columns;
* `eq_of_sub_eq_two_mul_int`: two `0/1` values that differ by an even integer are equal;
* `distinctModPeriod_antipodalMotif`: the statement above.

What this file does NOT prove: that the configuration is not a translate of a lattice (roadmap
item C6).
-/

noncomputable section

open Finset

namespace Stealth

variable {α : Type*} [Fintype α] [DecidableEq α] {H : Matrix α α ℤ} {n : ℕ}

/-- A set of columns with more than `|α| - n` elements contains one of `n` distinct chosen
columns. -/
theorem exists_col_mem_of_card_lt {c : Fin n → α} (hc : Function.Injective c) (D : Finset α)
    (h : Fintype.card α < D.card + n) : ∃ i, c i ∈ D := by
  by_contra hne
  have hdisj : Disjoint D (univ.image c) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk'
    exact hne ⟨i, hk⟩
  have hcard : (D ∪ univ.image c).card = D.card + n := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hc]
    simp
  have := Finset.card_le_univ (D ∪ univ.image c)
  omega

/-- Two real numbers in `{0, 1}` whose difference is an even integer are equal. -/
theorem eq_of_sub_eq_two_mul_int {x y : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (z : ℤ)
    (h : x - y = 2 * (z : ℝ)) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exfalso
    have h' : ((2 * z : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
    have h'' : 2 * z = -1 := by exact_mod_cast h'
    omega
  · exfalso
    have h' : ((2 * z : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
    have h'' : 2 * z = 1 := by exact_mod_cast h'
    omega
  · rfl

/-- The `2m` projected sign rows of `H` and `-H` are pairwise distinct modulo `2ℤⁿ` when fewer
than half of the `m` columns are deleted (`m < 2n`). -/
theorem distinctModPeriod_antipodalMotif (hH : IsHadamard H) {c : Fin n → α}
    (hc : Function.Injective c) (hmn : Fintype.card α < 2 * n) :
    DistinctModPeriod (antipodalMotif H c) := by
  rintro ⟨r, b⟩ ⟨r', b'⟩ hne ⟨z, hz⟩
  have hbin := isBinary_antipodalMotif hH c
  -- the two points agree in every coordinate, hence so do the signed entries
  have hsign : ∀ i, (if b then -1 else 1) * H r (c i) = (if b' then -1 else 1) * H r' (c i) := by
    intro i
    have heq := eq_of_sub_eq_two_mul_int (hbin (r, b) i) (hbin (r', b') i) (z i) (hz i)
    simp only [antipodalMotif] at heq
    have h2 : ((if b then (-1 : ℝ) else 1) * (H r (c i) : ℝ))
        = (if b' then (-1 : ℝ) else 1) * (H r' (c i) : ℝ) := by linarith
    have h3 : (((if b then -1 else 1) * H r (c i) : ℤ) : ℝ)
        = (((if b' then -1 else 1) * H r' (c i) : ℤ) : ℝ) := by
      push_cast
      convert h2 using 2
    exact_mod_cast h3
  have hn : 0 < n := by omega
  by_cases hr : r = r'
  · -- antipodal pair: every coordinate differs
    subst hr
    have hb : b ≠ b' := fun h => hne (by rw [h])
    have h0 := hsign ⟨0, hn⟩
    rcases hH.entry r (c ⟨0, hn⟩) with h | h <;> cases b <;> cases b' <;> simp_all
  · have hne' := hH.two_mul_card_ne hr
    have heq' := hH.two_mul_card_eq hr
    by_cases hb : b = b'
    · -- same sign: the rows would agree on all chosen columns
      subst hb
      obtain ⟨i, hi⟩ := exists_col_mem_of_card_lt hc (univ.filter fun k => H r k ≠ H r' k)
        (by omega)
      have hi' : H r (c i) ≠ H r' (c i) := by simpa using hi
      have h0 := hsign i
      cases b <;> simp_all
    · -- opposite signs: the rows would differ on all chosen columns
      obtain ⟨i, hi⟩ := exists_col_mem_of_card_lt hc (univ.filter fun k => H r k = H r' k)
        (by omega)
      have hi' : H r (c i) = H r' (c i) := by simpa using hi
      have h0 := hsign i
      rcases hH.entry r' (c i) with h | h <;> cases b <;> cases b' <;> simp_all

end Stealth

end
