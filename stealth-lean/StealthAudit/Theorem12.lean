import StealthAudit.EqualityDifferences
import StealthAudit.EqualityHadamard
import StealthAudit.AntipodalArray
import StealthAudit.Theorem11

/-!
# D9. Theorem 1.2 assembled

**Theorem 1.2 (equality case).** Let `n ≥ 3` and let `X : ι → Fin n → ℝ` be a motif with exactly
`N = 2n` points. Then `K(P) ≥ 1` for `P = X + 2ℤⁿ` (that is, `GapAtLeast X 4`) if and only if, up to a
common translation `t`, a relabelling `e : Fin n × Bool ≃ ι` and shifts by vectors of `2ℤⁿ`, `X` is the
antipodal array of a Hadamard matrix `H` of order `n`:

  `X (e p) i = tᵢ + antipodalMotif H id p i + 2 z_{p,i}`.

Together with `two_mul_le_card_of_gapAtLeast_four` (D3: `K ≥ 1` forces `N ≥ 2n`) this is Theorem 1.2 of
the paper, both the bound and the equality statement, for `n ≥ 3`.

Proof. Forward: fix a point `k₀`. By D7 every difference `X k − X k₀` is an integer vector `z_k`, and for
`k ≠ l` the vector `z_l − z_k = X l − X k` has `n` or `n/2` odd entries. So the binary motif
`Y k = z_k mod 2` has pairwise Hamming distances `n` or `n/2`, and D8 gives `H` and `e` with
`Y (e p) = antipodalMotif H id p`; finally `z = (z mod 2) + 2 ⌊z/2⌋`. Backward: C2 (an antipodal Hadamard
array has `K = 1`), invariance under relabelling (C5), shifts by `2ℤⁿ` and translation (A1).

Proved here: `theorem_1_2_forward`, `theorem_1_2_backward`, `theorem_1_2`.

What this file does NOT prove: anything about `n ≤ 2` (the paper states Theorem 1.2 for `n ≥ 3`).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The backward direction: a translated, relabelled, `2ℤⁿ`-shifted antipodal Hadamard array has
`K ≥ 1`. Holds for every `n`. -/
theorem theorem_1_2_backward {X : ι → Fin n → ℝ} (t : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : IsHadamard H) (e : Fin n × Bool ≃ ι) (z : Fin n × Bool → Fin n → ℤ)
    (hX : ∀ p i, X (e p) i = t i + antipodalMotif H id p i + 2 * (z p i : ℝ)) :
    GapAtLeast X 4 := by
  have hA : GapAtLeast (fun p i => antipodalMotif H id p i + 2 * (z p i : ℝ)) 4 := by
    intro u hu hs
    rw [amp_add_period]
    exact gapAtLeast_four_antipodalMotif hH Function.injective_id u hu hs
  have hXe : (X ∘ e) = fun p => (fun p i => antipodalMotif H id p i + 2 * (z p i : ℝ)) p + t := by
    funext p i
    simp only [Function.comp, Pi.add_apply, hX]
    ring
  have hB : GapAtLeast (X ∘ e) 4 := by
    rw [hXe, gapAtLeast_translate]; exact hA
  intro u hu hs
  rw [← amp_reindex e X]
  exact hB u hu hs

/-- The forward direction: `K ≥ 1` with `N = 2n`, `n ≥ 3`, forces a translated antipodal Hadamard array. -/
theorem theorem_1_2_forward {X : ι → Fin n → ℝ} (hn : 3 ≤ n) (hcard : Fintype.card ι = 2 * n)
    (hX : GapAtLeast X 4) :
    ∃ (t : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℤ), IsHadamard H ∧
      ∃ (e : Fin n × Bool ≃ ι) (z : Fin n × Bool → Fin n → ℤ),
        ∀ p i, X (e p) i = t i + antipodalMotif H id p i + 2 * (z p i : ℝ) := by
  classical
  have hne : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨k₀⟩ := hne
  -- integer differences from the base point
  have hdiff : ∀ k, ∃ w : Fin n → ℤ, ∀ i, X k i - X k₀ i = w i := fun k => by
    by_cases hk : k = k₀
    · exact ⟨0, fun i => by simp [hk]⟩
    · obtain ⟨w, hw, -⟩ := equality_differences hX hcard hn (Ne.symm hk)
      exact ⟨w, hw⟩
  choose w hw using hdiff
  -- the binary motif of parities
  let Y : ι → Fin n → ℝ := fun k i => ((w k i % 2 : ℤ) : ℝ)
  have hpar : ∀ (a : ℤ), a % 2 = 0 ∨ a % 2 = 1 := fun a => Int.emod_two_eq_zero_or_one a
  have hYb : IsBinary Y := fun k i => by
    rcases hpar (w k i) with h | h <;> simp [Y, h]
  have hYeq : ∀ k l i, Y k i = Y l i ↔ w k i % 2 = w l i % 2 := fun k l i => by
    simp only [Y]; exact_mod_cast Iff.rfl
  have hTD : TwoDistance Y := by
    intro k l hkl
    obtain ⟨v, hv, hcount⟩ := equality_differences hX hcard hn hkl
    have hvw : ∀ i, v i = w l i - w k i := fun i => by
      have : ((v i : ℤ) : ℝ) = ((w l i - w k i : ℤ) : ℝ) := by
        push_cast; rw [← hv i, ← hw l i, ← hw k i]; ring
      exact_mod_cast this
    have hset : (univ.filter fun i => Y k i ≠ Y l i) = univ.filter fun i => v i % 2 = 1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hYeq, hvw i]
      constructor <;> intro h <;> omega
    unfold hamming
    rw [hset]
    exact hcount
  obtain ⟨H, hH, e, he⟩ := equality_hadamard (by omega) hYb hcard hTD
  refine ⟨X k₀, H, hH, e, fun p i => w (e p) i / 2, fun p i => ?_⟩
  have h1 : X (e p) i = X k₀ i + (w (e p) i : ℝ) := by linarith [hw (e p) i]
  have h2 : Y (e p) i = antipodalMotif H id p i := congrFun (he p) i
  have h3 : (w (e p) i : ℝ) = Y (e p) i + 2 * ((w (e p) i / 2 : ℤ) : ℝ) := by
    simp only [Y]
    exact_mod_cast (by omega : w (e p) i = w (e p) i % 2 + 2 * (w (e p) i / 2))
  rw [h1, h3, h2]
  ring

/-- **Theorem 1.2 (equality case).** For `n ≥ 3` and a motif with exactly `2n` points, `K(P) ≥ 1` if and
only if the motif is a translated, relabelled, `2ℤⁿ`-shifted antipodal Hadamard array of order `n`. -/
theorem theorem_1_2 {X : ι → Fin n → ℝ} (hn : 3 ≤ n) (hcard : Fintype.card ι = 2 * n) :
    GapAtLeast X 4 ↔
      ∃ (t : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℤ), IsHadamard H ∧
        ∃ (e : Fin n × Bool ≃ ι) (z : Fin n × Bool → Fin n → ℤ),
          ∀ p i, X (e p) i = t i + antipodalMotif H id p i + 2 * (z p i : ℝ) := by
  constructor
  · exact theorem_1_2_forward hn hcard
  · rintro ⟨t, H, hH, e, z, hX⟩
    exact theorem_1_2_backward t H hH e z hX

end Stealth

end
