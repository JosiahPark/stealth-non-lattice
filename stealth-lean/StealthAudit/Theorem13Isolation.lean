import StealthAudit.Theorem13
import StealthAudit.EqualityDifferences
import StealthAudit.BoundedComplexity

/-!
# F5b. Theorem 1.3, last sentence: local isolation for `n = 12`, `N = 24`

Let `C` be a binary motif of strength three with `N = 24` points in dimension `n = 12`. Then the equality
case of Theorem 1.3 is locally isolated: there are a neighbourhood `U` of `C` and `δ > 0` such that if
`X ∈ U`, `Q` is a period shape (symmetric positive definite, `det Q = 1`) with `‖Q − 1‖² < δ`, and
`centerDensityQ X Q = 1/24`, then `Q = 1` and `X` is a common translate of `C` (with the same labelling).

Proof. `Q ≠ 1` would give `Δ_st < 1/24` by F5a, so `Q = 1`. Then `Δ_st(X) = 1/24` with `24 < 79` gives
`K(X) = 1` (E1), and by D7 every difference `X l i − X k i` is an integer. The differences of `C` are
integers too (binary), and for `X` within `1/4` of `C` the two differences are within `1/2` of each
other, hence equal. So `X k − C k` does not depend on `k`.

This is stronger than the paper's "modulo translations, similarities and point relabelling": near `C` no
relabelling or shift by `2ℤ¹²` is needed. The paper's similarities are the period changes with
`Q_B = 1`.

Proved here: `int_diff_of_isBinary`, `eq_translate_of_close`, `theorem_1_3_isolation`.
-/

noncomputable section

open Finset Filter Topology

namespace Stealth

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem int_diff_of_isBinary {n : ℕ} {C : ι → Fin n → ℝ} (hC : IsBinary C) (k l : ι) (i : Fin n) :
    ∃ w : ℤ, C l i - C k i = w := by
  rcases hC l i with h1 | h1 <;> rcases hC k i with h2 | h2
  · exact ⟨0, by rw [h1, h2]; norm_num⟩
  · exact ⟨-1, by rw [h1, h2]; norm_num⟩
  · exact ⟨1, by rw [h1, h2]; norm_num⟩
  · exact ⟨0, by rw [h1, h2]; norm_num⟩

omit [Fintype ι] in
/-- Two integers within distance `< 1` are equal. -/
theorem eq_translate_of_close {x y c d : ℝ} {z w : ℤ} (hz : x - y = z) (hw : c - d = w)
    (hx : |x - c| < 1 / 4) (hy : |y - d| < 1 / 4) : x - y = c - d := by
  have h : |((z - w : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [← hz, ← hw]
    calc |x - y - (c - d)| = |(x - c) - (y - d)| := by ring_nf
      _ ≤ |x - c| + |y - d| := abs_sub _ _
      _ < 1 := by linarith
  have h' : |z - w| < 1 := by exact_mod_cast h
  have : z - w = 0 := Int.abs_lt_one_iff.mp h'
  rw [hz, hw]
  exact_mod_cast (by omega : z = w)

/-- **Theorem 1.3, last sentence.** For `n = 12` and `N = 24`, near `C` and near `Q = 1`, equality
`Δ_st = 1/24` forces `Q = 1` and `X = C + t` for a common translation `t`. -/
theorem theorem_1_3_isolation [Nonempty ι] {C : ι → Fin 12 → ℝ} (hC : IsBinary C)
    (hs : HasStrength C 3) (hcard : Fintype.card ι = 24) :
    ∃ U ∈ 𝓝 C, ∃ δ : ℝ, 0 < δ ∧ ∀ X ∈ U, ∀ Q : Matrix (Fin 12) (Fin 12) ℝ, Q.PosDef → Q.det = 1 →
      frobSq (Q - 1) < δ → centerDensityQ X Q = 1 / 24 →
        Q = 1 ∧ ∃ t : Fin 12 → ℝ, ∀ k, X k = C k + t := by
  obtain ⟨-, U, hU, δ, hδ, hloc⟩ := theorem_1_3 (n := 12) (by norm_num) hC hs (by rw [hcard])
  refine ⟨U ∩ Metric.ball C (1 / 4), Filter.inter_mem hU (Metric.ball_mem_nhds C (by norm_num)), δ, hδ,
    fun X hX Q hQ hdet hlt heq => ?_⟩
  have hcardR : (Fintype.card ι : ℝ) = 24 := by exact_mod_cast hcard
  -- `Q = 1`
  have hQ1 : Q = 1 := by
    by_contra hne
    have := (hloc X hX.1 Q hQ hdet hlt).2 hne
    rw [heq, hcardR] at this
    exact lt_irrefl _ this
  refine ⟨hQ1, ?_⟩
  subst hQ1
  -- `K(X) = 1`
  rw [centerDensityQ_one] at heq
  have hN : Fintype.card ι < 1 + 12 + Nat.choose 12 2 := by
    rw [hcard]; decide
  have h12 : (1 : ℝ) / (2 * ((12 : ℕ) : ℝ)) = 1 / 24 := by norm_num
  obtain ⟨hg, -⟩ := (centerDensity_eq_iff_of_card_lt (n := 12) (by norm_num) X hN).mp
    (by rw [heq, h12])
  have h4 : GapAtLeast X 4 := (gapAtLeast_iff_le_gapSq (by norm_num) X 4).mpr (by rw [hg]; norm_num)
  -- coordinates within `1/4`
  have hclose : ∀ k i, |X k i - C k i| < 1 / 4 := fun k i => by
    have h1 : dist (X k i) (C k i) ≤ dist X C :=
      (dist_le_pi_dist (X k) (C k) i).trans (dist_le_pi_dist X C k)
    have h2 : dist X C < 1 / 4 := Metric.mem_ball.mp hX.2
    rw [Real.dist_eq] at h1
    linarith
  obtain ⟨k₀⟩ := ‹Nonempty ι›
  refine ⟨X k₀ - C k₀, fun k => funext fun i => ?_⟩
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hk : k = k₀
  · subst hk; ring
  · obtain ⟨z, hz, -⟩ := equality_differences h4 (by rw [hcard]) (by norm_num) (Ne.symm hk)
    obtain ⟨w, hw⟩ := int_diff_of_isBinary hC k₀ k i
    have := eq_translate_of_close (hz i) hw (hclose k i) (hclose k₀ i)
    linarith

end Stealth

end
