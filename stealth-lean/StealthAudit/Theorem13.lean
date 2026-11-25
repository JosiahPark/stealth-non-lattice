import StealthAudit.ReciprocalGram
import StealthAudit.TestAmplitudes
import StealthAudit.AmpContinuity
import StealthAudit.PeriodShape

/-!
# F5a. Theorem 1.3 (local maximality in the marked period model)

In the marked period model of A3, the stealth center density of the configuration with motif `X`
(`N` labelled representatives) and period shape `Q` (real symmetric positive definite with `det Q = 1`)
is `centerDensityQ X Q = (gapQ X Q / 4)^{n/2} / N`, the right side of formula (3); `Q = 1` is the cube.

**Theorem 1.3.** Let `n ≥ 4` and let `C` be a binary motif of strength three with `N ≡ 8 (mod 16)`. Then
there are a neighbourhood `U` of `C` and `δ > 0` such that for every motif `X ∈ U` and every period shape
`Q` with `‖Q − 1‖² < δ`:

* `centerDensityQ X Q ≤ 1/N = centerDensityQ C 1` (local maximality), and
* `centerDensityQ X Q < 1/N` when `Q ≠ 1` (every small nonsimilarity change of period shape strictly
  decreases `Δ_st`).

Proof (§6). By F2 every test vector `v` survives for `C`, and by F4 for every `X` near `C`; hence
`gapQ X Q ≤ vᵀ Q v` for every test vector. With `Q = 1` this gives `gapQ ≤ 4`, and for `Q ≠ 1` near `1`
Lemma 6.1 (F3c) gives a test vector with `vᵀ Q v < 4`.

Proved here: `centerDensityQ_le_of_gapQ_le`, `centerDensityQ_lt_of_gapQ_lt`, `centerDensityQ_one_of_strength_three`,
`theorem_1_3`.

What this file does NOT prove: the last sentence of Theorem 1.3 (for `n = 12`, `N = 24` the equality case
is locally isolated modulo translations, similarities and relabelling; item F5b). The derivation of
formula (3) from a period matrix `B` is a remark in A3, not a theorem; here the period shape enters as `Q`
(`Q = 1` exactly when `B` is a similarity). Points are counted with multiplicity, so the paper's
hypothesis "distinct rows" is not needed.
-/

noncomputable section

open Finset Filter Topology

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem centerDensityQ_le_of_gapQ_le [Nonempty ι] {X : ι → Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hn : 0 < n) (h : gapQ X Q ≤ 4) :
    centerDensityQ X Q ≤ 1 / (Fintype.card ι : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hg := gapQ_pos hQ hn X
  unfold centerDensityQ
  refine div_le_div_of_nonneg_right ?_ hN.le
  exact Real.rpow_le_one (by positivity) (by linarith) (by positivity)

theorem centerDensityQ_lt_of_gapQ_lt [Nonempty ι] {X : ι → Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hn : 0 < n) (h : gapQ X Q < 4) :
    centerDensityQ X Q < 1 / (Fintype.card ι : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hg := gapQ_pos hQ hn X
  unfold centerDensityQ
  refine div_lt_div_of_pos_right ?_ hN
  exact Real.rpow_lt_one (by positivity) (by linarith) (by positivity)

theorem centerDensityQ_one_of_strength_three [Nonempty ι] {C : ι → Fin n → ℝ} (hn : 0 < n)
    (hC : IsBinary C) (hs : HasStrength C 3) :
    centerDensityQ C 1 = 1 / (Fintype.card ι : ℝ) := by
  rw [centerDensityQ_one, centerDensity_of_hasStrength_three hn hC hs]

/-- **Theorem 1.3** in the marked period model. -/
theorem theorem_1_3 [Nonempty ι] (hn : 4 ≤ n) {C : ι → Fin n → ℝ} (hC : IsBinary C)
    (hs : HasStrength C 3) (hN : Fintype.card ι % 16 = 8) :
    centerDensityQ C 1 = 1 / (Fintype.card ι : ℝ) ∧
      ∃ U ∈ 𝓝 C, ∃ δ : ℝ, 0 < δ ∧ ∀ X ∈ U, ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef → Q.det = 1 →
        frobSq (Q - 1) < δ →
          centerDensityQ X Q ≤ 1 / (Fintype.card ι : ℝ) ∧
            (Q ≠ 1 → centerDensityQ X Q < 1 / (Fintype.card ι : ℝ)) := by
  have hn0 : 0 < n := by omega
  refine ⟨centerDensityQ_one_of_strength_three hn0 hC hs, ?_⟩
  -- test vectors survive near `C`
  have hsurv : ∀ᶠ X in 𝓝 C, ∀ v ∈ testFinset n, amp X v ≠ 0 :=
    eventually_amp_ne_zero C (testFinset n) fun v hv =>
      amp_testVector_ne_zero hC hs hN (mem_testFinset.mp hv)
  obtain ⟨-, δ, hδ, hlemma⟩ := lemma_6_1 hn
  refine ⟨_, hsurv, δ, hδ, fun X hX Q hQ hdet hlt => ?_⟩
  have hgap : ∀ v ∈ testVectors n, gapQ X Q ≤ quadForm Q v := fun v hv =>
    gapQ_le_of_survives hQ hn0 ⟨testVector_ne_zero hv, hX v (mem_testFinset.mpr hv)⟩
  refine ⟨?_, fun hQ1 => ?_⟩
  · -- some test vector has `vᵀ Q v ≤ 4`
    by_cases hQ1 : Q = 1
    · subst hQ1
      have hv : (fun j : Fin n => if j = ⟨0, hn0⟩ then (2 : ℤ) else 0) ∈ testVectors n :=
        Or.inl ⟨_, rfl⟩
      exact centerDensityQ_le_of_gapQ_le hQ hn0
        ((hgap _ hv).trans (quadForm_one_testVector hv).le)
    · have hpos : 0 < frobSq (Q - 1) := frobSq_pos (sub_ne_zero.mpr hQ1)
      obtain ⟨v, hv, hq⟩ := hlemma Q hQ hdet hpos hlt
      exact centerDensityQ_le_of_gapQ_le hQ hn0 ((hgap v hv).trans hq.le)
  · have hpos : 0 < frobSq (Q - 1) := frobSq_pos (sub_ne_zero.mpr hQ1)
    obtain ⟨v, hv, hq⟩ := hlemma Q hQ hdet hpos hlt
    exact centerDensityQ_lt_of_gapQ_lt hQ hn0 (lt_of_le_of_lt (hgap v hv) hq)

end Stealth

end
