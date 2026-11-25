import StealthAudit.Basic

/-!
# F4. Stability of the amplitudes

For a fixed frequency `u`, the amplitude `X ↦ a_X(u) = ∑ₖ e^{πi u·Xₖ}` is a continuous function of the
motif `X : ι → Fin n → ℝ` (product topology). Hence a finite set of nonzero amplitudes stays nonzero for
all motifs near `X`: the nonforward peaks that the proof of Theorem 1.3 uses persist under small
perturbations of the motif.

Proved here: `continuous_dot_right`, `continuous_phase_right`, `continuous_amp`,
`eventually_amp_ne_zero`.

What this file does NOT prove: Theorem 1.3 itself (item F5).
-/

noncomputable section

open Finset Filter Topology

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem continuous_dot_right (u : Fin n → ℤ) : Continuous fun x : Fin n → ℝ => dot u x := by
  unfold dot
  fun_prop

theorem continuous_phase_right (u : Fin n → ℤ) : Continuous fun x : Fin n → ℝ => phase u x := by
  unfold phase
  have := continuous_dot_right u
  fun_prop

/-- For fixed `u`, the amplitude `a_X(u)` depends continuously on the motif `X`. -/
theorem continuous_amp (u : Fin n → ℤ) : Continuous fun X : ι → Fin n → ℝ => amp X u := by
  unfold amp
  have := continuous_phase_right u
  fun_prop

/-- **Stability.** If the amplitudes of `X` at finitely many frequencies are nonzero, they stay nonzero
for every motif in a neighbourhood of `X`. -/
theorem eventually_amp_ne_zero (X : ι → Fin n → ℝ) (T : Finset (Fin n → ℤ))
    (hT : ∀ u ∈ T, amp X u ≠ 0) : ∀ᶠ Y in 𝓝 X, ∀ u ∈ T, amp Y u ≠ 0 := by
  rw [Filter.eventually_all_finset]
  intro u hu
  exact (continuous_amp u).continuousAt.eventually_ne (hT u hu)

end Stealth

end
