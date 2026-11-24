import StealthAudit.Basic

/-!
# A1. Phase algebra

Elementary identities for `dot`, `phase` and `amp` of `StealthAudit/Basic.lean` (paper §2):

* `phase_zero`, `phase_add`, `phase_neg`, `norm_phase`: `u ↦ e^{πi u·x}` is a unitary character
  of `ℤⁿ`;
* `amp_zero`: `a_X(0) = N`;
* `sum_conj_phase_mul_phase`: `∑_x conj (e^{πi u·x}) e^{πi v·x} = a_X(v - u)`, the inner product of
  two evaluation columns (used in the proofs of Theorem 1.2 and Lemma 4.1);
* `amp_translate`, `gapAtLeast_translate`: a common translation of the motif multiplies every
  amplitude by a unit, so `GapAtLeast` is translation invariant;
* `phase_add_period`, `amp_add_period`: moving the points by vectors of `2ℤⁿ` changes nothing.

What this file does NOT prove: any bound on the number of points, any statement about `gapSq`,
`stealthRadius` or `centerDensity`, and nothing about the diffraction measure. It proves nothing
toward Theorems 1.1–1.3 beyond these identities.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem dot_zero (x : Fin n → ℝ) : dot 0 x = 0 := by simp [dot]

theorem dot_add (u v : Fin n → ℤ) (x : Fin n → ℝ) : dot (u + v) x = dot u x + dot v x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_neg (u : Fin n → ℤ) (x : Fin n → ℝ) : dot (-u) x = -dot u x := by simp [dot]

theorem dot_sub (u v : Fin n → ℤ) (x : Fin n → ℝ) : dot (u - v) x = dot u x - dot v x := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

theorem dot_add_right (u : Fin n → ℤ) (x y : Fin n → ℝ) : dot u (x + y) = dot u x + dot u y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

/-- `e^{πi 0·x} = 1`. -/
theorem phase_zero (x : Fin n → ℝ) : phase 0 x = 1 := by simp [phase, dot_zero]

/-- `e^{πi (u+v)·x} = e^{πi u·x} e^{πi v·x}`. -/
theorem phase_add (u v : Fin n → ℤ) (x : Fin n → ℝ) :
    phase (u + v) x = phase u x * phase v x := by
  simp only [phase, dot_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every phase has modulus one. -/
theorem norm_phase (u : Fin n → ℤ) (x : Fin n → ℝ) : ‖phase u x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_ne_zero (u : Fin n → ℤ) (x : Fin n → ℝ) : phase u x ≠ 0 := Complex.exp_ne_zero _

/-- `e^{πi (-u)·x}` is the complex conjugate of `e^{πi u·x}`. -/
theorem phase_neg (u : Fin n → ℤ) (x : Fin n → ℝ) : phase (-u) x = conj (phase u x) := by
  simp only [phase, dot_neg]
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem conj_phase_mul_phase (u v : Fin n → ℤ) (x : Fin n → ℝ) :
    conj (phase u x) * phase v x = phase (v - u) x := by
  rw [← phase_neg, ← phase_add]
  congr 1
  abel

/-- `a_X(0) = N`. -/
theorem amp_zero (X : ι → Fin n → ℝ) : amp X 0 = (Fintype.card ι : ℂ) := by
  simp [amp, phase_zero]

/-- The inner product of the evaluation columns at `u` and `v` is `a_X(v - u)`. -/
theorem sum_conj_phase_mul_phase (X : ι → Fin n → ℝ) (u v : Fin n → ℤ) :
    ∑ k, conj (phase u (X k)) * phase v (X k) = amp X (v - u) := by
  simp [amp, conj_phase_mul_phase]

theorem phase_add_right (u : Fin n → ℤ) (x t : Fin n → ℝ) :
    phase u (x + t) = phase u x * phase u t := by
  simp only [phase, dot_add_right]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A common translation of the motif multiplies every amplitude by a phase. -/
theorem amp_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) (u : Fin n → ℤ) :
    amp (fun k => X k + t) u = phase u t * amp X u := by
  simp [amp, phase_add_right, Finset.mul_sum, mul_comm]

/-- `GapAtLeast` does not change under a common translation of the motif. -/
theorem gapAtLeast_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) (s : ℤ) :
    GapAtLeast (fun k => X k + t) s ↔ GapAtLeast X s := by
  unfold GapAtLeast
  refine forall_congr' fun u => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [amp_translate, mul_eq_zero, or_iff_right (phase_ne_zero u t)]

/-- `Survives` does not change under a common translation of the motif. -/
theorem survives_translate (X : ι → Fin n → ℝ) (t : Fin n → ℝ) (u : Fin n → ℤ) :
    Survives (fun k => X k + t) u ↔ Survives X u := by
  unfold Survives
  rw [amp_translate, mul_ne_zero_iff, and_iff_right (phase_ne_zero u t)]

/-- A point of the period lattice `2ℤⁿ` has trivial phase. -/
theorem phase_two_mul_int (u z : Fin n → ℤ) : phase u (fun i => 2 * (z i : ℝ)) = 1 := by
  have h : (((Real.pi * dot u (fun i => 2 * (z i : ℝ)) : ℝ) : ℂ) * Complex.I)
      = ((∑ i, u i * z i : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [dot]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [phase, h, Complex.exp_int_mul_two_pi_mul_I]

/-- Moving a point by a vector of the period lattice `2ℤⁿ` does not change its phases. -/
theorem phase_add_period (u z : Fin n → ℤ) (x : Fin n → ℝ) :
    phase u (fun i => x i + 2 * (z i : ℝ)) = phase u x := by
  have h := phase_add_right u x (fun i => 2 * (z i : ℝ))
  rw [phase_two_mul_int, mul_one] at h
  exact h

/-- Moving each point of the motif by its own vector of `2ℤⁿ` does not change the amplitudes. -/
theorem amp_add_period (X : ι → Fin n → ℝ) (z : ι → Fin n → ℤ) (u : Fin n → ℤ) :
    amp (fun k i => X k i + 2 * (z k i : ℝ)) u = amp X u := by
  simp only [amp]
  exact Finset.sum_congr rfl fun k _ => phase_add_period u (z k) (X k)

end Stealth

end
