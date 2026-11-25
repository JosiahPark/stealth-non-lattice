import StealthAudit.PeriodicConfig
import StealthAudit.Basic

/-!
# H2. Formal duality with a cubic-period configuration

Let `X : ι → Fin n → ℝ` be a motif with points distinct modulo `2ℤⁿ`, so `P = X + 2ℤⁿ` is a simple
periodic configuration with `N = card ι` points per period and density `N / 2ⁿ`, and let `Q` be a simple
periodic configuration (H1) with period lattice `Γ = A ℤⁿ` and `M` representatives `w k`.

**The definition used.** In [3] (Cohn, Kumar, Reiher, Schürmann) formal duality is defined by a
Poisson-type summation identity for Schwartz functions. For periodic configurations it is equivalent to
the following statement about pair coefficients: the Fourier transform of the pair correlation of each
configuration is supported on the dual lattice of its period lattice, and there it equals the pair
coefficients of the other configuration. That analytic definition and the equivalence are NOT
formalized. Here `FormallyDual X Q` is DEFINED by the pair-coefficient conditions:

* (i) `ρ(P) · ρ(Q) = 1`;
* (ii) for `t ∈ ℝⁿ`: if `2t = u ∈ ℤⁿ` (that is, `t` lies in the dual lattice `½ℤⁿ` of `2ℤⁿ`), then
  `pairCoeff Q t = ‖a_X(u)‖² / N²`, where `a_X(u) = ∑ₖ e^{πi u·Xₖ} = ∑ₖ e^{2πi ⟨t, Xₖ⟩}`; otherwise
  `pairCoeff Q t = 0`;
* (iii) with the roles exchanged: for `s` in the dual lattice `Γ*` of `Γ`, the pair coefficient of `P` at
  `s` equals `‖∑ₖ e^{2πi⟨s, w k⟩}‖² / M²`, and for `s ∉ Γ*` it is `0`.

Proved here: `formallyDual_support` (two points of a formal dual of `P` differ by a vector of `½ℤⁿ`) and
`pairCoeff_of_formallyDual`.

What this file does NOT prove: the equivalence of this definition with the analytic definition of [3],
and Proposition 7.1 (item H5). The paper says the pair correlation of `Q` is "supported on `ℤⁿ`"; the
argument needs only the support in `½ℤⁿ` that (ii) gives.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- `t` lies in `½ℤⁿ`, the dual lattice of `2ℤⁿ`, with `2t = u`. -/
def HalfIntVec (t : Fin n → ℝ) (u : Fin n → ℤ) : Prop := ∀ i, 2 * t i = u i

open Classical in
/-- The normalized pair coefficient of `P = X + 2ℤⁿ` at `s`:
`#{(j, k) : X k − X j − s ∈ 2ℤⁿ} / N`. -/
def motifPairCoeff (X : ι → Fin n → ℝ) (s : Fin n → ℝ) : ℝ :=
  ((univ.filter fun p : ι × ι => ∃ z : Fin n → ℤ, ∀ i, X p.2 i - X p.1 i - s i = 2 * z i).card : ℝ) /
    Fintype.card ι

namespace PeriodicConfig

variable (Q : PeriodicConfig n)

/-- `s` lies in the dual lattice `Γ*` of the period lattice of `Q`. -/
def InDual (s : Fin n → ℝ) : Prop := ∀ z : Fin n → ℤ, ∃ m : ℤ, ∑ i, s i * Q.lat z i = m

/-- The Fourier coefficient `∑ₖ e^{2πi⟨s, w k⟩}` of the representatives of `Q`. -/
def fourierCoeff (s : Fin n → ℝ) : ℂ :=
  ∑ k, Complex.exp (((2 * Real.pi * ∑ i, s i * Q.w k i : ℝ) : ℂ) * Complex.I)

end PeriodicConfig

/-- **Formal duality** of `P = X + 2ℤⁿ` and `Q`, in the pair-coefficient form (see the module
docstring: this characterization is the definition used here). -/
structure FormallyDual (X : ι → Fin n → ℝ) (Q : PeriodicConfig n) : Prop where
  distinct : DistinctModPeriod X
  density_mul : density X * Q.density = 1
  pair_of_half : ∀ (t : Fin n → ℝ) (u : Fin n → ℤ), HalfIntVec t u →
    Q.pairCoeff t = ‖amp X u‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2
  pair_of_not_half : ∀ t : Fin n → ℝ, (¬ ∃ u, HalfIntVec t u) → Q.pairCoeff t = 0
  dual_pair : ∀ s : Fin n → ℝ, Q.InDual s →
    motifPairCoeff X s = ‖Q.fourierCoeff s‖ ^ 2 / (Q.M : ℝ) ^ 2
  dual_pair_zero : ∀ s : Fin n → ℝ, ¬ Q.InDual s → motifPairCoeff X s = 0

theorem pairCoeff_of_formallyDual {X : ι → Fin n → ℝ} {Q : PeriodicConfig n} (h : FormallyDual X Q)
    (t : Fin n → ℝ) (u : Fin n → ℤ) (ht : HalfIntVec t u) :
    Q.pairCoeff t = ‖amp X u‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2 :=
  h.pair_of_half t u ht

/-- **Support.** Two points of a formal dual of `X + 2ℤⁿ` differ by a vector of `½ℤⁿ`. -/
theorem formallyDual_support {X : ι → Fin n → ℝ} {Q : PeriodicConfig n} (h : FormallyDual X Q)
    {x y : Fin n → ℝ} (hx : Q.mem x) (hy : Q.mem y) : ∀ i, ∃ z : ℤ, 2 * (y i - x i) = z := by
  have hpos : 0 < Q.pairCoeff (y - x) := (Q.pairCoeff_pos_iff _).mpr ⟨x, y, hx, hy, rfl⟩
  by_cases hu : ∃ u, HalfIntVec (y - x) u
  · obtain ⟨u, hu⟩ := hu
    exact fun i => ⟨u i, by simpa using hu i⟩
  · exact absurd (h.pair_of_not_half _ hu) hpos.ne'

end Stealth

end
