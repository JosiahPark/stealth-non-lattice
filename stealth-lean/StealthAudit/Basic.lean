import Mathlib

/-!
# Shared definitions for the stealth project

Definitions (with definitional unfolding lemmas only) following §2–§3 of J. Park, "Hadamard
configurations and sharp cubic-period bounds for stealth in dimensions 10, 11, and 12"
(4 Nov 2026; `paper/stealth_hadamard.pdf`). Other files in `StealthAudit/` should
`import StealthAudit.Basic` and reuse these definitions instead of redefining them.

Conventions.

* The marked period is always `2ℤⁿ`. A motif is an indexed family `X : ι → Fin n → ℝ` with `ι` a
  finite type; `N = Fintype.card ι`. Repeated points are allowed (they act as integer weights), and
  the points are not required to lie in `[0, 2)ⁿ`. The paper's "`N` distinct representatives" is
  the extra hypothesis `DistinctModPeriod X`.
* Frequencies are integer vectors `u : Fin n → ℤ`; the dual-lattice point is `ξ = u / 2`.
  `amp X u` is the paper's `a_X(u) = ∑_{x ∈ X} e^{πi u·x}`.
* The paper's formula (2), `K(P) = min {‖ξ‖ : ξ ∈ L* \ {0}, A_X(ξ) ≠ 0}`, is taken here as the
  DEFINITION of the stealth radius. `gapSq X` is `4 K(P)²`, the least `‖u‖²` over nonzero
  frequencies of nonzero amplitude, and `GapAtLeast X s` says `4 K(P)² ≥ s`. So `K(P) ≥ 1` is
  `GapAtLeast X 4` and `K(P) > 1` is `GapAtLeast X 5`.

What this file does NOT contain: any definition of the diffraction measure of a periodic set, so
the derivation of (2) from diffraction theory is outside this library; any period lattice other
than `2ℤⁿ` (formula (3) of the paper is not stated here); any theorem beyond unfolding lemmas.
In particular `gapSq X` is `0` by convention when no frequency survives; that a frequency always
survives for `n ≥ 1` and nonempty `ι` is roadmap item A2 (`StealthRadius.lean`), not proved in this
file.
-/

noncomputable section

open Finset

namespace Stealth

/-! ### Frequencies, phases and amplitudes (paper §2) -/

section Amplitude

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The pairing `u · x = ∑ᵢ uᵢ xᵢ` of an integer frequency with a point of `ℝⁿ`. -/
def dot (u : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := ∑ i, (u i : ℝ) * x i

/-- The phase `e^{πi u·x}`. -/
def phase (u : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (((Real.pi * dot u x : ℝ) : ℂ) * Complex.I)

/-- The amplitude `a_X(u) = ∑_{x ∈ X} e^{πi u·x}` of the motif `X` at the frequency `u`. -/
def amp (X : ι → Fin n → ℝ) (u : Fin n → ℤ) : ℂ := ∑ k, phase u (X k)

/-- The squared Euclidean norm `‖u‖² = ∑ᵢ uᵢ²` of an integer vector. -/
def sqNorm (u : Fin n → ℤ) : ℤ := ∑ i, u i ^ 2

/-- A frequency survives when it is nonzero and its amplitude is nonzero (a nonforward
diffraction peak of `X + 2ℤⁿ` at `ξ = u / 2`). -/
def Survives (X : ι → Fin n → ℝ) (u : Fin n → ℤ) : Prop := u ≠ 0 ∧ amp X u ≠ 0

/-- `GapAtLeast X s`: every nonzero frequency with `‖u‖² < s` has zero amplitude. With the paper's
`K(P)` for `P = X + 2ℤⁿ` this says `4 K(P)² ≥ s`. -/
def GapAtLeast (X : ι → Fin n → ℝ) (s : ℤ) : Prop :=
  ∀ u : Fin n → ℤ, u ≠ 0 → sqNorm u < s → amp X u = 0

/-- `4 K(P)²`: the least `‖u‖²` over surviving frequencies (`0` by convention if none survives). -/
def gapSq (X : ι → Fin n → ℝ) : ℕ :=
  sInf {s : ℕ | ∃ u : Fin n → ℤ, Survives X u ∧ sqNorm u = (s : ℤ)}

/-- The raw stealth radius `K(P) = ½ min ‖u‖` of `P = X + 2ℤⁿ` (paper §2, after (2)). -/
def stealthRadius (X : ι → Fin n → ℝ) : ℝ := Real.sqrt (gapSq X) / 2

/-- The point density `ρ(P) = N / 2ⁿ` of `P = X + 2ℤⁿ`, points counted with multiplicity. -/
def density (_X : ι → Fin n → ℝ) : ℝ := (Fintype.card ι : ℝ) / 2 ^ n

/-- The stealth center density (1): `Δ_st(P) = (K(P) / 2)ⁿ / ρ(P)`. -/
def centerDensity (X : ι → Fin n → ℝ) : ℝ := (stealthRadius X / 2) ^ n / density X

/-- The points of the motif are pairwise distinct modulo the period `2ℤⁿ`. -/
def DistinctModPeriod (X : ι → Fin n → ℝ) : Prop :=
  ∀ k l : ι, k ≠ l → ¬ ∃ z : Fin n → ℤ, ∀ i, X k i - X l i = 2 * (z i : ℝ)

theorem dot_def (u : Fin n → ℤ) (x : Fin n → ℝ) : dot u x = ∑ i, (u i : ℝ) * x i := rfl

theorem phase_def (u : Fin n → ℤ) (x : Fin n → ℝ) :
    phase u x = Complex.exp (((Real.pi * dot u x : ℝ) : ℂ) * Complex.I) := rfl

theorem amp_def (X : ι → Fin n → ℝ) (u : Fin n → ℤ) : amp X u = ∑ k, phase u (X k) := rfl

theorem sqNorm_def (u : Fin n → ℤ) : sqNorm u = ∑ i, u i ^ 2 := rfl

theorem density_def (X : ι → Fin n → ℝ) : density X = (Fintype.card ι : ℝ) / 2 ^ n := rfl

end Amplitude

/-! ### Indicator frequencies -/

section Indicator

variable {n : ℕ}

/-- The `0/1` frequency `∑_{i ∈ S} eᵢ` of a set of coordinates. -/
def ind (S : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ S then 1 else 0

/-- The coordinates where `u` is odd: the support of `u mod 2`. -/
def oddSupp (u : Fin n → ℤ) : Finset (Fin n) := univ.filter fun i => u i % 2 = 1

@[simp] theorem ind_apply (S : Finset (Fin n)) (i : Fin n) : ind S i = if i ∈ S then 1 else 0 := rfl

@[simp] theorem mem_oddSupp (u : Fin n → ℤ) (i : Fin n) : i ∈ oddSupp u ↔ u i % 2 = 1 := by
  simp [oddSupp]

end Indicator

/-! ### Binary motifs and orthogonal arrays (paper §3) -/

section Binary

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A binary motif: every coordinate of every point is `0` or `1`. -/
def IsBinary (X : ι → Fin n → ℝ) : Prop := ∀ k i, X k i = 0 ∨ X k i = 1

/-- The binary character sum `∑_{x ∈ X} ∏_{i ∈ S} (1 - 2 xᵢ)`; for a binary motif this is the
paper's `\widehat{1_C}(u)` with `S` the support of `u ∈ 𝔽₂ⁿ`. -/
def charSum (X : ι → Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ k, ∏ i ∈ S, (1 - 2 * X k i)

/-- Strength `t` in Fourier form: every character sum of weight `1, …, t` vanishes. For a binary
motif without repeated points this is the paper's "orthogonal array of strength `t`". -/
def HasStrength (X : ι → Fin n → ℝ) (t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ t → charSum X S = 0

theorem charSum_def (X : ι → Fin n → ℝ) (S : Finset (Fin n)) :
    charSum X S = ∑ k, ∏ i ∈ S, (1 - 2 * X k i) := rfl

end Binary

/-! ### Hadamard matrices and antipodal arrays (paper §3) -/

section Hadamard

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A Hadamard matrix indexed by `α`: entries `±1` and `H Hᵀ = |α| I`. -/
structure IsHadamard (H : Matrix α α ℤ) : Prop where
  entry : ∀ i j, H i j = 1 ∨ H i j = -1
  mul_transpose : H * H.transpose = (Fintype.card α : ℤ) • (1 : Matrix α α ℤ)

end Hadamard

/-- The antipodal binary array of `H`: the rows of `H` and of `-H`, restricted to the columns
`c 0, …, c (n-1)`, with a sign `s` mapped to `(1 - s) / 2`. The index `(r, false)` is row `r` of
`H` and `(r, true)` is row `r` of `-H`. -/
def antipodalMotif {α : Type*} {n : ℕ} (H : Matrix α α ℤ) (c : Fin n → α) : α × Bool → Fin n → ℝ :=
  fun p i => (1 - (if p.2 then -1 else 1) * (H p.1 (c i) : ℝ)) / 2

theorem antipodalMotif_apply {α : Type*} {n : ℕ} (H : Matrix α α ℤ) (c : Fin n → α) (p : α × Bool)
    (i : Fin n) :
    antipodalMotif H c p i = (1 - (if p.2 then -1 else 1) * (H p.1 (c i) : ℝ)) / 2 := rfl

end Stealth

end
