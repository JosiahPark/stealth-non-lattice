import StealthAudit.PhaseAlgebra

/-!
# D1. The rank principle behind Theorem 1.2 and Lemma 4.1

For a motif `X : ι → Fin n → ℝ` and a finite family of frequencies `b : κ → Fin n → ℤ`, the
evaluation matrix `evalMatrix X b` has the columns `V_b = (e^{πi b·x})_{x ∈ X} ∈ ℂ^N` of §4 of the
paper. Proved here:

* `conjTranspose_mul_evalMatrix`: the Gram matrix of the columns has entries `a_X(b q - b p)`;
* `conjTranspose_mul_evalMatrix_of_orthogonal`: if `a_X(b q - b p) = 0` for all `p ≠ q`, the Gram
  matrix is `N • 1` (the columns are mutually orthogonal of norm `√N`);
* `card_le_card_of_orthogonal`: in that case the number of frequencies is at most `N`, for a
  nonempty motif;
* `card_le_card_of_gapAtLeast`: the same conclusion from `GapAtLeast X s`, when all differences
  `b q - b p` (`p ≠ q`) are nonzero of squared norm less than `s`.

What this file does NOT prove: any specific bound such as `N ≥ 2n` (that needs a choice of
frequencies; see `CardinalityBound.lean`), and nothing about the equality case of Theorem 1.2.
-/

noncomputable section

open Finset Matrix
open scoped ComplexConjugate

namespace Stealth

variable {n : ℕ} {ι κ : Type*}

/-- The evaluation matrix: the column of the frequency `b p` is `(e^{πi (b p)·x})_{x ∈ X}`. -/
def evalMatrix (X : ι → Fin n → ℝ) (b : κ → Fin n → ℤ) : Matrix ι κ ℂ :=
  Matrix.of fun k p => phase (b p) (X k)

@[simp] theorem evalMatrix_apply (X : ι → Fin n → ℝ) (b : κ → Fin n → ℤ) (k : ι) (p : κ) :
    evalMatrix X b k p = phase (b p) (X k) := rfl

/-- The Gram matrix of the evaluation columns: its `(p, q)` entry is `a_X(b q - b p)`. -/
theorem conjTranspose_mul_evalMatrix [Fintype ι] (X : ι → Fin n → ℝ) (b : κ → Fin n → ℤ)
    (p q : κ) :
    ((evalMatrix X b)ᴴ * evalMatrix X b) p q = amp X (b q - b p) := by
  rw [← sum_conj_phase_mul_phase]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- If all the amplitudes `a_X(b q - b p)`, `p ≠ q`, vanish, the evaluation columns are mutually
orthogonal of squared norm `N`. -/
theorem conjTranspose_mul_evalMatrix_of_orthogonal [Fintype ι] [DecidableEq κ] (X : ι → Fin n → ℝ)
    (b : κ → Fin n → ℤ) (h : ∀ p q, p ≠ q → amp X (b q - b p) = 0) :
    (evalMatrix X b)ᴴ * evalMatrix X b = (Fintype.card ι : ℂ) • (1 : Matrix κ κ ℂ) := by
  ext p q
  rw [conjTranspose_mul_evalMatrix]
  by_cases hpq : p = q
  · subst hpq
    simp [amp_zero]
  · simp [h p q hpq, hpq]

/-- **Rank principle.** A family of frequencies whose pairwise differences all have zero
amplitude has at most `N` members: the evaluation columns are `|κ|` mutually orthogonal nonzero
vectors of `ℂ^N`. -/
theorem card_le_card_of_orthogonal [Fintype ι] [Fintype κ] [Nonempty ι] (X : ι → Fin n → ℝ)
    (b : κ → Fin n → ℤ)
    (h : ∀ p q, p ≠ q → amp X (b q - b p) = 0) : Fintype.card κ ≤ Fintype.card ι := by
  classical
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinv : ((Fintype.card ι : ℂ)⁻¹ • (evalMatrix X b)ᴴ) * evalMatrix X b = 1 := by
    rw [Matrix.smul_mul, conjTranspose_mul_evalMatrix_of_orthogonal X b h, smul_smul,
      inv_mul_cancel₀ hN, one_smul]
  calc Fintype.card κ = (1 : Matrix κ κ ℂ).rank := (Matrix.rank_one (R := ℂ)).symm
    _ = (((Fintype.card ι : ℂ)⁻¹ • (evalMatrix X b)ᴴ) * evalMatrix X b).rank := by rw [hinv]
    _ ≤ ((Fintype.card ι : ℂ)⁻¹ • (evalMatrix X b)ᴴ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card ι := Matrix.rank_le_card_width _

/-- The rank principle in the form used in §4–§5: if `4 K(P)² ≥ s` and the frequencies `b p` have
pairwise differences that are nonzero of squared norm less than `s`, there are at most `N` of
them. -/
theorem card_le_card_of_gapAtLeast [Fintype ι] [Fintype κ] [Nonempty ι] (X : ι → Fin n → ℝ) (s : ℤ)
    (hX : GapAtLeast X s) (b : κ → Fin n → ℤ)
    (hb : ∀ p q, p ≠ q → b q - b p ≠ 0 ∧ sqNorm (b q - b p) < s) :
    Fintype.card κ ≤ Fintype.card ι :=
  card_le_card_of_orthogonal X b fun p q hpq => hX _ (hb p q hpq).1 (hb p q hpq).2

end Stealth

end
