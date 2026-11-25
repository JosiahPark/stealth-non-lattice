import StealthAudit.BinaryParseval
import StealthAudit.FormalDualityArithmetic

/-!
# I2. Finite binary formal duality

Two binary motifs `X : ι → Fin n → ℝ` (`N` points) and `Y : κ → Fin n → ℝ` (`M` points), both
nonempty and without repeated points, are a *binary formal dual pair* (`IsBinaryFormalDual X Y`) when,
for every coordinate set `S`,

  `M · charSum X S ² = N² · binaryDiffCount Y S`.

This is the coefficient identity (ii) of formal duality (H2) for `P = X + 2ℤⁿ` and `Q = Y/2 + ℤⁿ`,
after clearing denominators: by `amp_of_isBinary`, `a_X(u) = charSum X S` for `u ∈ {0,1}ⁿ` with
support `S`, and the pair coefficient of `Q` at `u/2` is `binaryDiffCount Y S / M` (item I4).

Proved here:

* `binaryFormalDual_card_mul`: `N · M = 2ⁿ` (sum the identity over all `S` and use I1);
* `binaryFormalDual_card_dvd`: `N ∣ 2ⁿ`;
* `no_binaryFormalDual_of_card_24`: a 24-point binary motif has no binary formal dual, in any dimension.

The definitions and statements follow the uncompiled candidate file of the bridge note supplied by
Josiah on 2026-11-25; they are compiled and checked here.

What this file does NOT prove: that a formal dual in the sense of H2 gives a binary formal dual pair
(items I3, I4), or Proposition 7.1 from condition (ii) alone (I5).
-/

noncomputable section

open Finset
open scoped Classical

namespace Stealth

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The denominator-cleared CKRS identity on the elementary binary group.
Nonempty and distinct motifs are part of the definition, not consequences. -/
def IsBinaryFormalDual (X : ι → Fin n → ℝ) (Y : κ → Fin n → ℝ) : Prop :=
  Nonempty ι ∧ Nonempty κ ∧ IsBinary X ∧ IsBinary Y ∧
  Function.Injective X ∧ Function.Injective Y ∧
  ∀ S : Finset (Fin n),
    (Fintype.card κ : ℝ) * charSum X S ^ 2 =
      (Fintype.card ι : ℝ)^2 * (binaryDiffCount Y S : ℝ)

/-- Finite formal duals have product of cardinalities equal to the group order. -/
theorem binaryFormalDual_card_mul {X : ι → Fin n → ℝ} {Y : κ → Fin n → ℝ}
    (h : IsBinaryFormalDual X Y) : Fintype.card ι * Fintype.card κ = 2 ^ n := by
  classical
  rcases h with ⟨hi, hk, hb, _, hd, _, hcoeff⟩
  letI : Nonempty ι := hi
  letI : Nonempty κ := hk
  have hsum := Finset.sum_congr (rfl : (univ : Finset (Fin n)).powerset = univ.powerset)
    (fun S _ => hcoeff S)
  rw [← Finset.mul_sum, ← Finset.mul_sum, binary_dual_parseval hb hd, binaryDiffCount_sum Y] at hsum
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hh : (Fintype.card ι : ℝ) * Fintype.card κ = 2 ^ n := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hN hM))
    linear_combination -1 * hsum
  exact_mod_cast hh

theorem binaryFormalDual_card_dvd {X : ι → Fin n → ℝ} {Y : κ → Fin n → ℝ}
    (h : IsBinaryFormalDual X Y) : Fintype.card ι ∣ 2 ^ n :=
  ⟨Fintype.card κ, (binaryFormalDual_card_mul h).symm⟩

/-- The 24-point obstruction in the finite group, all dimensions. -/
theorem no_binaryFormalDual_of_card_24 {X : ι → Fin n → ℝ} {Y : κ → Fin n → ℝ}
    (hN : Fintype.card ι = 24) : ¬ IsBinaryFormalDual X Y := by
  intro h
  have hd := binaryFormalDual_card_dvd h
  rw [hN] at hd
  exact not_twentyfour_dvd_two_pow n hd

end Stealth

end
