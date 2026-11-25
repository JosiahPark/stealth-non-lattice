import StealthAudit.BinaryMotif
import StealthAudit.PeriodShape

/-!
# B2. Proposition 3.1 as displayed: `4K² = min {4, d⊥}`

For a motif `X` define the dual distance `dualDist X : ℕ∞` as the least weight `|S|` of a nonempty
coordinate set with nonzero binary character sum `charSum X S` (`⊤` if every such sum vanishes). For a
binary motif with points distinct modulo `2ℤⁿ` this is the dual distance `d⊥` of the code `C ⊆ 𝔽₂ⁿ`.

This file proves:

* `hasStrength_iff_lt_dualDist`: `HasStrength X t ↔ t < dualDist X` (any motif, any `t`);
* `gapSq_eq_min_four_dualDist`: for a nonempty binary motif in dimension `n ≥ 1`,
  `4 K(P)² = gapSq X = min 4 d⊥` (equality in `ℕ∞`), the first display of Proposition 3.1 squared;
* `stealthRadius_eq_min_four_dualDist`: `K(P) = √(min 4 d⊥) / 2`;
* `centerDensity_sq_eq_min_four_dualDist`: `Δ_st(P)² = (min 4 d⊥ / 4)ⁿ / N²`;
* `centerDensity_eq_min_four_dualDist`: `Δ_st(P) = (min 4 d⊥ / 4)^{n/2} / N` with a real power, the
  second display of Proposition 3.1.

Here `min 4 d⊥` is finite, and enters the real formulas through `ENat.toNat`.

What this file does NOT prove: that `dualDist` agrees with the dual distance of a linear code (no code
or dual code is defined in this library; the character-sum form is the definition here), and nothing
about repeated points beyond what `charSum` counts with multiplicity.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι] {X : ι → Fin n → ℝ}

/-- The dual distance `d⊥`: the least weight of a nonempty coordinate set with nonzero binary
character sum, `⊤` if there is none. -/
def dualDist (X : ι → Fin n → ℝ) : ℕ∞ :=
  ⨅ S ∈ {S : Finset (Fin n) | S.Nonempty ∧ charSum X S ≠ 0}, (S.card : ℕ∞)

/-- Strength `t` says exactly that the dual distance exceeds `t`. -/
theorem hasStrength_iff_lt_dualDist (X : ι → Fin n → ℝ) (t : ℕ) :
    HasStrength X t ↔ (t : ℕ∞) < dualDist X := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top t), dualDist, le_iInf₂_iff]
  constructor
  · intro h S hS
    by_contra hlt
    have hcard : S.card ≤ t := by
      have h1 : (S.card : ℕ∞) < ((t + 1 : ℕ) : ℕ∞) := by exact_mod_cast not_le.mp hlt
      have h2 : S.card < t + 1 := by exact_mod_cast h1
      omega
    exact hS.2 (h S hS.1 hcard)
  · intro h S hne hcard
    by_contra hS
    have := h S ⟨hne, hS⟩
    have h' : ((t + 1 : ℕ) : ℕ∞) ≤ (S.card : ℕ∞) := by exact_mod_cast this
    have : t + 1 ≤ S.card := by exact_mod_cast h'
    omega

/-- **Proposition 3.1, first display (squared)**: `4 K(P)² = min {4, d⊥}`. -/
theorem gapSq_eq_min_four_dualDist [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    (gapSq X : ℕ∞) = min 4 (dualDist X) := by
  have h4 := gapSq_le_four hn hX
  have hpos := gapSq_pos hn X
  -- for `t ≤ 3`: `t + 1 ≤ gapSq X ↔ t < d⊥`
  have key : ∀ t : ℕ, t ≤ 3 → (t + 1 ≤ gapSq X ↔ (t : ℕ∞) < dualDist X) := fun t ht => by
    rw [le_gapSq_iff_hasStrength hn hX t ht, hasStrength_iff_lt_dualDist]
  apply le_antisymm
  · refine le_min (by exact_mod_cast h4) ?_
    -- `gapSq X - 1 < d⊥`
    have h := (key (gapSq X - 1) (by omega)).mp (by omega)
    have h' : ((gapSq X - 1 : ℕ) : ℕ∞) + 1 ≤ dualDist X :=
      (ENat.add_one_le_iff (ENat.natCast_ne_top _)).mpr h
    have hcast : ((gapSq X - 1 : ℕ) : ℕ∞) + 1 = (gapSq X : ℕ∞) := by
      rw [← ENat.natCast_one, ← ENat.natCast_add, Nat.sub_add_cancel hpos]
    rwa [hcast] at h'
  · rcases Nat.lt_or_ge (gapSq X) 4 with hlt | hge
    · -- `gapSq X ≤ 3`, so strength `gapSq X` fails and `d⊥ ≤ gapSq X`
      have h : ¬ ((gapSq X : ℕ∞) < dualDist X) := fun h =>
        absurd ((key (gapSq X) (by omega)).mpr h) (by omega)
      exact min_le_of_right_le (not_lt.mp h)
    · have : gapSq X = 4 := by omega
      rw [this]
      exact min_le_left _ _

theorem gapSq_eq_toNat_min_four_dualDist [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    gapSq X = (min 4 (dualDist X)).toNat := by
  rw [← gapSq_eq_min_four_dualDist hn hX, ENat.toNat_natCast]

/-- `K(P) = √(min {4, d⊥}) / 2`. -/
theorem stealthRadius_eq_min_four_dualDist [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    stealthRadius X = Real.sqrt ((min 4 (dualDist X)).toNat : ℝ) / 2 := by
  rw [stealthRadius, gapSq_eq_toNat_min_four_dualDist hn hX]

/-- `Δ_st(P)² = (min {4, d⊥} / 4)ⁿ / N²`. -/
theorem centerDensity_sq_eq_min_four_dualDist [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    centerDensity X ^ 2 =
      (((min 4 (dualDist X)).toNat : ℝ) / 4) ^ n / (Fintype.card ι : ℝ) ^ 2 := by
  rw [centerDensity_eq, stealthRadius_eq_min_four_dualDist hn hX, div_pow, ← pow_mul, mul_comm n 2,
    pow_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num

/-- **Proposition 3.1, second display**: `Δ_st(P) = (min {4, d⊥} / 4)^{n/2} / N`. -/
theorem centerDensity_eq_min_four_dualDist [Nonempty ι] (hn : 0 < n) (hX : IsBinary X) :
    centerDensity X =
      (((min 4 (dualDist X)).toNat : ℝ) / 4) ^ ((n : ℝ) / 2) / (Fintype.card ι : ℝ) := by
  rw [← centerDensityQ_one, centerDensityQ, gapQ_one, gapSq_eq_toNat_min_four_dualDist hn hX]

end Stealth

end
