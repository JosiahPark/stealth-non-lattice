import StealthAudit.Marginals

/-!
# I1. Binary Parseval and the difference count

For a binary motif `X` without repeated points (`Function.Injective X`):

* `binary_dual_parseval`: `∑_{S ⊆ [n]} charSum X S ^ 2 = 2ⁿ N`. The proof forms the XOR motif
  `dualXorMotif X` on `ι × ι` (coordinatewise `x ⊕ y`), whose character sums are `charSum X S ^ 2`
  (`charSum_dualXorMotif`), and applies the marginal identity `two_pow_mul_card_zeros` of B3 with
  `T = univ`: the pairs with XOR `0` are the `N` diagonal pairs.

For any binary `Y : κ → Fin n → ℝ`, with `binaryDiffCount Y S = #{(k, l) : {i | Y k i ≠ Y l i} = S}`:

* `binaryDiffCount_sum`: `∑_{S ⊆ [n]} binaryDiffCount Y S = (card κ)²` (each pair has exactly one
  difference set).

Also `dual_injective_of_distinctModPeriod`: points distinct modulo `2ℤⁿ` are distinct.

The lemmas follow the uncompiled candidate file of the bridge note supplied by Josiah on 2026-11-25;
they are compiled and checked here.

What this file does NOT prove: finite binary formal duality (I2) or Proposition 7.1 (I5).
-/

noncomputable section

open Finset
open scoped Classical

namespace Stealth

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Binary coordinatewise XOR of two indexed points. -/
def dualXorMotif (X : ι → Fin n → ℝ) (p : ι × ι) (i : Fin n) : ℝ :=
  (1 - (1 - 2 * X p.1 i) * (1 - 2 * X p.2 i)) / 2

omit [Fintype ι] in
theorem dualXorMotif_binary {X : ι → Fin n → ℝ} (hX : IsBinary X) :
    IsBinary (dualXorMotif X) := by
  intro p i
  rcases hX p.1 i with h | h <;> rcases hX p.2 i with h' | h' <;>
    norm_num [dualXorMotif, h, h']

omit [Fintype ι] in
theorem dualXorMotif_zero_iff {X : ι → Fin n → ℝ} (hX : IsBinary X)
    (p : ι × ι) (i : Fin n) : dualXorMotif X p i = 0 ↔ X p.1 i = X p.2 i := by
  rcases hX p.1 i with h | h <;> rcases hX p.2 i with h' | h' <;>
    norm_num [dualXorMotif, h, h']

omit [Fintype ι] in
theorem dualXorMotif_sign (X : ι → Fin n → ℝ) (p : ι × ι) (i : Fin n) :
    1 - 2 * dualXorMotif X p i = (1 - 2 * X p.1 i) * (1 - 2 * X p.2 i) := by
  unfold dualXorMotif
  ring

theorem charSum_dualXorMotif (X : ι → Fin n → ℝ) (S : Finset (Fin n)) :
    charSum (dualXorMotif X) S = charSum X S ^ 2 := by
  simp only [charSum, dualXorMotif_sign, Finset.prod_mul_distrib, Fintype.sum_prod_type]
  rw [pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

omit [Fintype ι] in
/-- Distinct modulo the marked period implies ordinary injectivity. -/
theorem dual_injective_of_distinctModPeriod {X : ι → Fin n → ℝ}
    (hX : DistinctModPeriod X) : Function.Injective X := by
  intro a b h
  by_contra hn
  apply hX a b hn
  refine ⟨0, fun i => ?_⟩
  rw [h]
  simp

/-- Binary Parseval via the repository's already proved zero-marginal identity. -/
theorem binary_dual_parseval {X : ι → Fin n → ℝ} (hb : IsBinary X)
    (hd : Function.Injective X) :
    (∑ S ∈ (univ : Finset (Fin n)).powerset, charSum X S ^ 2) =
      (2 : ℝ) ^ n * (Fintype.card ι : ℝ) := by
  classical
  have h := two_pow_mul_card_zeros (dualXorMotif_binary hb) (univ : Finset (Fin n))
  have hf : ∀ p : ι × ι, (∀ i ∈ (univ : Finset (Fin n)), dualXorMotif X p i = 0) ↔ p.1 = p.2 := by
    intro p
    constructor
    · intro hp
      apply hd
      funext i
      exact (dualXorMotif_zero_iff hb p i).mp (hp i (mem_univ i))
    · intro hp i _
      exact (dualXorMotif_zero_iff hb p i).mpr (by rw [hp])
  have hcount : ((univ : Finset (ι × ι)).filter
      (fun p => ∀ i ∈ (univ : Finset (Fin n)), dualXorMotif X p i = 0)).card = Fintype.card ι := by
    have he : (univ : Finset (ι × ι)).filter
        (fun p => ∀ i ∈ (univ : Finset (Fin n)), dualXorMotif X p i = 0) =
        (univ : Finset ι).image (fun a => (a,a)) := by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hp
        exact ⟨p.1, by cases p; simp_all⟩
      · rintro ⟨a, ha⟩
        rw [← ha]
        intro i _
        exact (dualXorMotif_zero_iff hb (a, a) i).mpr rfl
    rw [he, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]; rfl
  rw [hcount] at h
  simp only [Finset.card_univ, Fintype.card_fin, charSum_dualXorMotif] at h
  exact h.symm

/-- Count pairs by their XOR support (binary subtraction equals addition). -/
def binaryDiffCount (Y : κ → Fin n → ℝ) (S : Finset (Fin n)) : ℕ :=
  ((univ : Finset (κ × κ)).filter
    (fun p => (univ.filter fun i => Y p.1 i ≠ Y p.2 i) = S)).card

/-- Sum of all difference multiplicities. -/
theorem binaryDiffCount_sum (Y : κ → Fin n → ℝ) :
    (∑ S ∈ (univ : Finset (Fin n)).powerset, (binaryDiffCount Y S : ℝ)) =
      (Fintype.card κ : ℝ)^2 := by
  classical
  simp only [binaryDiffCount, ← Finset.sum_boole]
  rw [Finset.sum_comm]
  have hs (p : κ × κ) :
      ∑ S ∈ (univ : Finset (Fin n)).powerset,
        (if (univ.filter fun i => Y p.1 i ≠ Y p.2 i) = S then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (univ.filter fun i => Y p.1 i ≠ Y p.2 i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exfalso
      exact h (mem_powerset.mpr (subset_univ _))
  simp only [hs, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul, pow_two]

end Stealth

end
