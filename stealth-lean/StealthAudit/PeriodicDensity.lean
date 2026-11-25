import StealthAudit.PeriodicConfig
import StealthAudit.CosetCounting

/-!
# H4c. The density of a `ℤⁿ`-periodic configuration in `½ℤⁿ` is an integer

Let `Q` be a simple periodic configuration (H1) with period lattice `A ℤⁿ` and `M` representatives
`w k`. Assume that every `u ∈ ℤⁿ` is a period of `Q` and that any two points of `Q` differ by a vector
of `½ℤⁿ` (for a formal dual of a binary motif these are H3 and `formallyDual_support`, H2). Then
`density Q = M / |det A|` is a natural number.

Proof. Each column `A eⱼ` is a difference of two points of `Q`, so `B = 2A` is an integer matrix, with
`det B = 2ⁿ det A ≠ 0`. The vectors `r k = 2 (w k − w 0)` are integral, pairwise distinct modulo
`H = B ℤⁿ` (distinctness of the `w k` modulo `A ℤⁿ`), and their cosets form a `2ℤⁿ`-invariant union
(integer periods of `Q`). By H4b `2ⁿ M = c · [ℤⁿ : H]`, and `[ℤⁿ : H] = |det B| = 2ⁿ |det A|` by H4a,
so `M / |det A| = c`.

Proved here: `PeriodicConfig.lat_single`, `PeriodicConfig.density_eq_nat`.

What this file does NOT prove: Proposition 7.1 (item H5).
-/

noncomputable section

open Finset Matrix

namespace Stealth

namespace PeriodicConfig

variable {n : ℕ} (Q : PeriodicConfig n)

theorem lat_single (i j : Fin n) : Q.lat (Pi.single j 1) i = Q.A i j := by
  simp [lat, mulVec, dotProduct, Pi.single_apply]

/-- **Integer density.** If every integer vector is a period of `Q` and all differences of points of
`Q` lie in `½ℤⁿ`, then `density Q` is a natural number. -/
theorem density_eq_nat
    (hper : ∀ (u : Fin n → ℤ) (x : Fin n → ℝ), Q.mem x → Q.mem (x + fun i => (u i : ℝ)))
    (hsupp : ∀ x y, Q.mem x → Q.mem y → ∀ i, ∃ z : ℤ, 2 * (y i - x i) = z) :
    ∃ m : ℕ, Q.density = m := by
  have hmem : ∀ k, Q.mem (Q.w k) := fun k => ⟨k, 0, by rw [Q.lat_zero, add_zero]⟩
  let k0 : Fin Q.M := ⟨0, Q.M_pos⟩
  -- `B = 2A` is an integer matrix
  have hAint : ∀ i j, ∃ z : ℤ, 2 * Q.A i j = z := by
    intro i j
    obtain ⟨z, hz⟩ := hsupp (Q.w k0) (Q.w k0 + Q.lat (Pi.single j 1)) (hmem k0) ⟨k0, _, rfl⟩ i
    refine ⟨z, ?_⟩
    rw [← hz, Pi.add_apply, add_sub_cancel_left, lat_single]
  choose B0 hB0 using hAint
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℤ, ∀ i j, 2 * Q.A i j = B i j :=
    ⟨Matrix.of B0, hB0⟩
  have hBlat : ∀ (z : Fin n → ℤ) i, (((B *ᵥ z) i : ℤ) : ℝ) = 2 * Q.lat z i := by
    intro z i
    simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, lat, Finset.mul_sum, ← hB]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdetR : ((B.det : ℤ) : ℝ) = 2 ^ n * Q.A.det := by
    have h1 : B.map (Int.castRingHom ℝ) = (2 : ℝ) • Q.A := by
      ext i j; simp [← hB]
    rw [show ((B.det : ℤ) : ℝ) = (Int.castRingHom ℝ) B.det from rfl, RingHom.map_det,
      RingHom.mapMatrix_apply, h1, det_smul, Fintype.card_fin]
  have hBdet : B.det ≠ 0 := by
    have : ((B.det : ℤ) : ℝ) ≠ 0 := by
      rw [hdetR]; exact mul_ne_zero (by positivity) Q.det_ne_zero
    exact_mod_cast this
  -- the integer representatives `r k = 2 (w k − w 0)`
  have hrint : ∀ k i, ∃ z : ℤ, 2 * (Q.w k i - Q.w k0 i) = z := fun k i =>
    hsupp _ _ (hmem k0) (hmem k) i
  choose r hr using hrint
  set H := (LinearMap.range (Matrix.toLin' B)).toAddSubgroup with hH
  have memH : ∀ x, x ∈ H ↔ ∃ z, B *ᵥ z = x := fun x => by
    simp [hH, Matrix.toLin'_apply]
  have hdist : ∀ k l, r l - r k ∈ H → k = l := by
    intro k l h
    obtain ⟨z, hz⟩ := (memH _).mp h
    refine Q.distinct k l z (funext fun i => ?_)
    have h1 := congrArg (fun v => ((v i : ℤ) : ℝ)) hz
    simp only [Pi.sub_apply, Int.cast_sub, hBlat] at h1
    rw [← hr l i, ← hr k i] at h1
    show Q.w l i - Q.w k i = Q.lat z i
    linarith
  have hinv : ∀ k (v : Fin n → ℤ), ∃ l, r k + 2 • v - r l ∈ H := by
    intro k v
    obtain ⟨l, z, hz⟩ := hper v (Q.w k) (hmem k)
    refine ⟨l, (memH _).mpr ⟨z, funext fun i => ?_⟩⟩
    have h1 := congrFun hz i
    simp only [Pi.add_apply] at h1
    have : (((B *ᵥ z) i : ℤ) : ℝ) = (((r k + 2 • v - r l) i : ℤ) : ℝ) := by
      rw [hBlat]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Int.cast_add, Int.cast_sub, ← hr]
      have h2v : (((2 • v i : ℤ)) : ℝ) = 2 * (v i : ℝ) := by
        simp
      rw [h2v]
      linarith
    exact_mod_cast this
  -- counting
  obtain ⟨c, hc⟩ := two_pow_mul_card_eq hdist hinv
  rw [hH, index_range_toLin' B hBdet] at hc
  refine ⟨c, ?_⟩
  have hcR : (2 : ℝ) ^ n * Q.M = c * |((B.det : ℤ) : ℝ)| := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hc
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_natAbs, Int.cast_abs] using this
  rw [hdetR, abs_mul, abs_pow, abs_two] at hcR
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (Q.M : ℝ) = c * |Q.A.det| :=
    mul_left_cancel₀ h2.ne' (show (2 : ℝ) ^ n * Q.M = 2 ^ n * (c * |Q.A.det|) by rw [hcR]; ring)
  unfold density
  rw [div_eq_iff (abs_pos.mpr Q.det_ne_zero).ne', hM]

end PeriodicConfig

end Stealth

end
