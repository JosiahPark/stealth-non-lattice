import Mathlib

/-!
# H1. Simple periodic configurations and their pair coefficients

A simple equally weighted periodic configuration in `ℝⁿ` (in the sense used by Proposition 7.1) is
`Q = {w k + γ : k, γ ∈ Γ}` with period lattice `Γ = A ℤⁿ` (`det A ≠ 0`) and `M > 0` representatives
`w k` that are pairwise distinct modulo `Γ`. Its density is `M / |det A|`, and its normalized pair
coefficient at `t ∈ ℝⁿ` is

  `pairCoeff Q t = #{(k, l) : w l − w k − t ∈ Γ} / M`,

the fraction of points `x ∈ Q` (counted per period) with `x + t ∈ Q`.

Proved here:

* `pairCoeff_zero`: `pairCoeff Q 0 = 1`;
* `pairCoeff_nonneg`, `pairCoeff_le_one`: `0 ≤ pairCoeff Q t ≤ 1` (each `k` has at most one matching
  `l`, by distinctness);
* `pairCoeff_pos_iff`: `0 < pairCoeff Q t` exactly when `t` is a difference of two points of `Q`;
* `pairCoeff_eq_one_iff`: `pairCoeff Q t = 1` exactly when `t` is a period of `Q`
  (`x ∈ Q → x + t ∈ Q`);
* `density_pos`.

What this file does NOT prove: anything about formal duality (item H2) or Proposition 7.1 (H5).
-/

noncomputable section

open Finset Matrix

namespace Stealth

/-- A simple equally weighted periodic configuration: period lattice `A ℤⁿ` and `M` representatives
pairwise distinct modulo it. -/
structure PeriodicConfig (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  det_ne_zero : A.det ≠ 0
  M : ℕ
  M_pos : 0 < M
  w : Fin M → Fin n → ℝ
  distinct : ∀ (k l : Fin M) (z : Fin n → ℤ), w l - w k = A *ᵥ (fun i => (z i : ℝ)) → k = l

namespace PeriodicConfig

variable {n : ℕ} (Q : PeriodicConfig n)

/-- The lattice vector `A z`. -/
def lat (z : Fin n → ℤ) : Fin n → ℝ := Q.A *ᵥ (fun i => (z i : ℝ))

/-- Membership in the period lattice `Γ = A ℤⁿ`. -/
def InLattice (v : Fin n → ℝ) : Prop := ∃ z, v = Q.lat z

/-- Membership in the configuration. -/
def mem (x : Fin n → ℝ) : Prop := ∃ k z, x = Q.w k + Q.lat z

/-- The particle density `M / |det A|`. -/
def density : ℝ := Q.M / |Q.A.det|

open Classical in
/-- The pairs `(k, l)` with `w l − w k − t ∈ Γ`. -/
def pairSet (t : Fin n → ℝ) : Finset (Fin Q.M × Fin Q.M) :=
  univ.filter fun p => Q.InLattice (Q.w p.2 - Q.w p.1 - t)

/-- The normalized pair coefficient at `t`. -/
def pairCoeff (t : Fin n → ℝ) : ℝ := ((Q.pairSet t).card : ℝ) / Q.M

theorem lat_zero : Q.lat 0 = 0 := by
  have h : (fun i => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) = 0 := by ext; simp
  unfold lat
  rw [h, mulVec_zero]

theorem lat_add (a b : Fin n → ℤ) : Q.lat (a + b) = Q.lat a + Q.lat b := by
  unfold lat; rw [← mulVec_add]; congr 1; ext i; simp

theorem lat_neg (a : Fin n → ℤ) : Q.lat (-a) = -Q.lat a := by
  unfold lat; rw [← mulVec_neg]; congr 1; ext i; simp

theorem lat_sub (a b : Fin n → ℤ) : Q.lat (a - b) = Q.lat a - Q.lat b := by
  unfold lat; rw [← mulVec_sub]; congr 1; ext i; simp

theorem mem_pairSet {t : Fin n → ℝ} {p : Fin Q.M × Fin Q.M} :
    p ∈ Q.pairSet t ↔ Q.InLattice (Q.w p.2 - Q.w p.1 - t) := by
  simp [pairSet]

theorem density_pos : 0 < Q.density := by
  have : (0 : ℝ) < Q.M := by exact_mod_cast Q.M_pos
  have := abs_pos.mpr Q.det_ne_zero
  unfold density; positivity

/-- Each `k` has at most one partner `l`. -/
theorem pair_unique {t : Fin n → ℝ} {p q : Fin Q.M × Fin Q.M} (hp : p ∈ Q.pairSet t)
    (hq : q ∈ Q.pairSet t) (h : p.1 = q.1) : p = q := by
  obtain ⟨a, ha⟩ := Q.mem_pairSet.mp hp
  obtain ⟨b, hb⟩ := Q.mem_pairSet.mp hq
  have h2 : p.2 = q.2 := by
    refine Q.distinct p.2 q.2 (b - a) ?_
    show Q.w q.2 - Q.w p.2 = Q.lat (b - a)
    rw [Q.lat_sub, ← ha, ← hb, h]
    abel
  exact Prod.ext h h2

theorem card_pairSet_image (t : Fin n → ℝ) :
    ((Q.pairSet t).image Prod.fst).card = (Q.pairSet t).card :=
  card_image_of_injOn fun _ hp _ hq h => Q.pair_unique hp hq h

theorem card_pairSet_le (t : Fin n → ℝ) : (Q.pairSet t).card ≤ Q.M := by
  rw [← Q.card_pairSet_image t]
  exact (card_le_univ _).trans (by simp)

theorem card_pairSet_eq_iff (t : Fin n → ℝ) :
    (Q.pairSet t).card = Q.M ↔ ∀ k, ∃ l, (k, l) ∈ Q.pairSet t := by
  rw [← Q.card_pairSet_image t]
  constructor
  · intro h k
    have hu : (Q.pairSet t).image Prod.fst = univ :=
      eq_univ_of_card _ (by rw [h, Fintype.card_fin])
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (hu ▸ mem_univ k)
    exact ⟨p.2, hp⟩
  · intro h
    have hu : (Q.pairSet t).image Prod.fst = univ :=
      eq_univ_iff_forall.mpr fun k => by
        obtain ⟨l, hl⟩ := h k
        exact mem_image.mpr ⟨(k, l), hl, rfl⟩
    rw [hu, card_univ, Fintype.card_fin]

theorem pairCoeff_nonneg (t : Fin n → ℝ) : 0 ≤ Q.pairCoeff t := by
  unfold pairCoeff; positivity

theorem pairCoeff_le_one (t : Fin n → ℝ) : Q.pairCoeff t ≤ 1 := by
  have hM : (0 : ℝ) < Q.M := by exact_mod_cast Q.M_pos
  unfold pairCoeff
  rw [div_le_one hM]
  exact_mod_cast Q.card_pairSet_le t

theorem pairCoeff_eq_one_iff_card (t : Fin n → ℝ) :
    Q.pairCoeff t = 1 ↔ (Q.pairSet t).card = Q.M := by
  have hM : (Q.M : ℝ) ≠ 0 := by exact_mod_cast Q.M_pos.ne'
  unfold pairCoeff
  rw [div_eq_one_iff_eq hM]
  exact_mod_cast Iff.rfl

theorem pairCoeff_zero : Q.pairCoeff 0 = 1 := by
  rw [pairCoeff_eq_one_iff_card, card_pairSet_eq_iff]
  intro k
  exact ⟨k, Q.mem_pairSet.mpr ⟨0, by rw [lat_zero]; simp⟩⟩

/-- `pairCoeff Q t > 0` exactly when `t` is a difference of two points of `Q`. -/
theorem pairCoeff_pos_iff (t : Fin n → ℝ) :
    0 < Q.pairCoeff t ↔ ∃ x y, Q.mem x ∧ Q.mem y ∧ y - x = t := by
  have hM : (0 : ℝ) < Q.M := by exact_mod_cast Q.M_pos
  unfold pairCoeff
  rw [div_pos_iff_of_pos_right hM, Nat.cast_pos, card_pos]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨b, hb⟩ := Q.mem_pairSet.mp hp
    refine ⟨Q.w p.1, Q.w p.2 + Q.lat (-b), ⟨p.1, 0, by rw [lat_zero, add_zero]⟩, ⟨p.2, -b, rfl⟩, ?_⟩
    rw [lat_neg, show Q.w p.2 + -Q.lat b - Q.w p.1 = (Q.w p.2 - Q.w p.1 - t) - Q.lat b + t by abel,
      hb]
    abel
  · rintro ⟨x, y, ⟨k, a, rfl⟩, ⟨l, b, rfl⟩, h⟩
    refine ⟨(k, l), Q.mem_pairSet.mpr ⟨a - b, ?_⟩⟩
    rw [lat_sub, ← h]
    abel

/-- `pairCoeff Q t = 1` exactly when `t` is a period of `Q`. -/
theorem pairCoeff_eq_one_iff (t : Fin n → ℝ) :
    Q.pairCoeff t = 1 ↔ ∀ x, Q.mem x → Q.mem (x + t) := by
  rw [pairCoeff_eq_one_iff_card, card_pairSet_eq_iff]
  constructor
  · rintro h x ⟨k, a, rfl⟩
    obtain ⟨l, hl⟩ := h k
    obtain ⟨b, hb⟩ := Q.mem_pairSet.mp hl
    refine ⟨l, a - b, ?_⟩
    have hk : Q.w k + t = Q.w l - Q.lat b := by rw [← hb]; abel
    rw [lat_sub, show Q.w k + Q.lat a + t = (Q.w k + t) + Q.lat a by abel, hk]
    abel
  · intro h k
    obtain ⟨l, b, hb⟩ := h (Q.w k) ⟨k, 0, by rw [lat_zero, add_zero]⟩
    refine ⟨l, Q.mem_pairSet.mpr ⟨-b, ?_⟩⟩
    rw [lat_neg, show Q.w l - Q.w k - t = Q.w l - (Q.w k + t) by abel, hb]
    abel

end PeriodicConfig

end Stealth

end
