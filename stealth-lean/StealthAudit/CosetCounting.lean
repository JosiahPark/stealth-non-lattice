import StealthAudit.IndexDet

/-!
# H4b. Coset counting

Let `H ≤ ℤⁿ` be a subgroup and let `r : Fin M → ℤⁿ` be pairwise distinct modulo `H`, such that the union
of the cosets `r k + H` is invariant under `2ℤⁿ`. With `L = H ⊔ 2ℤⁿ`:

* every fibre of `k ↦ r k mod L` has exactly `[L : H]` elements (`card_fiber`): the map
  `l ↦ (r l − r k) mod H` is a bijection from the fibre of `k` onto `L ⧸ H`;
* hence `[L : H] ∣ M` (`relIndex_dvd_card`), and since `[ℤⁿ : L] ∣ [ℤⁿ : 2ℤⁿ] = 2ⁿ` (H4a) and
  `[ℤⁿ : H] = [L : H] [ℤⁿ : L]`, `2ⁿ M` is a multiple of `[ℤⁿ : H]` (`two_pow_mul_card_eq`).

The hypothesis `H.index ≠ 0` of the roadmap item is not needed.

Proved here: `mem_twoZ`, `card_fiber`, `relIndex_dvd_card`, `two_pow_mul_card_eq`.

What this file does NOT prove: the integrality of the density of a periodic configuration (H4c).
-/

noncomputable section

open Finset

namespace Stealth

variable {n M : ℕ}

/-- The subgroup `2ℤⁿ` of `ℤⁿ`. -/
def twoZ (n : ℕ) : AddSubgroup (Fin n → ℤ) :=
  (LinearMap.range (Matrix.toLin' ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)))).toAddSubgroup

theorem mem_twoZ {x : Fin n → ℤ} : x ∈ twoZ n ↔ ∃ v, x = 2 • v := by
  have h : ∀ v : Fin n → ℤ, Matrix.toLin' ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) v = 2 • v := by
    intro v; ext i; simp [Matrix.toLin'_apply]
  simp only [twoZ, Submodule.mem_toAddSubgroup, LinearMap.mem_range, h]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

variable {H : AddSubgroup (Fin n → ℤ)} {r : Fin M → Fin n → ℤ}

/-- Each fibre of `k ↦ r k mod (H ⊔ 2ℤⁿ)` has `[H ⊔ 2ℤⁿ : H]` elements. -/
theorem card_fiber [DecidableEq ((Fin n → ℤ) ⧸ (H ⊔ twoZ n))]
    (hdist : ∀ k l, r l - r k ∈ H → k = l) (hinv : ∀ k (v : Fin n → ℤ), ∃ l, r k + 2 • v - r l ∈ H)
    (k : Fin M) :
    #{l | (r l : (Fin n → ℤ) ⧸ (H ⊔ twoZ n)) = r k} = H.relIndex (H ⊔ twoZ n) := by
  set s : Finset (Fin M) := {l | (r l : (Fin n → ℤ) ⧸ (H ⊔ twoZ n)) = r k}
  have hmemL : ∀ l ∈ s, r l - r k ∈ (H ⊔ twoZ n) := fun l hl => by
    have h := QuotientAddGroup.eq.mp (mem_filter.mp hl).2
    have := (H ⊔ twoZ n).neg_mem h
    rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
  let f : s → ↥(H ⊔ twoZ n) ⧸ H.addSubgroupOf (H ⊔ twoZ n) := fun l =>
    (⟨r l - r k, hmemL l l.2⟩ : ↥(H ⊔ twoZ n))
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
      have h' := AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h)
      have : r l₂ - r l₁ ∈ H := by
        convert h' using 1
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        abel
      exact Subtype.ext (hdist l₁ l₂ this)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H x =>
        obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp x.2
        obtain ⟨v, rfl⟩ := mem_twoZ.mp hz
        obtain ⟨l, hl⟩ := hinv k v
        have hls : l ∈ s := by
          refine mem_filter.mpr ⟨mem_univ _, QuotientAddGroup.eq.mpr ?_⟩
          have h2 : (2 • v) ∈ H ⊔ twoZ n :=
            (le_sup_right : twoZ n ≤ H ⊔ twoZ n) (mem_twoZ.mpr ⟨v, rfl⟩)
          have := (H ⊔ twoZ n).sub_mem ((le_sup_left : H ≤ (H ⊔ twoZ n)) hl) h2
          convert this using 1
          abel
        refine ⟨⟨l, hls⟩, QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)⟩
        have := H.add_mem hl hy
        convert this using 1
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, ← hyz]
        abel
  rw [← Nat.card_eq_finsetCard]
  exact (Nat.card_eq_of_bijective f hf).trans rfl

theorem relIndex_dvd_card (hdist : ∀ k l, r l - r k ∈ H → k = l)
    (hinv : ∀ k (v : Fin n → ℤ), ∃ l, r k + 2 • v - r l ∈ H) : H.relIndex (H ⊔ twoZ n) ∣ M := by
  classical
  have h := card_eq_sum_card_image (fun l => (r l : (Fin n → ℤ) ⧸ (H ⊔ twoZ n))) univ
  rw [card_univ, Fintype.card_fin] at h
  rw [h, sum_const_nat (m := H.relIndex (H ⊔ twoZ n)) fun b hb => ?_]
  · exact dvd_mul_left _ _
  · obtain ⟨k, -, rfl⟩ := mem_image.mp hb
    exact card_fiber hdist hinv k

/-- **Coset counting.** `2ⁿ M` is a multiple of `[ℤⁿ : H]`. -/
theorem two_pow_mul_card_eq (hdist : ∀ k l, r l - r k ∈ H → k = l)
    (hinv : ∀ k (v : Fin n → ℤ), ∃ l, r k + 2 • v - r l ∈ H) :
    ∃ c : ℕ, 2 ^ n * M = c * H.index := by
  obtain ⟨a, ha⟩ := relIndex_dvd_card hdist hinv
  have hL : (H ⊔ twoZ n).index ∣ 2 ^ n := by
    have := AddSubgroup.index_dvd_of_le (le_sup_right : twoZ n ≤ H ⊔ twoZ n)
    rwa [twoZ, index_range_two] at this
  obtain ⟨b, hb⟩ := hL
  refine ⟨a * b, ?_⟩
  rw [← AddSubgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ twoZ n), ha, hb]
  ring

end Stealth

end
