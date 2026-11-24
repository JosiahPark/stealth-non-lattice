import StealthAudit.Theorem11

/-!
# C6. The configurations are not translates of lattices (Theorem 1.1, last clause)

`periodicSet X` is the point set `X + 2ℤⁿ`. `IsSubgroupTranslate P` says that `P = t + L` for
some point `t` and some additive subgroup `L` of `ℝⁿ`; a translate of a lattice is of this form,
so `¬ IsSubgroupTranslate P` is stronger than "not a translate of a lattice". Proved here,
following the proof of Theorem 1.1 (translate a point to the origin; the quotient by `2ℤⁿ` is a
subgroup of `𝔽₂ⁿ`, whose order is a power of two):

* `exists_card_eq_two_pow`: a subset of `𝔽₂ⁿ` that contains `0` and is closed under addition has
  `2^d` elements;
* `bits_injective`: for a binary motif with points distinct modulo `2ℤⁿ`, reduction modulo 2 is
  injective;
* `card_eq_two_pow_of_isSubgroupTranslate`: if `X` is binary, its points are distinct modulo
  `2ℤⁿ`, and `X + 2ℤⁿ` is a translate of an additive subgroup, then `N` is a power of two;
* `twentyfour_ne_two_pow`: `24` is not a power of two;
* `not_isSubgroupTranslate_paley`: the projected Paley configurations (`7 ≤ n`) are not
  translates of additive subgroups of `ℝⁿ`, in particular not translates of lattices;
* `periodicSet_reindex`, and `theorem_1_1_full`: **Theorem 1.1** with the non-lattice clause:
  for `n ∈ {10, 11, 12}` there are 24 points, distinct modulo `2ℤⁿ`, with `K = 1`,
  `ρ = 24 / 2ⁿ`, `Δ_st = 1/24`, whose periodic set is not a translate of an additive subgroup.

What this file does NOT prove: the last sentence of Theorem 1.1 (the comparison with duals of
record lattice packings; the arithmetic of the table is `Comparisons.lean`, with the record
values as quoted inputs).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-- The periodic point set `X + 2ℤⁿ`. -/
def periodicSet {ι : Type*} (X : ι → Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ k, ∃ z : Fin n → ℤ, ∀ i, y i = X k i + 2 * (z i : ℝ)}

/-- `P` is a translate `t + L` of an additive subgroup `L` of `ℝⁿ` (for instance of a lattice). -/
def IsSubgroupTranslate (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (t : Fin n → ℝ) (L : AddSubgroup (Fin n → ℝ)), ∀ y, y ∈ P ↔ y - t ∈ L

/-! ### Subgroups of `𝔽₂ⁿ` -/

/-- A subset of `𝔽₂ⁿ` containing `0` and closed under addition has a power of two elements. -/
theorem exists_card_eq_two_pow (S : Finset (Fin n → ZMod 2)) (h0 : 0 ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) : ∃ d, S.card = 2 ^ d := by
  let L : AddSubgroup (Fin n → ZMod 2) :=
    { carrier := (S : Set (Fin n → ZMod 2))
      zero_mem' := by exact_mod_cast h0
      add_mem' := fun {x y} hx hy => by
        have hx' : x ∈ S := by exact_mod_cast hx
        have hy' : y ∈ S := by exact_mod_cast hy
        exact_mod_cast hadd x hx' y hy'
      neg_mem' := fun {x} hx => by
        have hneg : -x = x := by
          funext i
          exact ZMod.neg_eq_self_mod_two (x i)
        rw [hneg]
        exact hx }
  have hdvd : Nat.card L ∣ Nat.card (Fin n → ZMod 2) := AddSubgroup.card_addSubgroup_dvd_card L
  have hG : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    simp [Nat.card_eq_fintype_card]
  have hL : Nat.card L = S.card := by
    have : Nat.card L = Nat.card (S : Set (Fin n → ZMod 2)) := rfl
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hG, hL] at hdvd
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨d, hd⟩

/-! ### Reduction modulo 2 of a binary motif -/

/-- The integer `0` or `1` of a real coordinate (`1` exactly when the coordinate is `1`). -/
def bitZ (x : ℝ) : ℤ := if x = 1 then 1 else 0

theorem cast_bitZ {x : ℝ} (hx : x = 0 ∨ x = 1) : ((bitZ x : ℤ) : ℝ) = x := by
  rcases hx with rfl | rfl <;> simp [bitZ]

/-- The reduction modulo 2 of the point `X k`. -/
def bits {ι : Type*} (X : ι → Fin n → ℝ) (k : ι) : Fin n → ZMod 2 :=
  fun i => ((bitZ (X k i) : ℤ) : ZMod 2)

theorem bitZ_cast_injective {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : ((bitZ a : ℤ) : ZMod 2) = ((bitZ b : ℤ) : ZMod 2)) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [bitZ] at h ⊢

/-- If `a + b - c = d + 2w` with `a, b, c, d ∈ {0, 1}` and `w` an integer, the same relation
holds modulo 2. -/
theorem bitZ_closure {a b c d : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (w : ℤ) (h : a + b - c = d + 2 * (w : ℝ)) :
    ((bitZ d : ℤ) : ZMod 2)
      = ((bitZ a : ℤ) : ZMod 2) + ((bitZ b : ℤ) : ZMod 2) - ((bitZ c : ℤ) : ZMod 2) := by
  have hZ : bitZ a + bitZ b - bitZ c = bitZ d + 2 * w := by
    have hR : ((bitZ a + bitZ b - bitZ c : ℤ) : ℝ) = ((bitZ d + 2 * w : ℤ) : ℝ) := by
      push_cast
      rw [cast_bitZ ha, cast_bitZ hb, cast_bitZ hc, cast_bitZ hd]
      exact h
    exact_mod_cast hR
  have h2 : ((bitZ a + bitZ b - bitZ c : ℤ) : ZMod 2) = ((bitZ d + 2 * w : ℤ) : ZMod 2) := by
    rw [hZ]
  push_cast at h2
  have two0 : (2 : ZMod 2) = 0 := by decide
  rw [two0, zero_mul, add_zero] at h2
  exact h2.symm

section Motif

variable {ι : Type*} {X : ι → Fin n → ℝ}

/-- For a binary motif with points distinct modulo `2ℤⁿ`, reduction modulo 2 is injective. -/
theorem bits_injective (hb : IsBinary X) (hd : DistinctModPeriod X) :
    Function.Injective (bits X) := by
  intro k l h
  by_contra hkl
  refine hd k l hkl ⟨0, fun i => ?_⟩
  rw [bitZ_cast_injective (hb k i) (hb l i) (congrFun h i)]
  simp

/-- If `X` is binary with points distinct modulo `2ℤⁿ`, and `X + 2ℤⁿ` is a translate of an
additive subgroup of `ℝⁿ`, then the number of points is a power of two. -/
theorem card_eq_two_pow_of_isSubgroupTranslate [Fintype ι] (hb : IsBinary X)
    (hd : DistinctModPeriod X) (h : IsSubgroupTranslate (periodicSet X)) :
    ∃ d, Fintype.card ι = 2 ^ d := by
  classical
  obtain ⟨t, L, hL⟩ := h
  have ht : t ∈ periodicSet X := (hL t).mpr (by simp)
  obtain ⟨k₀, z₀, hz₀⟩ := ht
  have hmem : ∀ k, X k - t ∈ L := fun k => (hL (X k)).mp ⟨k, 0, by simp⟩
  have hclos : ∀ k l, ∃ m, bits X m = bits X k + bits X l - bits X k₀ := by
    intro k l
    have hsum : (X k + X l - t) - t ∈ L := by
      have hadd := L.add_mem (hmem k) (hmem l)
      have e : (X k + X l - t) - t = (X k - t) + (X l - t) := by abel
      rw [e]
      exact hadd
    obtain ⟨m, z, hz⟩ := (hL (X k + X l - t)).mpr hsum
    refine ⟨m, ?_⟩
    funext i
    have e : X k i + X l i - X k₀ i = X m i + 2 * ((z i + z₀ i : ℤ) : ℝ) := by
      have h1 := hz i
      have h2 := hz₀ i
      simp only [Pi.add_apply, Pi.sub_apply] at h1
      push_cast
      linarith
    exact bitZ_closure (hb k i) (hb l i) (hb k₀ i) (hb m i) _ e
  let S : Finset (Fin n → ZMod 2) := univ.image fun k => bits X k - bits X k₀
  have hinj : Function.Injective fun k => bits X k - bits X k₀ := fun k l hkl =>
    bits_injective hb hd (sub_left_injective hkl)
  have hcard : S.card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj]
    rfl
  have h0 : (0 : Fin n → ZMod 2) ∈ S :=
    Finset.mem_image.mpr ⟨k₀, Finset.mem_univ _, sub_self _⟩
  have hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S := by
    intro x hx y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨m, hm⟩ := hclos k l
    refine Finset.mem_image.mpr ⟨m, Finset.mem_univ _, ?_⟩
    rw [hm]
    abel
  obtain ⟨d, hd'⟩ := exists_card_eq_two_pow S h0 hadd
  exact ⟨d, by rw [← hcard, hd']⟩

theorem periodicSet_reindex {κ : Type*} (e : κ ≃ ι) (X : ι → Fin n → ℝ) :
    periodicSet (X ∘ e) = periodicSet X := by
  ext y
  constructor
  · rintro ⟨k, z, h⟩
    exact ⟨e k, z, h⟩
  · rintro ⟨k, z, h⟩
    exact ⟨e.symm k, z, by simpa using h⟩

end Motif

/-! ### The Paley configurations -/

/-- `24` is not a power of two. -/
theorem twentyfour_ne_two_pow (d : ℕ) : 24 ≠ 2 ^ d := by
  intro h
  rcases Nat.lt_or_ge d 5 with hd | hd
  · interval_cases d <;> norm_num at h
  · have : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega

/-- The projected Paley configurations are not translates of additive subgroups of `ℝⁿ`; in
particular they are not translates of lattices. -/
theorem not_isSubgroupTranslate_paley {n : ℕ} (hn : 7 ≤ n) {c : Fin n → Option (ZMod 11)}
    (hc : Function.Injective c) :
    ¬ IsSubgroupTranslate (periodicSet (antipodalMotif paley12 c)) := by
  intro h
  obtain ⟨hb, hd, -⟩ := paley_configuration hn hc
  obtain ⟨d, hd'⟩ := card_eq_two_pow_of_isSubgroupTranslate hb hd h
  rw [card_paley_index] at hd'
  exact twentyfour_ne_two_pow d hd'

/-- **Theorem 1.1 (explicit examples).** For each `n ∈ {10, 11, 12}` there is a periodic
configuration `X + 2ℤⁿ` with 24 representatives modulo `2ℤⁿ` (pairwise distinct) such that
`K = 1`, `ρ = 24 / 2ⁿ` and `Δ_st = 1/24`, and which is not a translate of an additive subgroup of
`ℝⁿ` (in particular not a translate of a lattice). The comparison with record lattice packings in
the last sentence of the theorem is not part of this statement. -/
theorem theorem_1_1_full (n : ℕ) (hn : n = 10 ∨ n = 11 ∨ n = 12) :
    ∃ X : Fin 24 → Fin n → ℝ, IsBinary X ∧ DistinctModPeriod X ∧ stealthRadius X = 1 ∧
      density X = 24 / 2 ^ n ∧ centerDensity X = 1 / 24 ∧
      ¬ IsSubgroupTranslate (periodicSet X) := by
  have hcard : Fintype.card (Option (ZMod 11)) = 12 := by decide
  obtain ⟨c⟩ : Nonempty (Fin n ↪ Option (ZMod 11)) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hcard]; omega)
  obtain ⟨hb, hd, hK, hρ, hΔ⟩ := paley_configuration (n := n) (by omega) c.injective
  let e : Fin 24 ≃ Option (ZMod 11) × Bool :=
    (Fintype.equivFinOfCardEq card_paley_index).symm
  refine ⟨antipodalMotif paley12 c ∘ e, isBinary_reindex e hb, distinctModPeriod_reindex e hd, ?_,
    ?_, ?_, ?_⟩
  · rw [stealthRadius_reindex, hK]
  · rw [density_reindex, hρ]
  · rw [centerDensity_reindex, hΔ]
  · rw [periodicSet_reindex]
    exact not_isSubgroupTranslate_paley (by omega) c.injective

end Stealth

end
