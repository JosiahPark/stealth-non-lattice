import StealthAudit.PeriodShape

/-!
# F1. The sign lemma inside Lemma 6.1

Let `n ≥ 4` and let `E` be a real symmetric `n × n` matrix with trace `0` and `E ≠ 0`. Then some test
vector `v` of §6,

  `v ∈ V = {2eᵢ} ∪ {∑_{i ∈ I} εᵢ eᵢ : |I| = 4, εᵢ = ±1}`,

has `vᵀ E v < 0`. If some diagonal entry is negative, `2eᵢ` works. Otherwise every diagonal entry is `0`
(the trace vanishes), some `E a b ≠ 0` with `a ≠ b`, and for a 4-set `I ∋ a, b` the 16 sign patterns on
`I` give values `q(ε) = 2 ∑_{i<j ∈ I} εᵢ εⱼ E i j` whose sum is `0` while the sum weighted by `ε_a ε_b` is
`32 E a b ≠ 0`; so not all are `≥ 0`.

Proved here:

* `testVectors`: the set `V`, as a `Set (Fin n → ℤ)`;
* `exists_sign_pattern_neg`: the 16-pattern argument for four coordinates;
* `quadForm_two_single`: `(2eᵢ)ᵀ E (2eᵢ) = 4 E i i`;
* `exists_testVector_quadForm_neg`: the sign lemma.

What this file does NOT prove: the rest of Lemma 6.1 (items F2, F3).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ}

/-- The test vectors of §6: `2eᵢ`, and the vectors with entries `±1` on a 4-set and `0` elsewhere. -/
def testVectors (n : ℕ) : Set (Fin n → ℤ) :=
  {v | (∃ i, v = fun j => if j = i then 2 else 0) ∨
    ∃ I : Finset (Fin n), I.card = 4 ∧ (∀ i ∈ I, v i = 1 ∨ v i = -1) ∧ ∀ i ∉ I, v i = 0}

/-- For four coordinates: if `x₀₁ ≠ 0`, some sign pattern makes `∑_{k<l} sₖ sₗ x_{kl}` negative. -/
theorem exists_sign_pattern_neg (x01 x02 x03 x12 x13 x23 : ℝ) (hx : x01 ≠ 0) :
    ∃ s : Fin 4 → ℤ, (∀ k, s k = 1 ∨ s k = -1) ∧
      (s 0 : ℝ) * s 1 * x01 + s 0 * s 2 * x02 + s 0 * s 3 * x03 + s 1 * s 2 * x12 +
        s 1 * s 3 * x13 + s 2 * s 3 * x23 < 0 := by
  by_contra hcon
  push Not at hcon
  have h : ∀ s : Fin 4 → ℤ, (∀ k, s k = 1 ∨ s k = -1) →
      0 ≤ (s 0 : ℝ) * s 1 * x01 + s 0 * s 2 * x02 + s 0 * s 3 * x03 + s 1 * s 2 * x12 +
        s 1 * s 3 * x13 + s 2 * s 3 * x23 := hcon
  have h0 := h ![1, 1, 1, 1] (by intro k; fin_cases k <;> simp)
  have h1 := h ![1, 1, 1, -1] (by intro k; fin_cases k <;> simp)
  have h2 := h ![1, 1, -1, 1] (by intro k; fin_cases k <;> simp)
  have h3 := h ![1, 1, -1, -1] (by intro k; fin_cases k <;> simp)
  have h4 := h ![1, -1, 1, 1] (by intro k; fin_cases k <;> simp)
  have h5 := h ![1, -1, 1, -1] (by intro k; fin_cases k <;> simp)
  have h6 := h ![1, -1, -1, 1] (by intro k; fin_cases k <;> simp)
  have h7 := h ![1, -1, -1, -1] (by intro k; fin_cases k <;> simp)
  have h8 := h ![-1, 1, 1, 1] (by intro k; fin_cases k <;> simp)
  have h9 := h ![-1, 1, 1, -1] (by intro k; fin_cases k <;> simp)
  have h10 := h ![-1, 1, -1, 1] (by intro k; fin_cases k <;> simp)
  have h11 := h ![-1, 1, -1, -1] (by intro k; fin_cases k <;> simp)
  have h12 := h ![-1, -1, 1, 1] (by intro k; fin_cases k <;> simp)
  have h13 := h ![-1, -1, 1, -1] (by intro k; fin_cases k <;> simp)
  have h14 := h ![-1, -1, -1, 1] (by intro k; fin_cases k <;> simp)
  have h15 := h ![-1, -1, -1, -1] (by intro k; fin_cases k <;> simp)
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  apply hx
  linarith

theorem quadForm_two_single (E : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    quadForm E (fun j => if j = i then 2 else 0) = 4 * E i i := by
  simp only [quadForm]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq']
  ring

/-- **The sign lemma.** For `n ≥ 4`, a nonzero symmetric trace-free real matrix `E` has `vᵀ E v < 0`
for some test vector `v`. -/
theorem exists_testVector_quadForm_neg (hn : 4 ≤ n) (E : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, E i j = E j i) (htr : E.trace = 0) (hE : E ≠ 0) :
    ∃ v ∈ testVectors n, quadForm E v < 0 := by
  classical
  by_cases hdiag : ∃ i, E i i < 0
  · obtain ⟨i, hi⟩ := hdiag
    exact ⟨_, Or.inl ⟨i, rfl⟩, by rw [quadForm_two_single]; linarith⟩
  push Not at hdiag
  -- the diagonal vanishes
  have hzero : ∀ i, E i i = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hdiag i)).mp htr
    exact fun i => h i (mem_univ i)
  -- an off-diagonal entry is nonzero
  obtain ⟨a, b, hab⟩ : ∃ a b, E a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Matrix.ext h)
  have hne : a ≠ b := fun h => hab (h ▸ hzero a)
  -- two more coordinates
  have hcard : 1 < ((univ.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hne]), Finset.card_erase_of_mem (mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc hd
  obtain ⟨hcb, hca⟩ := hc
  obtain ⟨hdb, hda⟩ := hd
  obtain ⟨s, hs, hneg⟩ := exists_sign_pattern_neg (E a b) (E a c) (E a d) (E b c) (E b d) (E c d) hab
  let v : Fin n → ℤ := fun i =>
    if i = a then s 0 else if i = b then s 1 else if i = c then s 2 else if i = d then s 3 else 0
  have hva : v a = s 0 := by simp [v]
  have hvb : v b = s 1 := by simp [v, Ne.symm hne]
  have hvc : v c = s 2 := by simp [v, hca, hcb]
  have hvd : v d = s 3 := by simp [v, hda, hdb, Ne.symm hcd]
  let I : Finset (Fin n) := {a, b, c, d}
  have hout : ∀ i ∉ I, v i = 0 := by
    intro i hi
    simp only [I, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [v, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
  have hIcard : I.card = 4 := by
    simp [I, Finset.card_insert_of_notMem, hne, hca.symm, hda.symm, hcb.symm, hdb.symm, hcd]
  have hvI : ∀ i ∈ I, v i = 1 ∨ v i = -1 := by
    intro i hi
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [hva]; exact hs 0
    · rw [hvb]; exact hs 1
    · rw [hvc]; exact hs 2
    · rw [hvd]; exact hs 3
  refine ⟨v, Or.inr ⟨I, hIcard, hvI, hout⟩, ?_⟩
  -- reduce the quadratic form to the four coordinates
  have hsub : ∀ f : Fin n → ℝ, (∀ i ∉ I, f i = 0) → ∑ i, f i = ∑ i ∈ I, f i := fun f hf =>
    (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hf i hi)).symm
  have hq : quadForm E v = ∑ i ∈ I, ∑ j ∈ I, (v i : ℝ) * E i j * (v j : ℝ) := by
    unfold quadForm
    rw [hsub _ (fun i hi => by simp [hout i hi])]
    refine Finset.sum_congr rfl fun i _ => hsub _ (fun j hj => by simp [hout j hj])
  have ha : a ∉ ({b, c, d} : Finset (Fin n)) := by simp [hne, Ne.symm hca, Ne.symm hda]
  have hb : b ∉ ({c, d} : Finset (Fin n)) := by simp [Ne.symm hcb, Ne.symm hdb]
  have hc' : c ∉ ({d} : Finset (Fin n)) := by simp [hcd]
  rw [hq]
  simp only [I, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc',
    Finset.sum_singleton, hva, hvb, hvc, hvd, hzero, hsymm b a, hsymm c a, hsymm d a, hsymm c b,
    hsymm d b, hsymm d c]
  linarith

end Stealth

end
