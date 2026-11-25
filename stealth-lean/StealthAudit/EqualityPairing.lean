import StealthAudit.Basic

/-!
# D8a. Antipodal pairing of a two-distance binary code

Let `Y : ι → Fin n → ℝ` be a binary motif with `N = 2n` points, `n ≥ 1`, such that any two distinct
points differ in exactly `n` or exactly `n/2` coordinates (the conclusion of D7 after reduction modulo 2).
With the sign vectors `sₖ = 1 − 2 Yₖ ∈ {±1}ⁿ` this says `⟨sₖ, sₗ⟩ ∈ {−n, 0}` for `k ≠ l`.

Proved here:

* `sgn_mul_sgn`, `sum_sgn_mul_sgn`: `⟨sₖ, sₗ⟩ = n − 2 d(k, l)` with `d` the Hamming distance;
* `sum_sgn_mul_sgn_eq_zero`: non-antipodal distinct points have orthogonal sign vectors;
* `antipodal_unique`: each point has at most one antipode (a point differing from it everywhere);
* `card_le_of_orthogonal`: at most `n` points have pairwise orthogonal sign vectors (rank argument);
* `exists_antipodal_pairing`: every point has exactly one antipode, and there is a set `R` of `n`
  points, pairwise orthogonal, such that every point is in `R` or is the antipode of a point of `R`.

What this file does NOT prove: the Hadamard matrix and the bijection with `Fin n × Bool` built from
`R` (item D8b).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι] {Y : ι → Fin n → ℝ}

/-- The sign vector `sₖ = 1 − 2 Yₖ`. -/
def sgn (Y : ι → Fin n → ℝ) (k : ι) (i : Fin n) : ℝ := 1 - 2 * Y k i

/-- The Hamming distance between two points of a motif. -/
def hamming (Y : ι → Fin n → ℝ) (k l : ι) : ℕ := (univ.filter fun i => Y k i ≠ Y l i).card

/-- `l` is an antipode of `k`: the two points differ in every coordinate. -/
def Antipodal (Y : ι → Fin n → ℝ) (k l : ι) : Prop := ∀ i, Y k i ≠ Y l i

omit [Fintype ι] in
theorem sgn_mul_sgn (hY : IsBinary Y) (k l : ι) (i : Fin n) :
    sgn Y k i * sgn Y l i = if Y k i = Y l i then 1 else -1 := by
  unfold sgn
  rcases hY k i with h1 | h1 <;> rcases hY l i with h2 | h2 <;> simp [h1, h2] <;> norm_num

omit [Fintype ι] in
theorem sum_sgn_mul_sgn (hY : IsBinary Y) (k l : ι) :
    ∑ i, sgn Y k i * sgn Y l i = (n : ℝ) - 2 * (hamming Y k l : ℝ) := by
  classical
  simp only [sgn_mul_sgn hY, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => Y k i = Y l i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hh : hamming Y k l = (univ.filter fun i => ¬ Y k i = Y l i).card := rfl
  rw [hh]
  have : ((univ.filter fun i => Y k i = Y l i).card : ℝ) +
      (univ.filter fun i => ¬ Y k i = Y l i).card = n := by exact_mod_cast hsplit
  linarith

omit [Fintype ι] in
theorem hamming_eq_iff_antipodal (k l : ι) : hamming Y k l = n ↔ Antipodal Y k l := by
  unfold hamming Antipodal
  constructor
  · intro h i
    have := Finset.filter_card_eq (s := univ) (p := fun i => Y k i ≠ Y l i)
      (by rw [h, Finset.card_univ, Fintype.card_fin])
    exact this i (mem_univ i)
  · intro h
    rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ, Fintype.card_fin]

/-- The two-distance hypothesis. -/
def TwoDistance (Y : ι → Fin n → ℝ) : Prop :=
  ∀ k l, k ≠ l → hamming Y k l = n ∨ 2 * hamming Y k l = n

omit [Fintype ι] in
theorem sum_sgn_mul_sgn_eq_zero (hY : IsBinary Y) (hd : TwoDistance Y) {k l : ι} (hkl : k ≠ l)
    (hna : ¬ Antipodal Y k l) : ∑ i, sgn Y k i * sgn Y l i = 0 := by
  rw [sum_sgn_mul_sgn hY]
  rcases hd k l hkl with h | h
  · exact absurd ((hamming_eq_iff_antipodal k l).mp h) hna
  · have : (2 * hamming Y k l : ℝ) = n := by exact_mod_cast h
    linarith

omit [Fintype ι] in
theorem antipodal_symm {k l : ι} (h : Antipodal Y k l) : Antipodal Y l k := fun i => (h i).symm

omit [Fintype ι] in
theorem not_antipodal_self (hn : 1 ≤ n) (k : ι) : ¬ Antipodal Y k k :=
  fun h => h ⟨0, hn⟩ rfl

omit [Fintype ι] in
theorem antipodal_unique (hn : 1 ≤ n) (hY : IsBinary Y) (hd : TwoDistance Y) {k l l' : ι}
    (h : Antipodal Y k l) (h' : Antipodal Y k l') : l = l' := by
  by_contra hne
  have heq : ∀ i, Y l i = Y l' i := fun i => by
    have a := h i; have b := h' i
    rcases hY k i with c | c <;> rcases hY l i with d | d <;> rcases hY l' i with e | e <;>
      simp_all
  have h0 : hamming Y l l' = 0 := by
    unfold hamming
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => not_not.mpr (heq i)
  rcases hd l l' hne with h1 | h1 <;> omega

omit [Fintype ι] in
/-- At most `n` points have pairwise orthogonal sign vectors. -/
theorem card_le_of_orthogonal (hn : 1 ≤ n) (hY : IsBinary Y) (R : Finset ι)
    (horth : ∀ k ∈ R, ∀ l ∈ R, k ≠ l → ∑ i, sgn Y k i * sgn Y l i = 0) : R.card ≤ n := by
  classical
  let M : Matrix R (Fin n) ℝ := Matrix.of fun k i => sgn Y k i
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hgram : M * M.transpose = (n : ℝ) • (1 : Matrix R R ℝ) := by
    ext k l
    simp only [M, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      simp [sgn_mul_sgn hY]
    · rw [horth k k.2 l l.2 (fun h => hkl (Subtype.ext h))]
      simp [hkl]
  have hinv : M * ((n : ℝ)⁻¹ • M.transpose) = 1 := by
    rw [Matrix.mul_smul, hgram, smul_smul, inv_mul_cancel₀ hN, one_smul]
  calc R.card = Fintype.card R := (Fintype.card_coe R).symm
    _ = (1 : Matrix R R ℝ).rank := (Matrix.rank_one (R := ℝ)).symm
    _ = (M * ((n : ℝ)⁻¹ • M.transpose)).rank := by rw [hinv]
    _ ≤ M.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
    _ = n := Fintype.card_fin n

/-- **Antipodal pairing.** Every point has exactly one antipode, and some `n` points with pairwise
orthogonal sign vectors meet every antipodal pair. -/
theorem exists_antipodal_pairing (hn : 1 ≤ n) (hY : IsBinary Y) (hcard : Fintype.card ι = 2 * n)
    (hd : TwoDistance Y) :
    (∀ k, ∃! l, Antipodal Y k l) ∧
      ∃ R : Finset ι, R.card = n ∧
        (∀ k ∈ R, ∀ l ∈ R, k ≠ l → ∑ i, sgn Y k i * sgn Y l i = 0) ∧
        ∀ k, k ∈ R ∨ ∃ r ∈ R, Antipodal Y r k := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let ant : ι → ι := fun k => if h : ∃ l, Antipodal Y k l then h.choose else k
  have hant : ∀ k, (∃ l, Antipodal Y k l) → Antipodal Y k (ant k) := fun k h => by
    simp only [ant, h, ↓reduceDIte]; exact h.choose_spec
  let R := univ.filter fun k => ∀ l, Antipodal Y k l → k < l
  have hRorth : ∀ k ∈ R, ∀ l ∈ R, k ≠ l → ∑ i, sgn Y k i * sgn Y l i = 0 := by
    intro k hk l hl hkl
    refine sum_sgn_mul_sgn_eq_zero hY hd hkl fun ha => ?_
    have h1 := (Finset.mem_filter.mp hk).2 l ha
    have h2 := (Finset.mem_filter.mp hl).2 k (antipodal_symm ha)
    exact lt_asymm h1 h2
  have hRle := card_le_of_orthogonal hn hY R hRorth
  -- points outside `R` have a smaller antipode, which lies in `R`
  have hout : ∀ k ∉ R, Antipodal Y k (ant k) ∧ ant k < k ∧ ant k ∈ R := by
    intro k hk
    simp only [R, Finset.mem_filter, mem_univ, true_and, not_forall, not_lt] at hk
    obtain ⟨l, hl, hlk⟩ := hk
    have ha := hant k ⟨l, hl⟩
    have hl' : ant k = l := antipodal_unique hn hY hd ha hl
    have hlt : ant k < k := lt_of_le_of_ne (hl' ▸ hlk) (fun h => not_antipodal_self hn k (h ▸ ha))
    refine ⟨ha, hlt, Finset.mem_filter.mpr ⟨mem_univ _, fun m hm => ?_⟩⟩
    rw [antipodal_unique hn hY hd hm (antipodal_symm ha)]
    exact hlt
  have hinj : Set.InjOn ant ↑(univ.filter fun k => k ∉ R) := by
    intro k hk k' hk' h
    have a := (hout k (Finset.mem_filter.mp hk).2).1
    have a' := (hout k' (Finset.mem_filter.mp hk').2).1
    rw [← h] at a'
    exact antipodal_unique hn hY hd (antipodal_symm a) (antipodal_symm a')
  have hmaps : ∀ k ∈ univ.filter fun k => k ∉ R, ant k ∈ R :=
    fun k hk => (hout k (Finset.mem_filter.mp hk).2).2.2
  have hcle := Finset.card_le_card_of_injOn ant hmaps hinj
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun k => k ∈ R)
  rw [Finset.card_univ, hcard, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
  have hR : R.card = n := by omega
  -- the injection from the complement onto `R` is onto, so every point of `R` has an antipode
  have hsurj : ∀ r ∈ R, ∃ k ∈ univ.filter fun k => k ∉ R, ant k = r := by
    intro r hr
    exact Finset.surj_on_of_inj_on_of_card_le (fun k hk => ant k) (fun k hk => hmaps k hk)
      (fun a b ha hb h => hinj ha hb h) (by omega) r hr |>.imp fun k ⟨hk, h⟩ => ⟨hk, h.symm⟩
  have hexists : ∀ k, ∃ l, Antipodal Y k l := by
    intro k
    by_cases hk : k ∈ R
    · obtain ⟨k', hk', h⟩ := hsurj k hk
      exact ⟨k', h ▸ antipodal_symm (hout k' (Finset.mem_filter.mp hk').2).1⟩
    · exact ⟨ant k, (hout k hk).1⟩
  refine ⟨fun k => ?_, R, hR, hRorth, fun k => ?_⟩
  · obtain ⟨l, hl⟩ := hexists k
    exact ⟨l, hl, fun l' hl' => antipodal_unique hn hY hd hl' hl⟩
  · by_cases hk : k ∈ R
    · exact Or.inl hk
    · exact Or.inr ⟨ant k, (hout k hk).2.2, antipodal_symm (hout k hk).1⟩

end Stealth

end
