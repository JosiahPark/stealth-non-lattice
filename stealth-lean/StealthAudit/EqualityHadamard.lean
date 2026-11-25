import StealthAudit.EqualityPairing

/-!
# D8b. From a two-distance binary code to an antipodal Hadamard array (D8)

Let `Y : ι → Fin n → ℝ` be a binary motif with `N = 2n` points, `n ≥ 1`, any two distinct points
differing in exactly `n` or exactly `n/2` coordinates (`TwoDistance Y`). By D8a there is a set `R` of `n`
points with pairwise orthogonal sign vectors `sₖ = 1 − 2Yₖ`, and every point is in `R` or is the unique
antipode of a point of `R`. Indexing `R` by `Fin n`, the sign vectors of `R` are the rows of a Hadamard
matrix `H`, and `(r, false) ↦ rₖ`, `(r, true) ↦ antipode of rₖ` is a bijection `Fin n × Bool ≃ ι`
carrying the antipodal array of `H` (C2) onto `Y`.

Proved here:

* `signRow`, `signRow_cast`: the integer `±1` matrix of sign vectors;
* `isHadamard_signRow`: it is a Hadamard matrix;
* `equality_hadamard`: **D8.** There are a Hadamard matrix `H : Matrix (Fin n) (Fin n) ℤ` and a
  bijection `e : Fin n × Bool ≃ ι` with `Y (e p) = antipodalMotif H id p` for every `p`.

What this file does NOT prove: Theorem 1.2 itself, which needs the passage from `GapAtLeast X 4` to a
binary two-distance motif (D7, after translating and reducing modulo 2) and the converse (item D9).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι] {Y : ι → Fin n → ℝ}

/-- The integer sign matrix of a family of points `rep : Fin n → ι`. -/
def signRow (Y : ι → Fin n → ℝ) (rep : Fin n → ι) : Matrix (Fin n) (Fin n) ℤ :=
  fun r i => if Y (rep r) i = 0 then 1 else -1

omit [Fintype ι] in
theorem signRow_cast (hY : IsBinary Y) (rep : Fin n → ι) (r i : Fin n) :
    ((signRow Y rep r i : ℤ) : ℝ) = sgn Y (rep r) i := by
  unfold signRow sgn
  rcases hY (rep r) i with h | h <;> norm_num [h]

omit [Fintype ι] in
/-- Sign rows of pairwise orthogonal points form a Hadamard matrix. -/
theorem isHadamard_signRow (hY : IsBinary Y) (rep : Fin n → ι)
    (horth : ∀ r r', r ≠ r' → ∑ i, sgn Y (rep r) i * sgn Y (rep r') i = 0) :
    IsHadamard (signRow Y rep) := by
  refine ⟨fun r i => by unfold signRow; split_ifs <;> simp, ?_⟩
  ext r r'
  apply Int.cast_injective (α := ℝ)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    Fintype.card_fin, smul_eq_mul]
  push_cast
  simp only [signRow_cast hY]
  by_cases h : r = r'
  · subst h
    simp [sgn_mul_sgn hY]
  · rw [horth r r' h]
    simp [h]

/-- **D8.** A binary motif with `2n` points and pairwise Hamming distances `n` or `n/2` is, after
relabelling, the antipodal array of a Hadamard matrix of order `n`. -/
theorem equality_hadamard (hn : 1 ≤ n) (hY : IsBinary Y) (hcard : Fintype.card ι = 2 * n)
    (hd : TwoDistance Y) :
    ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHadamard H ∧
      ∃ e : Fin n × Bool ≃ ι, ∀ p, Y (e p) = antipodalMotif H id p := by
  classical
  obtain ⟨hant, R, hR, hRorth, hcover⟩ := exists_antipodal_pairing hn hY hcard hd
  choose ant hantS hantU using hant
  -- `ant` is an involution
  have hantant : ∀ k, ant (ant k) = k := fun k =>
    (hantU (ant k) k (antipodal_symm (hantS k))).symm
  let eR : R ≃ Fin n := R.equivFinOfCardEq hR
  let rep : Fin n → ι := fun r => (eR.symm r : ι)
  have hrepR : ∀ r, rep r ∈ R := fun r => (eR.symm r).2
  have hrep : Function.Injective rep := fun a b h => eR.symm.injective (Subtype.ext h)
  have horth : ∀ r r', r ≠ r' → ∑ i, sgn Y (rep r) i * sgn Y (rep r') i = 0 :=
    fun r r' h => hRorth _ (hrepR r) _ (hrepR r') (fun h' => h (hrep h'))
  -- an antipode of a point of `R` is not in `R`
  have hantR : ∀ k ∈ R, ant k ∉ R := by
    intro k hk hak
    have hne : k ≠ ant k := fun h => not_antipodal_self hn k (by
      have := hantS k; rwa [← h] at this)
    have h0 := hRorth k hk (ant k) hak hne
    rw [sum_sgn_mul_sgn hY, (hamming_eq_iff_antipodal k (ant k)).mpr (hantS k)] at h0
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let f : Fin n × Bool → ι := fun p => if p.2 then ant (rep p.1) else rep p.1
  have hf : Function.Injective f := by
    rintro ⟨r, b⟩ ⟨r', b'⟩ h
    cases b <;> cases b' <;> simp only [f, Bool.false_eq_true, ite_true, ite_false] at h
    · rw [hrep h]
    · exact absurd (h ▸ hrepR r) (hantR _ (hrepR r'))
    · exact absurd (h ▸ hrepR r') (hantR _ (hrepR r))
    · have := congrArg ant h
      rw [hantant, hantant] at this
      rw [hrep this]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    simp [hcard, mul_comm]
  refine ⟨signRow Y rep, isHadamard_signRow hY rep horth, Equiv.ofBijective f hbij, ?_⟩
  rintro ⟨r, b⟩
  funext i
  simp only [Equiv.ofBijective_apply, f, antipodalMotif_apply, id, signRow_cast hY, sgn]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    ring
  · simp only [ite_true]
    have hdiff := hantS (rep r) i
    rcases hY (rep r) i with h | h <;> rcases hY (ant (rep r)) i with h' | h' <;>
      simp_all
    all_goals norm_num

end Stealth

end
