import StealthAudit.TraceFreeSign
import StealthAudit.BinaryMotif
import StealthAudit.Marginals

/-!
# F2. Amplitudes on the test vectors

For a binary motif `X` of strength three with `N ≡ 8 (mod 16)`, every test vector `v` of §6 (F1) is a
surviving frequency: `a_X(v) ≠ 0`.

* For `v = 2eᵢ`: `a_X(2eᵢ) = N` (`amp_two_mul_single` of B1), and `N ≠ 0`.
* For `v` with entries `±1` on a 4-set `I` and `0` elsewhere: the odd support of `v` is `I`, so
  `a_X(v)` is the character sum of weight four on `I` (`amp_of_isBinary` of B1), which is nonzero by
  `charSum_ne_zero_of_card_mod_sixteen` (B3).

Proved here: `oddSupp_eq_of_testVector`, `amp_testVector_ne_zero`, `testVector_ne_zero`,
`survives_of_mem_testVectors`.

What this file does NOT prove: the rest of Lemma 6.1 or Theorem 1.3 (items F3–F5).
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι] {X : ι → Fin n → ℝ}

/-- The odd support of a `±1` vector on `I` (zero elsewhere) is `I`. -/
theorem oddSupp_eq_of_testVector {v : Fin n → ℤ} {I : Finset (Fin n)}
    (hI : ∀ i ∈ I, v i = 1 ∨ v i = -1) (hout : ∀ i ∉ I, v i = 0) : oddSupp v = I := by
  ext i
  rw [mem_oddSupp]
  by_cases hi : i ∈ I
  · simp only [hi, iff_true]
    rcases hI i hi with h | h <;> rw [h] <;> decide
  · simp only [hi, iff_false, hout i hi]
    decide

/-- **F2.** Every test vector has nonzero amplitude for a binary motif of strength three with
`N ≡ 8 (mod 16)`. -/
theorem amp_testVector_ne_zero (hX : IsBinary X) (hs : HasStrength X 3)
    (hN : Fintype.card ι % 16 = 8) {v : Fin n → ℤ} (hv : v ∈ testVectors n) : amp X v ≠ 0 := by
  rcases hv with ⟨i, rfl⟩ | ⟨I, hcard, hI, hout⟩
  · rw [amp_two_mul_single hX]
    have : Fintype.card ι ≠ 0 := by omega
    exact_mod_cast this
  · rw [amp_of_isBinary hX, oddSupp_eq_of_testVector hI hout]
    exact_mod_cast charSum_ne_zero_of_card_mod_sixteen hX hs hN I hcard

omit [Fintype ι] in
/-- Test vectors are nonzero. -/
theorem testVector_ne_zero {v : Fin n → ℤ} (hv : v ∈ testVectors n) : v ≠ 0 := by
  rcases hv with ⟨i, rfl⟩ | ⟨I, hcard, hI, -⟩
  · intro h
    have := congrFun h i
    simp at this
  · intro h
    obtain ⟨i, hi⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
    rcases hI i hi with h1 | h1 <;> simp [h] at h1

theorem survives_of_mem_testVectors (hX : IsBinary X) (hs : HasStrength X 3)
    (hN : Fintype.card ι % 16 = 8) {v : Fin n → ℤ} (hv : v ∈ testVectors n) : Survives X v :=
  ⟨testVector_ne_zero hv, amp_testVector_ne_zero hX hs hN hv⟩

end Stealth

end
