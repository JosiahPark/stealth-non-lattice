import StealthAudit.BinaryMotif

/-!
# G3. The arithmetic of Proposition 7.1

Proposition 7.1 of the paper (no ordinary periodic formal dual) is NOT proved here: this library
has no definition of formal duality. This file checks the two computations its proof uses:

* `amp_two_mul`: for a binary motif `X`, `a_X(2u) = N` for every integer `u` (in the proof: "the
  Fourier-side pair coefficient equals one, since `a_{C_n}(2u) = 24`");
* `not_twentyfour_dvd_two_pow`: `24` does not divide `2ⁿ`;
* `two_pow_div_twentyfour_not_int`: `2ⁿ / 24` is not an integer (in the proof: `ρ(Q) = 2ⁿ/24` is
  not an integer), for every `n`, in particular for `n = 10, 11, 12`.

What this file does NOT prove: Proposition 7.1, or any statement about pair correlations or
formal duals.
-/

noncomputable section

open Finset

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- For a binary motif, `a_X(2u) = N` for every integer vector `u`. -/
theorem amp_two_mul {X : ι → Fin n → ℝ} (hX : IsBinary X) (u : Fin n → ℤ) :
    amp X (fun i => 2 * u i) = (Fintype.card ι : ℂ) := by
  rw [amp_of_isBinary hX]
  have h : oddSupp (fun i : Fin n => 2 * u i) = ∅ := by
    ext i
    simp
  rw [h]
  simp [charSum]

/-- `24` does not divide `2ⁿ`. -/
theorem not_twentyfour_dvd_two_pow (n : ℕ) : ¬ (24 ∣ 2 ^ n) := by
  intro h
  have h3 : 3 ∣ 2 ^ n := Dvd.dvd.trans (by norm_num) h
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

/-- `2ⁿ / 24` is not an integer. -/
theorem two_pow_div_twentyfour_not_int (n : ℕ) : ¬ ∃ m : ℤ, (2 : ℝ) ^ n / 24 = (m : ℝ) := by
  rintro ⟨m, hm⟩
  have h1 : ((2 ^ n : ℤ) : ℝ) = ((24 * m : ℤ) : ℝ) := by
    push_cast
    field_simp at hm
    linarith
  have h2 : (2 ^ n : ℤ) = 24 * m := by exact_mod_cast h1
  have hm0 : 0 ≤ m := by
    by_contra hneg
    have : (0 : ℤ) < 2 ^ n := by positivity
    omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  exact not_twentyfour_dvd_two_pow n ⟨k, by exact_mod_cast h2⟩

end Stealth

end
