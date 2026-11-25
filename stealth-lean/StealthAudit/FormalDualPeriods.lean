import StealthAudit.FormalDuality
import StealthAudit.FormalDualityArithmetic

/-!
# H3. Integer vectors are periods of a formal dual

Let `X` be a binary motif and `Q` a formal dual of `P = X + 2ℤⁿ` in the sense of H2. For every
`u ∈ ℤⁿ`, condition (ii) at `t = u` (so `2t = 2u`) and `a_X(2u) = N` (G3) give `pairCoeff Q u = 1`; by
H1 this says that `u` is a period of `Q`. In the paper: "for each `u ∈ ℤⁿ`, the Fourier-side pair
coefficient equals one, since `a_{C_n}(2u) = 24` … equality to one forces `u` to be a period".

Proved here: `card_pos_of_formallyDual`, `pairCoeff_int_of_formallyDual`, `int_period_of_formallyDual`.

What this file does NOT prove: that the density of `Q` is an integer (item H4), or Proposition 7.1 (H5).
-/

noncomputable section

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A motif with a formal dual is nonempty: otherwise `ρ(P) ρ(Q) = 0`. -/
theorem card_pos_of_formallyDual {X : ι → Fin n → ℝ} {Q : PeriodicConfig n} (h : FormallyDual X Q) :
    0 < Fintype.card ι := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · have := h.density_mul
    rw [density, h0] at this
    simp at this
  · exact h0

/-- For binary `X`, every integer vector has pair coefficient one in a formal dual. -/
theorem pairCoeff_int_of_formallyDual {X : ι → Fin n → ℝ} (hX : IsBinary X) {Q : PeriodicConfig n}
    (h : FormallyDual X Q) (u : Fin n → ℤ) : Q.pairCoeff (fun i => (u i : ℝ)) = 1 := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast card_pos_of_formallyDual h
  rw [h.pair_of_half _ (fun i => 2 * u i) (fun i => by push_cast; ring), amp_two_mul hX u,
    Complex.norm_natCast]
  exact div_self (by positivity)

/-- **Integer periods.** For binary `X`, every `u ∈ ℤⁿ` is a period of a formal dual `Q` of
`X + 2ℤⁿ`. -/
theorem int_period_of_formallyDual {X : ι → Fin n → ℝ} (hX : IsBinary X) {Q : PeriodicConfig n}
    (h : FormallyDual X Q) (u : Fin n → ℤ) (x : Fin n → ℝ) (hx : Q.mem x) :
    Q.mem (x + fun i => (u i : ℝ)) :=
  (Q.pairCoeff_eq_one_iff _).mp (pairCoeff_int_of_formallyDual hX h u) x hx

end Stealth

end
