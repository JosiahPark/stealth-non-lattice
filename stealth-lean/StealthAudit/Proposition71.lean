import StealthAudit.FormalDualPeriods
import StealthAudit.PeriodicDensity
import StealthAudit.Theorem11

/-!
# H5. Proposition 7.1 (no ordinary periodic formal dual)

**Proposition 7.1.** None of the configurations `P_n = C_n + 2ℤⁿ`, `n = 10, 11, 12`, has an ordinary
periodic formal dual among simple equally weighted periodic configurations.

Here formal duality is `FormallyDual` of H2, which is the pair-coefficient characterization of formal
duality of periodic configurations from Cohn, Kumar, Reiher and Schürmann, taken as the DEFINITION. Its
equivalence with their analytic definition (Poisson-type summation over Schwartz functions) is NOT
formalized, so this is Proposition 7.1 for that definition.

Proof (§7, with the support `½ℤⁿ` in place of the paper's `ℤⁿ`). Let `Q` be a formal dual of
`X + 2ℤⁿ`, `X` binary with `N` points. Two points of `Q` differ by a vector of `½ℤⁿ` (H2), and every
`u ∈ ℤⁿ` is a period of `Q` (H3), so `density Q = m` is a natural number (H4). Condition (i) of formal
duality says `(N / 2ⁿ) · m = 1`, that is `N · m = 2ⁿ`, so `N ∣ 2ⁿ`. For `N = 24` this is impossible
(G3).

Proved here: `card_mul_density_of_formallyDual`, `card_dvd_two_pow_of_formallyDual` (a binary motif
with a formal dual has a power-of-two divisor as its number of points: `N ∣ 2ⁿ`), `proposition_7_1`,
`proposition_7_1_paley` (for the motifs of `theorem_1_1`).

What this file does NOT prove: the equivalence of `FormallyDual` with the analytic definition of
formal duality, or anything about weighted or radial formal duals (the paper claims nothing there).
-/

noncomputable section

namespace Stealth

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- For binary `X` with a formal dual `Q`, `N · m = 2ⁿ` with `m = density Q ∈ ℕ`. -/
theorem card_mul_density_of_formallyDual {X : ι → Fin n → ℝ} (hX : IsBinary X)
    {Q : PeriodicConfig n} (h : FormallyDual X Q) :
    ∃ m : ℕ, Fintype.card ι * m = 2 ^ n := by
  obtain ⟨m, hm⟩ := Q.density_eq_nat (fun u x hx => int_period_of_formallyDual hX h u x hx)
    (fun x y hx hy => formallyDual_support h hx hy)
  refine ⟨m, ?_⟩
  have h1 := h.density_mul
  rw [hm, density] at h1
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h3 : ((Fintype.card ι * m : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    field_simp at h1
    linarith
  exact_mod_cast h3

/-- A binary motif with a formal dual has `N ∣ 2ⁿ`. -/
theorem card_dvd_two_pow_of_formallyDual {X : ι → Fin n → ℝ} (hX : IsBinary X)
    {Q : PeriodicConfig n} (h : FormallyDual X Q) : Fintype.card ι ∣ 2 ^ n := by
  obtain ⟨m, hm⟩ := card_mul_density_of_formallyDual hX h
  exact ⟨m, hm.symm⟩

/-- **Proposition 7.1** (for the pair-coefficient definition of formal duality, H2): a binary motif
with `24` points has no formal dual, in any dimension. -/
theorem proposition_7_1 {X : ι → Fin n → ℝ} (hX : IsBinary X) (hN : Fintype.card ι = 24)
    (Q : PeriodicConfig n) : ¬ FormallyDual X Q := by
  intro h
  have := card_dvd_two_pow_of_formallyDual hX h
  rw [hN] at this
  exact not_twentyfour_dvd_two_pow n this

/-- **Proposition 7.1** for the configurations of Theorem 1.1: for `n = 10, 11, 12` there is a binary
motif `X` of 24 points, distinct modulo `2ℤⁿ`, with `K = 1` and `Δ_st = 1/24`, such that `X + 2ℤⁿ`
has no formal dual. -/
theorem proposition_7_1_paley (n : ℕ) (hn : n = 10 ∨ n = 11 ∨ n = 12) :
    ∃ X : Fin 24 → Fin n → ℝ, IsBinary X ∧ DistinctModPeriod X ∧ stealthRadius X = 1 ∧
      centerDensity X = 1 / 24 ∧ ∀ Q : PeriodicConfig n, ¬ FormallyDual X Q := by
  obtain ⟨X, hb, hd, hK, -, hΔ⟩ := theorem_1_1 n hn
  exact ⟨X, hb, hd, hK, hΔ, fun Q => proposition_7_1 hb (by simp) Q⟩

end Stealth

end
