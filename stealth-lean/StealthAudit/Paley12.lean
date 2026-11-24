import StealthAudit.Hadamard

/-!
# C3. The Paley matrix of order 12 (the "explicit integral certificate" of §3)

Let `χ` be the quadratic character of `𝔽₁₁` with `χ(0) = 0`. Index a `12 × 12` matrix `S` by
`{∞} ∪ 𝔽₁₁` (here `Option (ZMod 11)`, with `none` for `∞`): `S ∞ ∞ = 0`, `S ∞ j = 1`,
`S j ∞ = -1`, `S i j = χ(j - i)`. Proved here, by evaluation of the finitely many integer entries
(`decide`, checked by the Lean kernel; no `native_decide`):

* `chi11_eq`: `chi11` is the quadratic character (`0` at `0`, `1` on nonzero squares, `-1`
  otherwise);
* `paleyS_transpose`: `Sᵀ = -S`;
* `paleyS_mul_transpose`: `S Sᵀ = 11 I`;
* `paley12_mul_transpose`: `H Hᵀ = 12 I` for `H = I + S`;
* `paley12_map_sq`, `paley12_entry`: every entry of `H` is `±1`;
* `isHadamard_paley12`: `H` is a Hadamard matrix of order 12.

What this file does NOT prove: Paley's construction for any other prime, and nothing about
stealth; the stealth statements for this matrix are in `Theorem11.lean`.
-/

noncomputable section

namespace Stealth

/-- The quadratic character of `𝔽₁₁`, with `χ(0) = 0`; the nonzero squares are `1, 3, 4, 5, 9`. -/
def chi11 (a : ZMod 11) : ℤ :=
  if a = 0 then 0 else if a = 1 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 9 then 1 else -1

/-- Paley's skew matrix `S`, indexed by `{∞} ∪ 𝔽₁₁`. -/
def paleyS : Matrix (Option (ZMod 11)) (Option (ZMod 11)) ℤ :=
  Matrix.of fun i j =>
    match i, j with
    | none, none => 0
    | none, some _ => 1
    | some _, none => -1
    | some a, some b => chi11 (b - a)

/-- The Paley matrix `H = I + S` of order 12. -/
def paley12 : Matrix (Option (ZMod 11)) (Option (ZMod 11)) ℤ := 1 + paleyS

/-- `chi11` is the quadratic character of `𝔽₁₁`. -/
theorem chi11_eq (a : ZMod 11) :
    chi11 a = if a = 0 then 0 else if ∃ b : ZMod 11, a = b * b then 1 else -1 := by
  revert a
  decide

/-- `Sᵀ = -S`. -/
theorem paleyS_transpose : paleyS.transpose = -paleyS := by
  decide

/-- `S Sᵀ = 11 I`. -/
theorem paleyS_mul_transpose :
    paleyS * paleyS.transpose = (11 : ℤ) • (1 : Matrix (Option (ZMod 11)) (Option (ZMod 11)) ℤ) := by
  decide

/-- `H Hᵀ = 12 I`. -/
theorem paley12_mul_transpose :
    paley12 * paley12.transpose
      = (12 : ℤ) • (1 : Matrix (Option (ZMod 11)) (Option (ZMod 11)) ℤ) := by
  decide

/-- Every entry of `H` has square `1`. -/
theorem paley12_map_sq :
    paley12.map (fun x => x * x) = Matrix.of fun _ _ => (1 : ℤ) := by
  decide

/-- Every entry of `H` is `1` or `-1`. -/
theorem paley12_entry (i j : Option (ZMod 11)) : paley12 i j = 1 ∨ paley12 i j = -1 := by
  have h : paley12 i j * paley12 i j = 1 := congrFun (congrFun paley12_map_sq i) j
  exact mul_self_eq_one_iff.mp h

/-- The Paley matrix of order 12 is a Hadamard matrix. -/
theorem isHadamard_paley12 : IsHadamard paley12 where
  entry := paley12_entry
  mul_transpose := by
    have h : Fintype.card (Option (ZMod 11)) = 12 := by decide
    rw [h]
    exact paley12_mul_transpose

end Stealth

end
