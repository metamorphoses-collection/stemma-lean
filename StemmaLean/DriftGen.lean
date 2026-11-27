/-
Proposition 8.14 of the technical report (`prop:drift`), drift towards the root: the exact
expected supports, as polynomials, and their leading orders.

The tree is `(((1,3),2),4)`, rooted at the vertex joining `{1,2,3}` and `4`, under the attraction
model.  The edges that can innovate are the edge above `{1,3}` (rate `r`), the edge above
`{1,2,3}` (rate `s`), and the pendant edges of `3` (rate `p3`) and `4` (rate `p4`); the pendant
edges of `1` and `2` have rate `0`.  Witnesses `1, 2, 3, 4` are `Fin 4` indices `0, 1, 2, 3`.
Each edge outcome is `0` (no innovation), `1` (attractive reading) or `2` (own reading), with
the probabilities `Quartet.w`; a witness reads the value of the lowest innovating edge above it.
Expected supports are the exact sums over the 81 outcomes.  After the substitution
`r = ρ ε²`, `s = σ ε`, `p3 = b ε`, `p4 = τ ε`, every support is `ε²` times a polynomial in `ε`,
except that of the cluster `{1,2,3}`, which is `ε` times one.
Generated from exact polynomials (`sympy`); every identity is checked by Lean.
-/
import StemmaLean.CodingGen

namespace Stemma.Drift

open Stemma.Quartet

/-- Expected support on the drift tree; `prop` decides from the readings `x₁ … x₄` of witnesses
`1 … 4`.  Edge codes (for own readings): `0` above `{1,3}`, `1` above `{1,2,3}`, `2` pendant of
`3`, `3` pendant of `4`. -/
def suppD (r s p3 p4 α : ℝ) (prop : ℕ → ℕ → ℕ → ℕ → Bool) : ℝ :=
  ∑ e : Fin 3, ∑ h : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    w r α e * w s α h * w p3 α c * w p4 α d *
      (if prop (readBelow 0 1 e h) (readBelow 1 1 0 h)
          (if c ≠ 0 then rd 2 c else readBelow 0 1 e h) (readBelow 3 3 0 d)
        then 1 else 0)

theorem closedD_U12 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.U12 = 2*p3*p4*r*s*α^4 - 3*p3*p4*r*s*α^3 + p3*p4*r*s*α^2 + p3*p4*r*s - p3*p4*r*α^3 + p3*p4*r*α^2 - p3*p4*r + p3*p4*s*α^3 - p3*p4*s*α^2 - p3*p4*s + p3*p4 - p3*r*s*α^3 + 2*p3*r*s*α^2 - p3*r*s - p3*s*α^2 + p3*s := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.U12, Fin.sum_univ_three]; ring

/-- `U12` divided by `ε ^ 2` after the substitution. -/
def gDU12 (ρ σ b τ α ε : ℝ) : ℝ := 2*b*α^4*ε^3*ρ*σ*τ - 3*b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ - b*α^3*ε^2*ρ*τ + b*α^3*ε*σ*τ + b*α^2*ε^3*ρ*σ*τ + 2*b*α^2*ε^2*ρ*σ + b*α^2*ε^2*ρ*τ - b*α^2*ε*σ*τ - b*α^2*σ + b*ε^3*ρ*σ*τ - b*ε^2*ρ*σ - b*ε^2*ρ*τ - b*ε*σ*τ + b*σ + b*τ

theorem scaleD_U12 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.U12 = ε ^ 2 * gDU12 ρ σ b τ α ε := by
  rw [closedD_U12]; unfold gDU12; ring

theorem contD_U12 (ρ σ b τ α : ℝ) : Continuous (gDU12 ρ σ b τ α) := by
  unfold gDU12; fun_prop

theorem zeroD_U12 (ρ σ b τ α : ℝ) : gDU12 ρ σ b τ α 0 = -b*α^2*σ + b*σ + b*τ := by
  unfold gDU12; ring

theorem closedD_U13 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Quartet.U13 = 2*p3*p4*r*s*α^4 - 3*p3*p4*r*s*α^3 + p3*p4*r*s - p3*p4*r*α^3 + 2*p3*p4*r*α^2 - p3*p4*r - p3*r*s*α^3 + 2*p3*r*s*α^2 - p3*r*s + p4*r*s*α^3 - p4*r*α^2 - r*s*α^2 + r := by
  simp [suppD, w, readBelow, rd, Stemma.Quartet.U13, Fin.sum_univ_three]; ring

/-- `U13` divided by `ε ^ 2` after the substitution. -/
def gDU13 (ρ σ b τ α ε : ℝ) : ℝ := 2*b*α^4*ε^3*ρ*σ*τ - 3*b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ - b*α^3*ε^2*ρ*τ + 2*b*α^2*ε^2*ρ*σ + 2*b*α^2*ε^2*ρ*τ + b*ε^3*ρ*σ*τ - b*ε^2*ρ*σ - b*ε^2*ρ*τ + α^3*ε^2*ρ*σ*τ - α^2*ε*ρ*σ - α^2*ε*ρ*τ + ρ

theorem scaleD_U13 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Quartet.U13 = ε ^ 2 * gDU13 ρ σ b τ α ε := by
  rw [closedD_U13]; unfold gDU13; ring

theorem contD_U13 (ρ σ b τ α : ℝ) : Continuous (gDU13 ρ σ b τ α) := by
  unfold gDU13; fun_prop

theorem zeroD_U13 (ρ σ b τ α : ℝ) : gDU13 ρ σ b τ α 0 = ρ := by
  unfold gDU13; ring

theorem closedD_U14 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.U14 = 2*p3*p4*r*s*α^4 - 2*p3*p4*r*s*α^3 - p3*p4*r*α^3 + p3*p4*r*α^2 - p3*r*s*α^3 + p3*r*s*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.U14, Fin.sum_univ_three]; ring

/-- `U14` divided by `ε ^ 2` after the substitution. -/
def gDU14 (ρ σ b τ α ε : ℝ) : ℝ := 2*b*α^4*ε^3*ρ*σ*τ - 2*b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ - b*α^3*ε^2*ρ*τ + b*α^2*ε^2*ρ*σ + b*α^2*ε^2*ρ*τ

theorem scaleD_U14 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.U14 = ε ^ 2 * gDU14 ρ σ b τ α ε := by
  rw [closedD_U14]; unfold gDU14; ring

theorem contD_U14 (ρ σ b τ α : ℝ) : Continuous (gDU14 ρ σ b τ α) := by
  unfold gDU14; fun_prop

theorem zeroD_U14 (ρ σ b τ α : ℝ) : gDU14 ρ σ b τ α 0 = 0 := by
  unfold gDU14; ring

theorem closedD_C12 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C12 = p3*p4*r*s*α^4 - 2*p3*p4*r*s*α^3 + p3*p4*r*s*α^2 + p3*p4*s*α^3 - p3*p4*s*α^2 - p3*r*s*α^3 + 2*p3*r*s*α^2 - p3*r*s - p3*s*α^2 + p3*s := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C12, Fin.sum_univ_three]; ring

/-- `C12` divided by `ε ^ 2` after the substitution. -/
def gDC12 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - 2*b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ + b*α^3*ε*σ*τ + b*α^2*ε^3*ρ*σ*τ + 2*b*α^2*ε^2*ρ*σ - b*α^2*ε*σ*τ - b*α^2*σ - b*ε^2*ρ*σ + b*σ

theorem scaleD_C12 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C12 = ε ^ 2 * gDC12 ρ σ b τ α ε := by
  rw [closedD_C12]; unfold gDC12; ring

theorem contD_C12 (ρ σ b τ α : ℝ) : Continuous (gDC12 ρ σ b τ α) := by
  unfold gDC12; fun_prop

theorem zeroD_C12 (ρ σ b τ α : ℝ) : gDC12 ρ σ b τ α 0 = -b*α^2*σ + b*σ := by
  unfold gDC12; ring

theorem closedD_C13 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C13 = p3*p4*r*s*α^4 - p3*p4*r*s*α^3 - p3*p4*r*α^3 + p3*p4*r*α^2 - p3*r*s*α^3 + p3*r*s*α^2 + p3*r*α^2 - p3*r + p4*r*s*α^3 - p4*r*α^2 - r*s*α^2 + r := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C13, Fin.sum_univ_three]; ring

/-- `C13` divided by `ε ^ 2` after the substitution. -/
def gDC13 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ - b*α^3*ε^2*ρ*τ + b*α^2*ε^2*ρ*σ + b*α^2*ε^2*ρ*τ + b*α^2*ε*ρ - b*ε*ρ + α^3*ε^2*ρ*σ*τ - α^2*ε*ρ*σ - α^2*ε*ρ*τ + ρ

theorem scaleD_C13 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C13 = ε ^ 2 * gDC13 ρ σ b τ α ε := by
  rw [closedD_C13]; unfold gDC13; ring

theorem contD_C13 (ρ σ b τ α : ℝ) : Continuous (gDC13 ρ σ b τ α) := by
  unfold gDC13; fun_prop

theorem zeroD_C13 (ρ σ b τ α : ℝ) : gDC13 ρ σ b τ α 0 = ρ := by
  unfold gDC13; ring

theorem closedD_C14 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C14 = p3*p4*r*s*α^4 - p3*p4*r*s*α^3 - p3*p4*r*α^3 + p3*p4*r*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C14, Fin.sum_univ_three]; ring

/-- `C14` divided by `ε ^ 2` after the substitution. -/
def gDC14 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*τ + b*α^2*ε^2*ρ*τ

theorem scaleD_C14 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C14 = ε ^ 2 * gDC14 ρ σ b τ α ε := by
  rw [closedD_C14]; unfold gDC14; ring

theorem contD_C14 (ρ σ b τ α : ℝ) : Continuous (gDC14 ρ σ b τ α) := by
  unfold gDC14; fun_prop

theorem zeroD_C14 (ρ σ b τ α : ℝ) : gDC14 ρ σ b τ α 0 = 0 := by
  unfold gDC14; ring

theorem closedD_C23 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C23 = p3*p4*r*s*α^4 - p3*p4*r*s*α^3 - p3*r*s*α^3 + p3*r*s*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C23, Fin.sum_univ_three]; ring

/-- `C23` divided by `ε ^ 2` after the substitution. -/
def gDC23 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - b*α^3*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*σ + b*α^2*ε^2*ρ*σ

theorem scaleD_C23 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C23 = ε ^ 2 * gDC23 ρ σ b τ α ε := by
  rw [closedD_C23]; unfold gDC23; ring

theorem contD_C23 (ρ σ b τ α : ℝ) : Continuous (gDC23 ρ σ b τ α) := by
  unfold gDC23; fun_prop

theorem zeroD_C23 (ρ σ b τ α : ℝ) : gDC23 ρ σ b τ α 0 = 0 := by
  unfold gDC23; ring

theorem closedD_C24 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C24 = p3*p4*r*s*α^4 - p3*p4*r*s*α^3 - p4*r*s*α^3 + p4*r*s*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C24, Fin.sum_univ_three]; ring

/-- `C24` divided by `ε ^ 2` after the substitution. -/
def gDC24 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - b*α^3*ε^3*ρ*σ*τ - α^3*ε^2*ρ*σ*τ + α^2*ε^2*ρ*σ*τ

theorem scaleD_C24 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C24 = ε ^ 2 * gDC24 ρ σ b τ α ε := by
  rw [closedD_C24]; unfold gDC24; ring

theorem contD_C24 (ρ σ b τ α : ℝ) : Continuous (gDC24 ρ σ b τ α) := by
  unfold gDC24; fun_prop

theorem zeroD_C24 (ρ σ b τ α : ℝ) : gDC24 ρ σ b τ α 0 = 0 := by
  unfold gDC24; ring

theorem closedD_C34 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C34 = p3*p4*r*s*α^4 - p3*p4*r*α^3 - p3*p4*s*α^3 + p3*p4*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C34, Fin.sum_univ_three]; ring

/-- `C34` divided by `ε ^ 2` after the substitution. -/
def gDC34 (ρ σ b τ α ε : ℝ) : ℝ := b*α^4*ε^3*ρ*σ*τ - b*α^3*ε^2*ρ*τ - b*α^3*ε*σ*τ + b*α^2*τ

theorem scaleD_C34 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C34 = ε ^ 2 * gDC34 ρ σ b τ α ε := by
  rw [closedD_C34]; unfold gDC34; ring

theorem contD_C34 (ρ σ b τ α : ℝ) : Continuous (gDC34 ρ σ b τ α) := by
  unfold gDC34; fun_prop

theorem zeroD_C34 (ρ σ b τ α : ℝ) : gDC34 ρ σ b τ α 0 = b*α^2*τ := by
  unfold gDC34; ring

theorem closedD_C123 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C123 = -p3*p4*r*s*α^4 + 2*p3*p4*r*s*α^3 - p3*p4*r*s*α^2 - p3*p4*s*α^3 + p3*p4*s*α^2 + p3*r*s*α^3 - 2*p3*r*s*α^2 + p3*r*s + p3*s*α^2 - p3*s - p4*r*s*α^3 + p4*r*s*α^2 - p4*s*α^2 + r*s*α^2 - r*s + s := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C123, Fin.sum_univ_three]; ring

/-- `C123` divided by `ε` after the substitution. -/
def gDC123 (ρ σ b τ α ε : ℝ) : ℝ := -b*α^4*ε^4*ρ*σ*τ + 2*b*α^3*ε^4*ρ*σ*τ + b*α^3*ε^3*ρ*σ - b*α^3*ε^2*σ*τ - b*α^2*ε^4*ρ*σ*τ - 2*b*α^2*ε^3*ρ*σ + b*α^2*ε^2*σ*τ + b*α^2*ε*σ + b*ε^3*ρ*σ - b*ε*σ - α^3*ε^3*ρ*σ*τ + α^2*ε^3*ρ*σ*τ + α^2*ε^2*ρ*σ - α^2*ε*σ*τ - ε^2*ρ*σ + σ

theorem scaleD_C123 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C123 = ε * gDC123 ρ σ b τ α ε := by
  rw [closedD_C123]; unfold gDC123; ring

theorem contD_C123 (ρ σ b τ α : ℝ) : Continuous (gDC123 ρ σ b τ α) := by
  unfold gDC123; fun_prop

theorem zeroD_C123 (ρ σ b τ α : ℝ) : gDC123 ρ σ b τ α 0 = σ := by
  unfold gDC123; ring

theorem closedD_C124 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C124 = -p3*p4*r*s*α^4 + 2*p3*p4*r*s*α^3 - p3*p4*r*s*α^2 - p3*p4*s*α^3 + p3*p4*s*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C124, Fin.sum_univ_three]; ring

/-- `C124` divided by `ε ^ 2` after the substitution. -/
def gDC124 (ρ σ b τ α ε : ℝ) : ℝ := -b*α^4*ε^3*ρ*σ*τ + 2*b*α^3*ε^3*ρ*σ*τ - b*α^3*ε*σ*τ - b*α^2*ε^3*ρ*σ*τ + b*α^2*ε*σ*τ

theorem scaleD_C124 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C124 = ε ^ 2 * gDC124 ρ σ b τ α ε := by
  rw [closedD_C124]; unfold gDC124; ring

theorem contD_C124 (ρ σ b τ α : ℝ) : Continuous (gDC124 ρ σ b τ α) := by
  unfold gDC124; fun_prop

theorem zeroD_C124 (ρ σ b τ α : ℝ) : gDC124 ρ σ b τ α 0 = 0 := by
  unfold gDC124; ring

theorem closedD_C134 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C134 = -p3*p4*r*s*α^4 + p3*p4*r*s*α^3 + p3*p4*r*α^3 - p3*p4*r*α^2 - p4*r*s*α^3 + p4*r*α^2 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C134, Fin.sum_univ_three]; ring

/-- `C134` divided by `ε ^ 2` after the substitution. -/
def gDC134 (ρ σ b τ α ε : ℝ) : ℝ := -b*α^4*ε^3*ρ*σ*τ + b*α^3*ε^3*ρ*σ*τ + b*α^3*ε^2*ρ*τ - b*α^2*ε^2*ρ*τ - α^3*ε^2*ρ*σ*τ + α^2*ε*ρ*τ

theorem scaleD_C134 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C134 = ε ^ 2 * gDC134 ρ σ b τ α ε := by
  rw [closedD_C134]; unfold gDC134; ring

theorem contD_C134 (ρ σ b τ α : ℝ) : Continuous (gDC134 ρ σ b τ α) := by
  unfold gDC134; fun_prop

theorem zeroD_C134 (ρ σ b τ α : ℝ) : gDC134 ρ σ b τ α 0 = 0 := by
  unfold gDC134; ring

theorem closedD_C234 (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α Stemma.Coding.C234 = -p3*p4*r*s*α^4 + p3*p4*r*s*α^3 := by
  simp [suppD, w, readBelow, rd, Stemma.Coding.C234, Fin.sum_univ_three]; ring

/-- `C234` divided by `ε ^ 2` after the substitution. -/
def gDC234 (ρ σ b τ α ε : ℝ) : ℝ := -b*α^4*ε^3*ρ*σ*τ + b*α^3*ε^3*ρ*σ*τ

theorem scaleD_C234 (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Stemma.Coding.C234 = ε ^ 2 * gDC234 ρ σ b τ α ε := by
  rw [closedD_C234]; unfold gDC234; ring

theorem contD_C234 (ρ σ b τ α : ℝ) : Continuous (gDC234 ρ σ b τ α) := by
  unfold gDC234; fun_prop

theorem zeroD_C234 (ρ σ b τ α : ℝ) : gDC234 ρ σ b τ α 0 = 0 := by
  unfold gDC234; ring

end Stemma.Drift
