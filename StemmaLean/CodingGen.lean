/-
Theorem 4.7 of the mathematical paper, complete: the leading-order consistency boundaries of the
unrooted and rooted codings on the quartet under the attraction model.

Setting: `p₂ = p₄ = 0`, halves of rate `r = ρ ε²`, pendant rates `p₁ = a ε`, `p₃ = b ε`.
(a) Unrooted coding: if `a b < 2ρ` the true split `12|34` has the largest expected support for
    all sufficiently small `ε > 0`; if `a b > 2ρ` the false split `13|24` does.
(b) Rooted coding: if `α² a b < 2ρ` the true clusters `{12, 34}` form the unique maximum-weight
    laminar family for all sufficiently small `ε > 0`; if `α² a b > 2ρ` the single cluster `{1,3}`
    outweighs them.
Expected supports are the exact sums over the 81 edge outcomes (`Stemma.Quartet.suppA`).
Generated from exact polynomials; every identity is checked by Lean.
-/
import StemmaLean.Quartet

open Filter Topology

namespace Stemma.Coding

open Stemma.Quartet

def U12 (x1 x2 x3 x4 : ℕ) : Bool := (x2 == x1 && x3 != x1 && x4 != x1) || (x4 == x3 && x1 != x3 && x2 != x3)
def U14 (x1 x2 x3 x4 : ℕ) : Bool := (x4 == x1 && x2 != x1 && x3 != x1) || (x3 == x2 && x1 != x2 && x4 != x2)
def C12 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x2 == x1 && x3 != x1 && x4 != x1)
def C13 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x3 == x1 && x2 != x1 && x4 != x1)
def C14 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x4 == x1 && x2 != x1 && x3 != x1)
def C23 (x1 x2 x3 x4 : ℕ) : Bool := (x2 != 0 && x3 == x2 && x1 != x2 && x4 != x2)
def C24 (x1 x2 x3 x4 : ℕ) : Bool := (x2 != 0 && x4 == x2 && x1 != x2 && x3 != x2)
def C34 (x1 x2 x3 x4 : ℕ) : Bool := (x3 != 0 && x4 == x3 && x1 != x3 && x2 != x3)
def C123 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x2 == x1 && x3 == x1 && x4 != x1)
def C124 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x2 == x1 && x4 == x1 && x3 != x1)
def C134 (x1 x2 x3 x4 : ℕ) : Bool := (x1 != 0 && x3 == x1 && x4 == x1 && x2 != x1)
def C234 (x1 x2 x3 x4 : ℕ) : Bool := (x2 != 0 && x3 == x2 && x4 == x2 && x1 != x2)

theorem closed_U12 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α U12 = 2*α^4*p1*p3*r^2 - 4*α^3*p1*p3*r^2 - 2*α^3*p1*p3*r + α^3*p1*r^2 + α^3*p3*r^2 + α^2*p1*p3*r^2 + 4*α^2*p1*p3*r - α^2*p1*r - α^2*p3*r - α^2*r^2 + p1*p3*r^2 - 2*p1*p3*r - r^2 + 2*r := by
  simp [suppA, w, readBelow, rd, U12, Fin.sum_univ_three]; ring

theorem closed_U13 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α Stemma.Quartet.U13 = 2*α^4*p1*p3*r^2 - 2*α^3*p1*p3*r^2 - 2*α^3*p1*p3*r + 2*α^2*p1*p3*r + p1*p3*r^2 - 2*p1*p3*r + p1*p3 := by
  simp [suppA, w, readBelow, rd, Stemma.Quartet.U13, Fin.sum_univ_three]; ring

theorem closed_U14 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α U14 = 2*α^4*p1*p3*r^2 - 2*α^3*p1*p3*r^2 - 2*α^3*p1*p3*r + 2*α^2*p1*p3*r := by
  simp [suppA, w, readBelow, rd, U14, Fin.sum_univ_three]; ring

theorem closed_R12 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C12 = α^4*p1*p3*r^2 - α^3*p1*p3*r^2 - α^3*p1*p3*r - α^3*p1*r^2 + α^3*p3*r^2 + α^2*p1*p3*r + α^2*p1*r^2 + α^2*p1*r - α^2*p3*r - α^2*r^2 - p1*r + r := by
  simp [suppA, w, readBelow, rd, C12, Fin.sum_univ_three]; ring

theorem closed_R13 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C13 = α^4*p1*p3*r^2 - 2*α^3*p1*p3*r + α^2*p1*p3 := by
  simp [suppA, w, readBelow, rd, C13, Fin.sum_univ_three]; ring

theorem closed_R14 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C14 = α^4*p1*p3*r^2 - α^3*p1*p3*r^2 - α^3*p1*p3*r + α^2*p1*p3*r := by
  simp [suppA, w, readBelow, rd, C14, Fin.sum_univ_three]; ring

theorem closed_R23 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C23 = α^4*p1*p3*r^2 - α^3*p1*p3*r^2 - α^3*p1*p3*r + α^2*p1*p3*r := by
  simp [suppA, w, readBelow, rd, C23, Fin.sum_univ_three]; ring

theorem closed_R24 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C24 = α^4*p1*p3*r^2 - 2*α^3*p1*p3*r^2 + α^2*p1*p3*r^2 := by
  simp [suppA, w, readBelow, rd, C24, Fin.sum_univ_three]; ring

theorem closed_R34 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C34 = α^4*p1*p3*r^2 - α^3*p1*p3*r^2 - α^3*p1*p3*r + α^3*p1*r^2 - α^3*p3*r^2 + α^2*p1*p3*r - α^2*p1*r + α^2*p3*r^2 + α^2*p3*r - α^2*r^2 - p3*r + r := by
  simp [suppA, w, readBelow, rd, C34, Fin.sum_univ_three]; ring

theorem closed_R123 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C123 = -α^4*p1*p3*r^2 + α^3*p1*p3*r^2 + α^3*p1*p3*r - α^3*p3*r^2 - α^2*p1*p3*r + α^2*p3*r := by
  simp [suppA, w, readBelow, rd, C123, Fin.sum_univ_three]; ring

theorem closed_R124 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C124 = -α^4*p1*p3*r^2 + 2*α^3*p1*p3*r^2 - α^3*p3*r^2 - α^2*p1*p3*r^2 + α^2*p3*r^2 := by
  simp [suppA, w, readBelow, rd, C124, Fin.sum_univ_three]; ring

theorem closed_R134 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C134 = -α^4*p1*p3*r^2 + α^3*p1*p3*r^2 + α^3*p1*p3*r - α^3*p1*r^2 - α^2*p1*p3*r + α^2*p1*r := by
  simp [suppA, w, readBelow, rd, C134, Fin.sum_univ_three]; ring

theorem closed_R234 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α C234 = -α^4*p1*p3*r^2 + 2*α^3*p1*p3*r^2 - α^3*p1*r^2 - α^2*p1*p3*r^2 + α^2*p1*r^2 := by
  simp [suppA, w, readBelow, rd, C234, Fin.sum_univ_three]; ring

/-- `U12` divided by `ε²` after the substitution. -/
def gU12 (ρ a b α ε : ℝ) : ℝ := 2*a*α^4*b*ε^4*ρ^2 - 4*a*α^3*b*ε^4*ρ^2 - 2*a*α^3*b*ε^2*ρ + a*α^3*ε^3*ρ^2 + a*α^2*b*ε^4*ρ^2 + 4*a*α^2*b*ε^2*ρ - a*α^2*ε*ρ + a*b*ε^4*ρ^2 - 2*a*b*ε^2*ρ + α^3*b*ε^3*ρ^2 - α^2*b*ε*ρ - α^2*ε^2*ρ^2 - ε^2*ρ^2 + 2*ρ

theorem scale_U12 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α U12 = ε ^ 2 * gU12 ρ a b α ε := by
  rw [closed_U12]; unfold gU12; ring

theorem cont_U12 (ρ a b α : ℝ) : Continuous (gU12 ρ a b α) := by
  unfold gU12; fun_prop

theorem zero_U12 (ρ a b α : ℝ) : gU12 ρ a b α 0 = 2*ρ := by
  unfold gU12; ring

/-- `U13` divided by `ε²` after the substitution. -/
def gU13 (ρ a b α ε : ℝ) : ℝ := 2*a*α^4*b*ε^4*ρ^2 - 2*a*α^3*b*ε^4*ρ^2 - 2*a*α^3*b*ε^2*ρ + 2*a*α^2*b*ε^2*ρ + a*b*ε^4*ρ^2 - 2*a*b*ε^2*ρ + a*b

theorem scale_U13 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α Stemma.Quartet.U13 = ε ^ 2 * gU13 ρ a b α ε := by
  rw [closed_U13]; unfold gU13; ring

theorem cont_U13 (ρ a b α : ℝ) : Continuous (gU13 ρ a b α) := by
  unfold gU13; fun_prop

theorem zero_U13 (ρ a b α : ℝ) : gU13 ρ a b α 0 = a*b := by
  unfold gU13; ring

/-- `U14` divided by `ε²` after the substitution. -/
def gU14 (ρ a b α ε : ℝ) : ℝ := 2*a*α^4*b*ε^4*ρ^2 - 2*a*α^3*b*ε^4*ρ^2 - 2*a*α^3*b*ε^2*ρ + 2*a*α^2*b*ε^2*ρ

theorem scale_U14 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α U14 = ε ^ 2 * gU14 ρ a b α ε := by
  rw [closed_U14]; unfold gU14; ring

theorem cont_U14 (ρ a b α : ℝ) : Continuous (gU14 ρ a b α) := by
  unfold gU14; fun_prop

theorem zero_U14 (ρ a b α : ℝ) : gU14 ρ a b α 0 = 0 := by
  unfold gU14; ring

/-- `R12` divided by `ε²` after the substitution. -/
def gR12 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - a*α^3*b*ε^4*ρ^2 - a*α^3*b*ε^2*ρ - a*α^3*ε^3*ρ^2 + a*α^2*b*ε^2*ρ + a*α^2*ε^3*ρ^2 + a*α^2*ε*ρ - a*ε*ρ + α^3*b*ε^3*ρ^2 - α^2*b*ε*ρ - α^2*ε^2*ρ^2 + ρ

theorem scale_R12 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C12 = ε ^ 2 * gR12 ρ a b α ε := by
  rw [closed_R12]; unfold gR12; ring

theorem cont_R12 (ρ a b α : ℝ) : Continuous (gR12 ρ a b α) := by
  unfold gR12; fun_prop

theorem zero_R12 (ρ a b α : ℝ) : gR12 ρ a b α 0 = ρ := by
  unfold gR12; ring

/-- `R13` divided by `ε²` after the substitution. -/
def gR13 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - 2*a*α^3*b*ε^2*ρ + a*α^2*b

theorem scale_R13 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C13 = ε ^ 2 * gR13 ρ a b α ε := by
  rw [closed_R13]; unfold gR13; ring

theorem cont_R13 (ρ a b α : ℝ) : Continuous (gR13 ρ a b α) := by
  unfold gR13; fun_prop

theorem zero_R13 (ρ a b α : ℝ) : gR13 ρ a b α 0 = a*α^2*b := by
  unfold gR13; ring

/-- `R14` divided by `ε²` after the substitution. -/
def gR14 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - a*α^3*b*ε^4*ρ^2 - a*α^3*b*ε^2*ρ + a*α^2*b*ε^2*ρ

theorem scale_R14 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C14 = ε ^ 2 * gR14 ρ a b α ε := by
  rw [closed_R14]; unfold gR14; ring

theorem cont_R14 (ρ a b α : ℝ) : Continuous (gR14 ρ a b α) := by
  unfold gR14; fun_prop

theorem zero_R14 (ρ a b α : ℝ) : gR14 ρ a b α 0 = 0 := by
  unfold gR14; ring

/-- `R23` divided by `ε²` after the substitution. -/
def gR23 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - a*α^3*b*ε^4*ρ^2 - a*α^3*b*ε^2*ρ + a*α^2*b*ε^2*ρ

theorem scale_R23 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C23 = ε ^ 2 * gR23 ρ a b α ε := by
  rw [closed_R23]; unfold gR23; ring

theorem cont_R23 (ρ a b α : ℝ) : Continuous (gR23 ρ a b α) := by
  unfold gR23; fun_prop

theorem zero_R23 (ρ a b α : ℝ) : gR23 ρ a b α 0 = 0 := by
  unfold gR23; ring

/-- `R24` divided by `ε²` after the substitution. -/
def gR24 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - 2*a*α^3*b*ε^4*ρ^2 + a*α^2*b*ε^4*ρ^2

theorem scale_R24 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C24 = ε ^ 2 * gR24 ρ a b α ε := by
  rw [closed_R24]; unfold gR24; ring

theorem cont_R24 (ρ a b α : ℝ) : Continuous (gR24 ρ a b α) := by
  unfold gR24; fun_prop

theorem zero_R24 (ρ a b α : ℝ) : gR24 ρ a b α 0 = 0 := by
  unfold gR24; ring

/-- `R34` divided by `ε²` after the substitution. -/
def gR34 (ρ a b α ε : ℝ) : ℝ := a*α^4*b*ε^4*ρ^2 - a*α^3*b*ε^4*ρ^2 - a*α^3*b*ε^2*ρ + a*α^3*ε^3*ρ^2 + a*α^2*b*ε^2*ρ - a*α^2*ε*ρ - α^3*b*ε^3*ρ^2 + α^2*b*ε^3*ρ^2 + α^2*b*ε*ρ - α^2*ε^2*ρ^2 - b*ε*ρ + ρ

theorem scale_R34 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C34 = ε ^ 2 * gR34 ρ a b α ε := by
  rw [closed_R34]; unfold gR34; ring

theorem cont_R34 (ρ a b α : ℝ) : Continuous (gR34 ρ a b α) := by
  unfold gR34; fun_prop

theorem zero_R34 (ρ a b α : ℝ) : gR34 ρ a b α 0 = ρ := by
  unfold gR34; ring

/-- `R123` divided by `ε²` after the substitution. -/
def gR123 (ρ a b α ε : ℝ) : ℝ := -a*α^4*b*ε^4*ρ^2 + a*α^3*b*ε^4*ρ^2 + a*α^3*b*ε^2*ρ - a*α^2*b*ε^2*ρ - α^3*b*ε^3*ρ^2 + α^2*b*ε*ρ

theorem scale_R123 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C123 = ε ^ 2 * gR123 ρ a b α ε := by
  rw [closed_R123]; unfold gR123; ring

theorem cont_R123 (ρ a b α : ℝ) : Continuous (gR123 ρ a b α) := by
  unfold gR123; fun_prop

theorem zero_R123 (ρ a b α : ℝ) : gR123 ρ a b α 0 = 0 := by
  unfold gR123; ring

/-- `R124` divided by `ε²` after the substitution. -/
def gR124 (ρ a b α ε : ℝ) : ℝ := -a*α^4*b*ε^4*ρ^2 + 2*a*α^3*b*ε^4*ρ^2 - a*α^2*b*ε^4*ρ^2 - α^3*b*ε^3*ρ^2 + α^2*b*ε^3*ρ^2

theorem scale_R124 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C124 = ε ^ 2 * gR124 ρ a b α ε := by
  rw [closed_R124]; unfold gR124; ring

theorem cont_R124 (ρ a b α : ℝ) : Continuous (gR124 ρ a b α) := by
  unfold gR124; fun_prop

theorem zero_R124 (ρ a b α : ℝ) : gR124 ρ a b α 0 = 0 := by
  unfold gR124; ring

/-- `R134` divided by `ε²` after the substitution. -/
def gR134 (ρ a b α ε : ℝ) : ℝ := -a*α^4*b*ε^4*ρ^2 + a*α^3*b*ε^4*ρ^2 + a*α^3*b*ε^2*ρ - a*α^3*ε^3*ρ^2 - a*α^2*b*ε^2*ρ + a*α^2*ε*ρ

theorem scale_R134 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C134 = ε ^ 2 * gR134 ρ a b α ε := by
  rw [closed_R134]; unfold gR134; ring

theorem cont_R134 (ρ a b α : ℝ) : Continuous (gR134 ρ a b α) := by
  unfold gR134; fun_prop

theorem zero_R134 (ρ a b α : ℝ) : gR134 ρ a b α 0 = 0 := by
  unfold gR134; ring

/-- `R234` divided by `ε²` after the substitution. -/
def gR234 (ρ a b α ε : ℝ) : ℝ := -a*α^4*b*ε^4*ρ^2 + 2*a*α^3*b*ε^4*ρ^2 - a*α^3*ε^3*ρ^2 - a*α^2*b*ε^4*ρ^2 + a*α^2*ε^3*ρ^2

theorem scale_R234 (ρ a b α ε : ℝ) :
    suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C234 = ε ^ 2 * gR234 ρ a b α ε := by
  rw [closed_R234]; unfold gR234; ring

theorem cont_R234 (ρ a b α : ℝ) : Continuous (gR234 ρ a b α) := by
  unfold gR234; fun_prop

theorem zero_R234 (ρ a b α : ℝ) : gR234 ρ a b α 0 = 0 := by
  unfold gR234; ring

end Stemma.Coding
