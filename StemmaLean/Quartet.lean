/-
The quartet under the irreversible model and under the attraction model.

Formalises, for the mathematical paper ("Coincident scribal error and the Bédier effect"):
* Proposition 4.4 (Quartet): the exact expected supports of the three splits;
* Corollary 4.5 (Textual long-branch zone): the consistency boundary (with the units, the two
  strict cases are `CodingLimit.long_branch_consistent` and `long_branch_inconsistent`);
* the two exact false supports in Theorem 4.7 (coincidence enters only the rooted coding).

Expected supports are computed by summing, over every outcome of the edges, the probability of
the outcome times the indicator that the unit proposes the split.  The leading-order parts (a), (b)
of Theorem 4.7 are in `Coding.lean`.
-/
import Mathlib

namespace Stemma.Quartet

/-! ### Irreversible model

The tree is `12|34`, rooted on the internal edge, with halves `r₁` (above 1, 2) and `r₂`
(above 3, 4) and pendant edges `p₁ … p₄`.  Each edge is marked independently; a witness reads `1`
when some edge above it is marked.  On four witnesses a unit proposes a non-trivial split exactly
when two witnesses read `1`. -/

/-- Probability of a mark pattern value. -/
def pr (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- Expected support of a split, as a sum over the 2⁶ mark patterns. `prop` decides, from the
readings of witnesses 1–4, whether the unit proposes the split. -/
def supp (r₁ r₂ p₁ p₂ p₃ p₄ : ℝ) (prop : Bool → Bool → Bool → Bool → Bool) : ℝ :=
  ∑ h₁ : Bool, ∑ h₂ : Bool, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    pr r₁ h₁ * pr r₂ h₂ * pr p₁ a * pr p₂ b * pr p₃ c * pr p₄ d *
      (if prop (h₁ || a) (h₁ || b) (h₂ || c) (h₂ || d) then 1 else 0)

/-- The unit proposes `12|34` when exactly {1,2} or exactly {3,4} read `1`. -/
def P12 (x₁ x₂ x₃ x₄ : Bool) : Bool := (x₁ && x₂ && !x₃ && !x₄) || (!x₁ && !x₂ && x₃ && x₄)
def P13 (x₁ x₂ x₃ x₄ : Bool) : Bool := (x₁ && !x₂ && x₃ && !x₄) || (!x₁ && x₂ && !x₃ && x₄)
def P14 (x₁ x₂ x₃ x₄ : Bool) : Bool := (x₁ && !x₂ && !x₃ && x₄) || (!x₁ && x₂ && x₃ && !x₄)

/-- **Proposition 4.4**, first formula. -/
theorem m12 (r₁ r₂ p₁ p₂ p₃ p₄ : ℝ) :
    supp r₁ r₂ p₁ p₂ p₃ p₄ P12 =
      (1 - r₂) * (1 - p₃) * (1 - p₄) * (r₁ + (1 - r₁) * p₁ * p₂) +
      (1 - r₁) * (1 - p₁) * (1 - p₂) * (r₂ + (1 - r₂) * p₃ * p₄) := by
  simp [supp, pr, P12]; ring

/-- **Proposition 4.4**, second formula. -/
theorem m13 (r₁ r₂ p₁ p₂ p₃ p₄ : ℝ) :
    supp r₁ r₂ p₁ p₂ p₃ p₄ P13 =
      (1 - r₁) * (1 - r₂) * (p₁ * p₃ * (1 - p₂) * (1 - p₄) + p₂ * p₄ * (1 - p₁) * (1 - p₃)) := by
  simp [supp, pr, P13]; ring

/-- **Proposition 4.4**, third formula. -/
theorem m14 (r₁ r₂ p₁ p₂ p₃ p₄ : ℝ) :
    supp r₁ r₂ p₁ p₂ p₃ p₄ P14 =
      (1 - r₁) * (1 - r₂) * (p₁ * p₄ * (1 - p₂) * (1 - p₃) + p₂ * p₃ * (1 - p₁) * (1 - p₄)) := by
  simp [supp, pr, P14]; ring

/-- **Corollary 4.5** (textual long-branch zone).  With `p₂ = p₄ = 0` and halves of equal rate
`r < 1`, the true split `12|34` has larger expected support than both false splits exactly when
`(1 - r) p₁ p₃ < r (2 - p₁ - p₃)`. -/
theorem long_branch (r p₁ p₃ : ℝ) (hr : r < 1) (hp₁ : 0 ≤ p₁) (hp₃ : 0 ≤ p₃) :
    (max (supp r r p₁ 0 p₃ 0 P13) (supp r r p₁ 0 p₃ 0 P14) < supp r r p₁ 0 p₃ 0 P12) ↔
      (1 - r) * p₁ * p₃ < r * (2 - p₁ - p₃) := by
  rw [m12, m13, m14]
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have e14 : (1 - r) * (1 - r) * (p₁ * 0 * (1 - 0) * (1 - p₃) + 0 * p₃ * (1 - p₁) * (1 - 0)) = 0 := by
    ring
  rw [e14]
  have key : (1 - (r:ℝ)) * (1 - p₃) * (1 - 0) * (r + (1 - r) * p₁ * 0) +
      (1 - r) * (1 - p₁) * (1 - 0) * (r + (1 - r) * p₃ * 0) -
      (1 - r) * (1 - r) * (p₁ * p₃ * (1 - 0) * (1 - 0) + 0 * 0 * (1 - p₁) * (1 - p₃)) =
      (1 - r) * (r * (2 - p₁ - p₃) - (1 - r) * p₁ * p₃) := by ring
  have hm13 : 0 ≤ (1 - r) * (1 - r) * (p₁ * p₃ * (1 - 0) * (1 - 0) + 0 * 0 * (1 - p₁) * (1 - p₃)) := by
    have : 0 ≤ p₁ * p₃ := mul_nonneg hp₁ hp₃
    nlinarith [mul_pos h1 h1]
  rw [max_lt_iff]
  constructor
  · rintro ⟨h, -⟩
    have : 0 < (1 - r) * (r * (2 - p₁ - p₃) - (1 - r) * p₁ * p₃) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp h1
    linarith
  · intro h
    have hpos : 0 < (1 - r) * (r * (2 - p₁ - p₃) - (1 - r) * p₁ * p₃) :=
      mul_pos h1 (by linarith)
    exact ⟨by linarith, by linarith⟩

/-! ### Attraction model (coincident errors)

Each edge innovates with its rate; an innovation takes the attractive reading with probability `α`
and otherwise a reading of its own.  A witness reads the value of the lowest innovating edge above
it.  Edge outcomes: `0` no innovation, `1` attractive, `2` own reading.  Reading codes: `0` the
original, `1` the attractive reading, `2 + e` the own reading of edge `e`.

Setting of Theorem 4.7: `p₂ = p₄ = 0` and halves of equal rate `r`, so witness 2 reads the value of
half-edge `h₁` and witness 4 that of `h₂`. -/

def w (π α : ℝ) : Fin 3 → ℝ
  | 0 => 1 - π
  | 1 => π * α
  | 2 => π * (1 - α)

/-- Reading produced by an innovating edge `e` with outcome `x`. -/
def rd (e : ℕ) (x : Fin 3) : ℕ := if x = 1 then 1 else 2 + e

/-- Value read below edge outcomes `lo` (lower edge `e`) and `hi` (upper edge `f`). -/
def readBelow (e f : ℕ) (lo hi : Fin 3) : ℕ :=
  if lo ≠ 0 then rd e lo else if hi ≠ 0 then rd f hi else 0

/-- Expected support under the attraction model; `prop` decides from readings `x₁ … x₄`.
Edges: `h₁` (code 0), `h₂` (code 1), pendant of 1 (code 2), pendant of 3 (code 3). -/
def suppA (r p₁ p₃ α : ℝ) (prop : ℕ → ℕ → ℕ → ℕ → Bool) : ℝ :=
  ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3,
    w r α h₁ * w r α h₂ * w p₁ α a * w p₃ α c *
      (if prop (readBelow 2 0 a h₁) (readBelow 0 0 0 h₁) (readBelow 3 1 c h₂) (readBelow 1 1 0 h₂)
        then 1 else 0)

/-- Unrooted coding: `13|24` is proposed when the reading class of witness 1 is {1,3} or the class
of witness 2 is {2,4}. -/
def U13 (x₁ x₂ x₃ x₄ : ℕ) : Bool :=
  (x₁ == x₃ && x₂ != x₁ && x₄ != x₁) || (x₂ == x₄ && x₁ != x₂ && x₃ != x₂)

/-- Rooted coding: the cluster {1,3} is proposed when 1 and 3 share a reading other than the
original, which 2 and 4 do not have. -/
def R13 (x₁ x₂ x₃ x₄ : ℕ) : Bool :=
  x₁ == x₃ && x₁ != 0 && x₂ != x₁ && x₄ != x₁

/-- **Theorem 4.7**, unrooted false support (exact). -/
theorem unrooted_false (r p₁ p₃ α : ℝ) :
    suppA r p₁ p₃ α U13 =
      p₁ * p₃ * ((1 - r) ^ 2 + 2 * α ^ 2 * r * (1 - α) * (1 - α * r)) := by
  simp [suppA, w, readBelow, rd, U13, Fin.sum_univ_three]; ring

/-- **Theorem 4.7**, rooted false support (exact). -/
theorem rooted_false (r p₁ p₃ α : ℝ) :
    suppA r p₁ p₃ α R13 = α ^ 2 * p₁ * p₃ * (1 - α * r) ^ 2 := by
  simp [suppA, w, readBelow, rd, R13, Fin.sum_univ_three]; ring

end Stemma.Quartet
