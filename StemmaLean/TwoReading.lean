/-
The two-reading coding: a unit proposes the split `A | B` only when `A` and `B` are exactly the
two reading classes of the unit, so a unit with three or more distinct readings proposes nothing.

Formalised:
* on the quartet `12|34` under the attraction model (setting of `Coding.lean`: `p₂ = p₄ = 0`,
  halves of rate `r`, pendant rates `p₁`, `p₃`), the three exact expected supports
  (`closed_T12`, `closed_T13`, `closed_T14`), summed over the 81 edge outcomes of
  `Quartet.suppA`;
* with `r = ρ ε²`, `p₁ = a ε`, `p₃ = b ε`: if `α² a b < 2ρ` the true split `12|34` has strictly
  the largest expected support for all sufficiently small `ε > 0` (`two_reading_consistent`); if
  `α² a b > 2ρ` the false split `13|24` does (`two_reading_inconsistent`).  The boundary is that
  of the rooted coding (`Coding.rooted_consistent`), not that of the unrooted coding;
* as the number of units grows: consistency with failure probability at most `6 e^{-L γ²/2}`
  (`two_reading_consistency`), and selection of `13|24` with probability tending to one
  (`two_reading_false_selected`);
* for any rooted stemma, a unit with exactly two innovating edges `e`, `f` (clades laminar):
  the two-reading coding proposes a split that is not `C_e` or `C_f` only when the clades are
  disjoint and both readings are attractive, and then the split is `(C_e ∪ C_f) | rest`
  (`two_reading_mechanisms`); a nested pair `C_f ⊊ C_e` proposes nothing unless both readings
  are attractive, and then only the split of `e` (`two_reading_nested`); a disjoint pair proposes
  nothing unless both readings are attractive, and then only `(C_e ∪ C_f) | rest`
  (`two_reading_disjoint`).  The classes are those of `Mechanisms.lean`.
-/
import StemmaLean.CodingLimit
import StemmaLean.Mechanisms

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped Classical

namespace Stemma.TwoReading

open Stemma.Splits Stemma.Quartet Stemma.Coding Stemma.CodingLimit

/-! ### The quartet: exact expected supports -/

/-- The two-reading coding proposes `12|34` when `{1,2}` and `{3,4}` are the two reading classes. -/
def T12 (x1 x2 x3 x4 : ℕ) : Bool := x1 == x2 && x3 == x4 && x1 != x3
/-- The two-reading coding proposes `13|24` when `{1,3}` and `{2,4}` are the two reading classes. -/
def T13 (x1 x2 x3 x4 : ℕ) : Bool := x1 == x3 && x2 == x4 && x1 != x2
/-- The two-reading coding proposes `14|23` when `{1,4}` and `{2,3}` are the two reading classes. -/
def T14 (x1 x2 x3 x4 : ℕ) : Bool := x1 == x4 && x2 == x3 && x1 != x2

theorem closed_T12 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α T12 = r * (2*α^3*p1*p3*r - α^3*p1*r - α^3*p3*r - α^2*p1*p3*r - 2*α^2*p1*p3
      + α^2*p1*r + α^2*p1 + α^2*p3*r + α^2*p3 - α^2*r - p1*p3*r + 2*p1*p3 + p1*r - 2*p1 + p3*r
      - 2*p3 - r + 2) := by
  simp [suppA, w, readBelow, rd, T12, Fin.sum_univ_three]; ring

theorem closed_T13 (r p1 p3 α : ℝ) :
    suppA r p1 p3 α T13 = α ^ 2 * p1 * p3 * (1 - r) ^ 2 := by
  simp [suppA, w, readBelow, rd, T13, Fin.sum_univ_three]; ring

theorem closed_T14 (r p1 p3 α : ℝ) : suppA r p1 p3 α T14 = 0 := by
  simp [suppA, w, readBelow, rd, T14, Fin.sum_univ_three]

/-! ### Leading order -/

/-- `T12` divided by `ε²` after the substitution `r = ρ ε²`, `p₁ = a ε`, `p₃ = b ε`. -/
def gT12 (ρ a b α ε : ℝ) : ℝ :=
  ρ * (2*α^3*(a*ε)*(b*ε)*(ρ*ε^2) - α^3*(a*ε)*(ρ*ε^2) - α^3*(b*ε)*(ρ*ε^2)
    - α^2*(a*ε)*(b*ε)*(ρ*ε^2) - 2*α^2*(a*ε)*(b*ε) + α^2*(a*ε)*(ρ*ε^2) + α^2*(a*ε)
    + α^2*(b*ε)*(ρ*ε^2) + α^2*(b*ε) - α^2*(ρ*ε^2) - (a*ε)*(b*ε)*(ρ*ε^2) + 2*(a*ε)*(b*ε)
    + (a*ε)*(ρ*ε^2) - 2*(a*ε) + (b*ε)*(ρ*ε^2) - 2*(b*ε) - (ρ*ε^2) + 2)

/-- `T13` divided by `ε²` after the substitution. -/
def gT13 (ρ a b α ε : ℝ) : ℝ := α ^ 2 * a * b * (1 - ρ * ε ^ 2) ^ 2

/-- Two-reading supports after the substitution. -/
def sT (P : ℕ → ℕ → ℕ → ℕ → Bool) (ρ a b α ε : ℝ) : ℝ :=
  suppA (ρ * ε ^ 2) (a * ε) (b * ε) α P

theorem scale_T12 (ρ a b α ε : ℝ) : sT T12 ρ a b α ε = ε ^ 2 * gT12 ρ a b α ε := by
  rw [sT, closed_T12]; unfold gT12; ring

theorem scale_T13 (ρ a b α ε : ℝ) : sT T13 ρ a b α ε = ε ^ 2 * gT13 ρ a b α ε := by
  rw [sT, closed_T13]; unfold gT13; ring

theorem scale_T14 (ρ a b α ε : ℝ) : sT T14 ρ a b α ε = 0 := by
  rw [sT, closed_T14]

theorem cont_T12 (ρ a b α : ℝ) : Continuous (gT12 ρ a b α) := by unfold gT12; fun_prop

theorem cont_T13 (ρ a b α : ℝ) : Continuous (gT13 ρ a b α) := by unfold gT13; fun_prop

theorem zero_T12 (ρ a b α : ℝ) : gT12 ρ a b α 0 = 2 * ρ := by unfold gT12; ring

theorem zero_T13 (ρ a b α : ℝ) : gT13 ρ a b α 0 = α ^ 2 * a * b := by unfold gT13; ring

/-- **Two-reading coding, consistent side.**  If `α² a b < 2ρ` (with `ρ > 0`), then for all
sufficiently small `ε > 0` the true split `12|34` has strictly larger expected support than both
false splits `13|24` and `14|23`. -/
theorem two_reading_consistent (ρ a b α : ℝ) (hρ : 0 < ρ) (h : α ^ 2 * a * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      max (sT T13 ρ a b α ε) (sT T14 ρ a b α ε) < sT T12 ρ a b α ε := by
  have e1 := eventually_pos (G := fun ε => gT12 ρ a b α ε - gT13 ρ a b α ε)
    ((cont_T12 ρ a b α).sub (cont_T13 ρ a b α)) (by simp [zero_T12, zero_T13]; linarith)
  have e2 := eventually_pos (cont_T12 ρ a b α) (by rw [zero_T12]; linarith)
  filter_upwards [e1, e2] with ε h1 h2
  rw [scale_T12, scale_T13, scale_T14, max_lt_iff]
  constructor <;> nlinarith

/-- **Two-reading coding, inconsistent side.**  If `α² a b > 2ρ` (with `ρ > 0`), then for all
sufficiently small `ε > 0` the false split `13|24` has strictly the largest expected support. -/
theorem two_reading_inconsistent (ρ a b α : ℝ) (hρ : 0 < ρ) (h : 2 * ρ < α ^ 2 * a * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sT T12 ρ a b α ε < sT T13 ρ a b α ε ∧ sT T14 ρ a b α ε < sT T13 ρ a b α ε := by
  have e1 := eventually_pos (G := fun ε => gT13 ρ a b α ε - gT12 ρ a b α ε)
    ((cont_T13 ρ a b α).sub (cont_T12 ρ a b α)) (by simp [zero_T12, zero_T13]; linarith)
  have e2 := eventually_pos (cont_T13 ρ a b α) (by rw [zero_T13]; linarith)
  filter_upwards [e1, e2] with ε h1 h2
  rw [scale_T12, scale_T13, scale_T14]
  constructor <;> nlinarith

/-! ### With the units -/

/-- The expected two-reading supports of the attraction model on the quartet, indexed by the
sides away from witness `4` (as `CodingLimit.mU`). -/
noncomputable def mT (ρ a b α ε : ℝ) (σ : Finset (Fin 4)) : ℝ :=
  if σ = s12 then sT T12 ρ a b α ε else if σ = s13 then sT T13 ρ a b α ε
  else if σ = s14 then sT T14 ρ a b α ε else 0

lemma mT12 (ρ a b α ε : ℝ) : mT ρ a b α ε s12 = sT T12 ρ a b α ε := by simp [mT]
lemma mT13 (ρ a b α ε : ℝ) : mT ρ a b α ε s13 = sT T13 ρ a b α ε := by
  have h1 : s13 ≠ s12 := by decide
  simp [mT, h1]
lemma mT14 (ρ a b α ε : ℝ) : mT ρ a b α ε s14 = sT T14 ρ a b α ε := by
  have h1 : s14 ≠ s12 := by decide
  have h2 : s14 ≠ s13 := by decide
  simp [mT, h1, h2]
lemma mT_off (ρ a b α ε : ℝ) (σ : Finset (Fin 4)) (h1 : σ ≠ s12) (h2 : σ ≠ s13)
    (h3 : σ ≠ s14) : mT ρ a b α ε σ = 0 := by
  simp [mT, h1, h2, h3]

/-- **Two-reading coding with units, consistent side.**  If `α² a b < 2ρ` (`ρ > 0`), then for every
sufficiently small `ε > 0` there is `γ > 0` such that, for units with the expected two-reading
supports of the attraction model, the estimator misses the true split `12|34` with probability at
most `6 e^{-L γ²/2}`. -/
theorem two_reading_consistency (ρ a b α : ℝ) (hρ : 0 < ρ) (h : α ^ 2 * a * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ σ, iIndepFun (Y σ) μ) → (∀ σ u, μ[Y σ u] = mT ρ a b α ε σ) →
      (∀ σ, σ ≠ s12 → σ ≠ s13 → σ ≠ s14 → ∀ u ω, Y σ u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {s12} ∧
        ∑ σ ∈ {s12}, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  filter_upwards [two_reading_consistent ρ a b α hρ h] with ε hε
  rw [max_lt_iff] at hε
  have h0 : 0 < sT T12 ρ a b α ε := by
    have := hε.2; rw [scale_T14] at this; exact this
  refine quartet_consistency _ ?_ ?_ ?_ (mT_off ρ a b α ε)
  · rw [mT13, mT12]; exact hε.1
  · rw [mT14, mT12]; exact hε.2
  · rw [mT12]; exact h0

/-- **Two-reading coding with units, inconsistent side.**  If `α² a b > 2ρ` (`ρ > 0`), then for
every sufficiently small `ε > 0`, for i.i.d. units with the expected two-reading supports, almost
surely the false split `13|24` is eventually strictly heavier than every other compatible set (so
it is selected), and the probability that it is tends to one. -/
theorem two_reading_false_selected (ρ a b α : ℝ) (hρ : 0 < ρ) (h : 2 * ρ < α ^ 2 * a * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ) →
      (∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ) →
      (∀ σ, μ[Y σ 0] = mT ρ a b α ε σ) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω}ᶜ) atTop
        (𝓝 0) := by
  filter_upwards [two_reading_inconsistent ρ a b α hρ h] with ε hε
  refine quartet_false_selected _ ?_ ?_
  · rw [mT12, mT13]; exact hε.1
  · rw [mT14, mT13]; exact hε.2

/-! ### Two innovating edges on any rooted stemma -/

section mechanisms

open Stemma.Mechanisms

variable {n : ℕ}

/-- The two-reading coding proposes the split `A | Aᶜ`: `A` and `Aᶜ` are non-empty and are
exactly the two reading classes of the unit. -/
def Prop2 (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) (A : Finset (Fin n)) :
    Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧ ∃ v v', A = cls M att v ∧ Aᶜ = cls M att v'

variable {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {A : Finset (Fin n)}

/-- A proposed split is the class of the reading of any of its witnesses. -/
lemma prop2_class (h : Prop2 M att A) {x : Fin n} (hx : x ∈ A) :
    ∀ y, y ∈ A ↔ read M att y = read M att x := by
  obtain ⟨-, -, v, -, hv, -⟩ := h
  have hxv : read M att x = v := mem_cls.mp (hv ▸ hx)
  intro y
  rw [hxv, hv, mem_cls]

/-- No unit with a proposed split has three distinct readings. -/
lemma prop2_three (h : Prop2 M att A) {x y z : Fin n} (hxy : read M att x ≠ read M att y)
    (hxz : read M att x ≠ read M att z) (hyz : read M att y ≠ read M att z) : False := by
  obtain ⟨-, -, v, v', hv, hv'⟩ := h
  have hc : ∀ t, read M att t = v ∨ read M att t = v' := by
    intro t
    by_cases ht : t ∈ A
    · exact Or.inl (mem_cls.mp (hv ▸ ht))
    · exact Or.inr (mem_cls.mp (hv' ▸ mem_compl.mpr ht))
  rcases hc x with hx | hx <;> rcases hc y with hy | hy <;> rcases hc z with hz | hz <;>
    simp_all

/-- The split proposed when the classes are `B` and `Bᶜ`. -/
lemma prop2_of_classes {B : Finset (Fin n)} (hB : B.Nonempty) (hB' : Bᶜ.Nonempty) {v v' : Rd n}
    (h1 : ∀ x, x ∈ B → read M att x = v) (h2 : ∀ x, x ∉ B → read M att x = v') (hvv : v ≠ v') :
    Prop2 M att B := by
  refine ⟨hB, hB', v, v', ?_, ?_⟩
  · ext x
    rw [mem_cls]
    by_cases hx : x ∈ B
    · simp [hx, h1 x hx]
    · simp [hx, h2 x hx, Ne.symm hvv]
  · ext x
    rw [mem_cls, mem_compl]
    by_cases hx : x ∈ B
    · simp [hx, h1 x hx, hvv]
    · simp [hx, h2 x hx]

/-- **Two innovations on disjoint clades.**  With innovations on two disjoint non-empty clades
`C_e`, `C_f` and some witness outside both, the two-reading coding proposes a split exactly when
both readings are attractive, and then it is `(C_e ∪ C_f) | rest`. -/
theorem two_reading_disjoint {e f : Finset (Fin n)} (hd : Disjoint e f) (he : e.Nonempty)
    (hf : f.Nonempty) (hrest : (e ∪ f)ᶜ.Nonempty) :
    Prop2 {e, f} att A ↔ att e = true ∧ att f = true ∧ (A = e ∪ f ∨ A = (e ∪ f)ᶜ) := by
  have hef : e ≠ f := by
    rintro rfl; obtain ⟨x, hx⟩ := he; exact disjoint_left.mp hd hx hx
  have hr := read_disj att hd
  obtain ⟨x, hx⟩ := he
  obtain ⟨y, hy⟩ := hf
  obtain ⟨z, hz⟩ := hrest
  have hye : y ∉ e := disjoint_right.mp hd hy
  have hze : z ∉ e := fun h => (mem_compl.mp hz) (mem_union_left _ h)
  have hzf : z ∉ f := fun h => (mem_compl.mp hz) (mem_union_right _ h)
  have rx : read {e, f} att x = val att e := by rw [hr, ite_eq_left hx]
  have ry : read {e, f} att y = val att f := by rw [hr, ite_eq_right hye, ite_eq_left hy]
  have rz : read {e, f} att z = .orig := by rw [hr, ite_eq_right hze, ite_eq_right hzf]
  constructor
  · intro hP
    have hboth : att e = true ∧ att f = true := by
      by_contra hne
      have hvv : val att e ≠ val att f := fun h => hne ((val_eq_iff att hef).mp h)
      exact prop2_three hP (x := x) (y := y) (z := z) (by rw [rx, ry]; exact hvv)
        (by rw [rx, rz]; exact val_ne_orig att e) (by rw [ry, rz]; exact val_ne_orig att f)
    refine ⟨hboth.1, hboth.2, ?_⟩
    have ve : val att e = .attr := by simp [Mechanisms.val, hboth.1]
    have vf : val att f = .attr := by simp [Mechanisms.val, hboth.2]
    have hread : ∀ t, read {e, f} att t = if t ∈ e ∪ f then .attr else .orig := by
      intro t
      rw [hr]
      by_cases hte : t ∈ e <;> by_cases htf : t ∈ f <;> simp [hte, htf, ve, vf]
    obtain ⟨t, ht⟩ := hP.1
    have hcl := prop2_class hP ht
    by_cases hte : t ∈ e ∪ f
    · left; ext s; rw [hcl s, hread s, hread t, ite_eq_left hte]
      by_cases hs : s ∈ e ∪ f <;> simp [hs]
    · right; ext s; rw [hcl s, hread s, hread t, ite_eq_right hte, mem_compl]
      by_cases hs : s ∈ e ∪ f <;> simp [hs]
  · rintro ⟨h1, h2, hA⟩
    have ve : val att e = .attr := by simp [Mechanisms.val, h1]
    have vf : val att f = .attr := by simp [Mechanisms.val, h2]
    have hread : ∀ t, read {e, f} att t = if t ∈ e ∪ f then .attr else .orig := by
      intro t
      rw [hr]
      by_cases hte : t ∈ e <;> by_cases htf : t ∈ f <;> simp [hte, htf, ve, vf]
    have hne1 : (e ∪ f).Nonempty := ⟨x, mem_union_left _ hx⟩
    have hne2 : (e ∪ f)ᶜ.Nonempty := ⟨z, hz⟩
    have hP : Prop2 {e, f} att (e ∪ f) :=
      prop2_of_classes hne1 hne2 (v := .attr) (v' := .orig)
        (fun t ht => by rw [hread, ite_eq_left ht]) (fun t ht => by rw [hread, ite_eq_right ht])
        (by simp)
    rcases hA with rfl | rfl
    · exact hP
    · obtain ⟨a1, a2, v, v', hv, hv'⟩ := hP
      exact ⟨a2, by rwa [compl_compl], v', v, hv', by rw [compl_compl]; exact hv⟩

/-- **Two nested innovations.**  With innovations on nested clades `C_f ⊊ C_e`, `C_f` non-empty
and some witness outside `C_e`, the two-reading coding proposes a split exactly when both readings
are attractive, and then it is the split `C_e | rest` of the edge `e`, a split of the stemma. -/
theorem two_reading_nested {e f : Finset (Fin n)} (hfe : f ⊂ e) (hf : f.Nonempty)
    (hrest : eᶜ.Nonempty) :
    Prop2 {e, f} att A ↔ att e = true ∧ att f = true ∧ (A = e ∨ A = eᶜ) := by
  have hef : e ≠ f := fun h => hfe.ne h.symm
  have hr := read_nest att hfe
  obtain ⟨y, hy⟩ := hf
  obtain ⟨x, hx⟩ : (e \ f).Nonempty := sdiff_nonempty.mpr (not_subset_of_ssubset hfe)
  obtain ⟨z, hz⟩ := hrest
  have hze : z ∉ e := mem_compl.mp hz
  have hzf : z ∉ f := fun h => hze (hfe.1 h)
  have rx : read {e, f} att x = val att e := by
    rw [hr, ite_eq_right (mem_sdiff.mp hx).2, ite_eq_left (mem_sdiff.mp hx).1]
  have ry : read {e, f} att y = val att f := by rw [hr, ite_eq_left hy]
  have rz : read {e, f} att z = .orig := by rw [hr, ite_eq_right hzf, ite_eq_right hze]
  constructor
  · intro hP
    have hboth : att e = true ∧ att f = true := by
      by_contra hne
      have hvv : val att e ≠ val att f := fun h => hne ((val_eq_iff att hef).mp h)
      exact prop2_three hP (x := x) (y := y) (z := z) (by rw [rx, ry]; exact hvv)
        (by rw [rx, rz]; exact val_ne_orig att e) (by rw [ry, rz]; exact val_ne_orig att f)
    refine ⟨hboth.1, hboth.2, ?_⟩
    have ve : val att e = .attr := by simp [Mechanisms.val, hboth.1]
    have vf : val att f = .attr := by simp [Mechanisms.val, hboth.2]
    have hread : ∀ t, read {e, f} att t = if t ∈ e then .attr else .orig := by
      intro t
      rw [hr]
      by_cases htf : t ∈ f
      · simp [htf, hfe.1 htf, vf]
      · by_cases hte : t ∈ e <;> simp [hte, htf, ve]
    obtain ⟨t, ht⟩ := hP.1
    have hcl := prop2_class hP ht
    by_cases hte : t ∈ e
    · left; ext s; rw [hcl s, hread s, hread t, ite_eq_left hte]
      by_cases hs : s ∈ e <;> simp [hs]
    · right; ext s; rw [hcl s, hread s, hread t, ite_eq_right hte, mem_compl]
      by_cases hs : s ∈ e <;> simp [hs]
  · rintro ⟨h1, h2, hA⟩
    have ve : val att e = .attr := by simp [Mechanisms.val, h1]
    have vf : val att f = .attr := by simp [Mechanisms.val, h2]
    have hread : ∀ t, read {e, f} att t = if t ∈ e then .attr else .orig := by
      intro t
      rw [hr]
      by_cases htf : t ∈ f
      · simp [htf, hfe.1 htf, vf]
      · by_cases hte : t ∈ e <;> simp [hte, htf, ve]
    have hne1 : e.Nonempty := ⟨y, hfe.1 hy⟩
    have hne2 : eᶜ.Nonempty := ⟨z, hz⟩
    have hP : Prop2 {e, f} att e :=
      prop2_of_classes hne1 hne2 (v := .attr) (v' := .orig)
        (fun t ht => by rw [hread, ite_eq_left ht]) (fun t ht => by rw [hread, ite_eq_right ht])
        (by simp)
    rcases hA with rfl | rfl
    · exact hP
    · obtain ⟨a1, a2, v, v', hv, hv'⟩ := hP
      exact ⟨a2, by rwa [compl_compl], v', v, hv', by rw [compl_compl]; exact hv⟩

/-- **The second-order mechanism of the two-reading coding.**  On any rooted stemma, in a unit
with exactly two innovating edges `e ≠ f` (clades non-empty and laminar, as the clades of a tree
are), every split proposed by the two-reading coding is a split of the stemma (`C_e` or `C_f`, by
either side), unless the clades are disjoint and both readings are attractive, in which case it
is `(C_e ∪ C_f) | rest`.  No witness outside the clades is assumed. -/
theorem two_reading_mechanisms {e f : Finset (Fin n)} (hef : e ≠ f) (he : e.Nonempty)
    (hf : f.Nonempty) (hlam : Disjoint e f ∨ e ⊆ f ∨ f ⊆ e) (hP : Prop2 {e, f} att A) :
    (A = e ∨ A = eᶜ ∨ A = f ∨ A = fᶜ) ∨
      (Disjoint e f ∧ att e = true ∧ att f = true ∧ (A = e ∪ f ∨ A = (e ∪ f)ᶜ)) := by
  -- the nested case, with `g ⊊ h`
  have nest : ∀ {g h : Finset (Fin n)}, g ⊂ h → g.Nonempty → Prop2 {h, g} att A →
      A = h ∨ A = hᶜ ∨ A = g ∨ A = gᶜ := by
    intro g h hgh hg hP'
    by_cases hrest : hᶜ.Nonempty
    · rcases ((two_reading_nested hgh hg hrest).mp hP').2.2 with hA | hA
      · exact Or.inl hA
      · exact Or.inr (Or.inl hA)
    · have hhU : ∀ t, t ∈ h := fun t => by
        by_contra ht; exact hrest ⟨t, mem_compl.mpr ht⟩
      have hr := read_nest att hgh
      obtain ⟨t, ht⟩ := hP'.1
      have hcl := prop2_class hP' ht
      by_cases htg : t ∈ g
      · -- `A` is the class of `val g`; it is `g` unless `val h = val g`
        by_cases hv : val att h = val att g
        · exfalso
          obtain ⟨s, hs⟩ := hP'.2.1
          have hsA : s ∉ A := mem_compl.mp hs
          apply hsA
          rw [hcl s, hr, hr t, ite_eq_left htg]
          by_cases hsg : s ∈ g
          · rw [ite_eq_left hsg]
          · rw [ite_eq_right hsg, ite_eq_left (hhU s), hv]
        · right; right; left
          ext s
          rw [hcl s, hr, hr t, ite_eq_left htg]
          by_cases hsg : s ∈ g
          · simp [hsg]
          · simp [hsg, hhU s, hv]
      · right; right; right
        ext s
        rw [hcl s, hr, hr t, ite_eq_right htg, ite_eq_left (hhU t), mem_compl]
        by_cases hsg : s ∈ g
        · simp only [hsg, ite_true, not_true_eq_false, iff_false]
          intro hv
          obtain ⟨u, hu⟩ := hP'.2.1
          apply mem_compl.mp hu
          rw [hcl u, hr, hr t, ite_eq_right htg, ite_eq_left (hhU t)]
          by_cases hug : u ∈ g
          · rw [ite_eq_left hug, hv]
          · rw [ite_eq_right hug, ite_eq_left (hhU u)]
        · simp [hsg, hhU s]
  rcases hlam with hd | hsub | hsub
  · by_cases hrest : (e ∪ f)ᶜ.Nonempty
    · exact Or.inr ⟨hd, (two_reading_disjoint hd he hf hrest).mp hP⟩
    · -- every witness is in `C_e` or `C_f`
      have hU : ∀ t, t ∈ e ∨ t ∈ f := fun t => by
        by_contra ht
        exact hrest ⟨t, mem_compl.mpr fun h => ht (mem_union.mp h)⟩
      have hr := read_disj att hd
      obtain ⟨t, ht⟩ := hP.1
      have hcl := prop2_class hP ht
      by_cases hv : val att e = val att f
      · exfalso
        obtain ⟨s, hs⟩ := hP.2.1
        apply mem_compl.mp hs
        rw [hcl s]
        have hall : ∀ u, read {e, f} att u = val att e := by
          intro u
          rw [hr]
          rcases hU u with hu | hu
          · rw [ite_eq_left hu]
          · rw [ite_eq_right (disjoint_right.mp hd hu), ite_eq_left hu, hv]
        rw [hall, hall]
      · left
        rcases hU t with hte | htf
        · left
          ext s
          rw [hcl s, hr, hr t, ite_eq_left hte]
          rcases hU s with hs | hs
          · simp [hs]
          · simp [disjoint_right.mp hd hs, hs, Ne.symm hv]
        · right; right; left
          ext s
          rw [hcl s, hr, hr t, ite_eq_right (disjoint_right.mp hd htf), ite_eq_left htf]
          rcases hU s with hs | hs
          · simp [hs, disjoint_left.mp hd hs, hv]
          · simp [disjoint_right.mp hd hs, hs]
  · have hP' : Prop2 {f, e} att A := by rwa [pair_comm]
    rcases nest (ssubset_of_subset_of_ne hsub hef) he hP' with h | h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
  · rcases nest (ssubset_of_subset_of_ne hsub hef.symm) hf hP with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

end mechanisms

end Stemma.TwoReading
