/-
Proposition 8.3 of the technical report (`prop:gap`), the largest-gap threshold.

The expected supports `m` of the true splits `T` and of the false splits `F`, together with `0`,
form a finite set of values `vals (T ∪ F) m`.  The gap between the groups runs from `a`, the
largest false value (or `0`), to `b`, the smallest true value; every other gap between consecutive
values has length at most `g₂ < b - a`.  The observed values `ŵ σ = w(σ)/L`, together with `0`,
are cut at the midpoint of their largest gap.

* `gap_separation`, the deterministic step: if every `|ŵ σ - m σ| < η = (b - a - g₂)/4`, the
  observed values have a largest gap, and the midpoint of every largest gap separates `T` from
  `F` (and from `0`).  The observed gap between the groups exceeds `G - 2η`, every other observed
  gap is below `g₂ + 2η = G - 2η` (`chain`: a run of expected values with gaps at most `g₂`
  leaves no observed gap of length `g₂ + 2η`).
* `gap_threshold`, the probability: with `L` independent units, the probability that the cut
  does not separate `T` from `F` is at most `2 (|T| + |F|) exp(-L (G - g₂)²/8)`, by Hoeffding's
  inequality for each split and a union bound.

A split outside `T ∪ F` is never proposed; its observed value is `0`, already a value of the set,
so it is left out.  Ties between largest gaps are allowed: every largest gap separates.
-/
import Mathlib
import StemmaLean.Consistency

open MeasureTheory ProbabilityTheory Real Finset
open scoped Classical

namespace Stemma.GapThreshold

variable {ι : Type*}

/-- The values of `f` on `R`, together with `0`. -/
noncomputable def vals (R : Finset ι) (f : ι → ℝ) : Finset ℝ := insert 0 (R.image f)

/-- `(x, y)` is a gap of `V`: two values of `V`, `x < y`, with no value strictly between. -/
def IsGap (V : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ V ∧ y ∈ V ∧ x < y ∧ ∀ v ∈ V, ¬ (x < v ∧ v < y)

/-- `(x, y)` is a largest gap of `V`. -/
def IsLargestGap (V : Finset ℝ) (x y : ℝ) : Prop :=
  IsGap V x y ∧ ∀ x' y', IsGap V x' y' → y' - x' ≤ y - x

/-- The cut `c` separates the true splits from the false ones and from `0`: every observed true
value lies above it, every observed false value and `0` below it. -/
def Separates (T F : Finset ι) (f : ι → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ (∀ σ ∈ T, c < f σ) ∧ ∀ τ ∈ F, f τ < c

lemma mem_vals {R : Finset ι} {f : ι → ℝ} {v : ℝ} :
    v ∈ vals R f ↔ v = 0 ∨ ∃ σ ∈ R, f σ = v := by
  simp [vals]

/-- **The chain.**  If `x₀, y₀ ∈ V`, `x₀ < p ≤ q < y₀` and every gap of `V` inside `[x₀, y₀]` has
length at most `g ≤ q - p`, then some value of `V` lies in `[p, q]`. -/
theorem chain (V : Finset ℝ) {x₀ y₀ p q g : ℝ} (hx₀ : x₀ ∈ V) (hy₀ : y₀ ∈ V) (hxp : x₀ < p)
    (hpq : p ≤ q) (hqy : q < y₀) (hg : g ≤ q - p)
    (hgaps : ∀ v₁ v₂, IsGap V v₁ v₂ → x₀ ≤ v₁ → v₂ ≤ y₀ → v₂ - v₁ ≤ g) :
    ∃ v ∈ V, p ≤ v ∧ v ≤ q := by
  set A := V.filter (· < p)
  have hA : A.Nonempty := ⟨x₀, mem_filter.mpr ⟨hx₀, hxp⟩⟩
  set v₁ := A.max' hA
  have hv₁A : v₁ ∈ A := max'_mem A hA
  have hv₁V : v₁ ∈ V := (mem_filter.mp hv₁A).1
  have hv₁p : v₁ < p := (mem_filter.mp hv₁A).2
  have hxv₁ : x₀ ≤ v₁ := le_max' A x₀ (mem_filter.mpr ⟨hx₀, hxp⟩)
  set B := V.filter (v₁ < ·)
  have hyB : y₀ ∈ B := mem_filter.mpr ⟨hy₀, by linarith⟩
  have hB : B.Nonempty := ⟨y₀, hyB⟩
  set v₂ := B.min' hB
  have hv₂B : v₂ ∈ B := min'_mem B hB
  have hv₂V : v₂ ∈ V := (mem_filter.mp hv₂B).1
  have hv₁₂ : v₁ < v₂ := (mem_filter.mp hv₂B).2
  have hv₂y : v₂ ≤ y₀ := min'_le B y₀ hyB
  have hgap : IsGap V v₁ v₂ := ⟨hv₁V, hv₂V, hv₁₂, fun v hv ⟨h1, h2⟩ => by
    have := min'_le B v (mem_filter.mpr ⟨hv, h1⟩)
    linarith⟩
  have hlen := hgaps v₁ v₂ hgap hxv₁ hv₂y
  refine ⟨v₂, hv₂V, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := le_max' A v₂ (mem_filter.mpr ⟨hv₂V, h⟩)
    linarith
  · by_contra h
    push Not at h
    linarith

variable [DecidableEq ι]

/-- **Proposition 8.3 (`prop:gap`), the deterministic step.**  Let the expected supports have the
gap `(a, b)` between the groups: every false value is at most `a ≥ 0` (in the report `a` is the
largest false value or `0`; Lean needs only the bound), `b` is the value of a true split, every
true value is at least `b`, and every other gap of the expected values (with `0`) has length at
most `g₂`, `0 ≤ g₂ < b - a`.  If every observed value lies within `η = (b - a - g₂)/4` of its
expectation, the observed values (with `0`) have a largest gap, and the midpoint of every largest
gap separates `T` from `F` and `0`. -/
theorem gap_separation (T F : Finset ι) (m w : ι → ℝ) (a b g₂ : ℝ) (ha0 : 0 ≤ a)
    (hF : ∀ τ ∈ F, m τ ≤ a)
    (hbV : ∃ σ ∈ T, m σ = b) (hT : ∀ σ ∈ T, b ≤ m σ) (hg₂ : 0 ≤ g₂) (hG : g₂ < b - a)
    (hgaps : ∀ x y, IsGap (vals (T ∪ F) m) x y → (x, y) ≠ (a, b) → y - x ≤ g₂)
    (hdev : ∀ σ ∈ T ∪ F, |w σ - m σ| < (b - a - g₂) / 4) :
    (∃ x y, IsLargestGap (vals (T ∪ F) w) x y) ∧
      ∀ x y, IsLargestGap (vals (T ∪ F) w) x y → Separates T F w ((x + y) / 2) := by
  set η := (b - a - g₂) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set V := vals (T ∪ F) m
  set W := vals (T ∪ F) w
  set θ := (a + b) / 2
  have hdT : ∀ σ ∈ T, |w σ - m σ| < η := fun σ hσ => hdev σ (mem_union_left _ hσ)
  have hdF : ∀ τ ∈ F, |w τ - m τ| < η := fun τ hτ => hdev τ (mem_union_right _ hτ)
  -- Step A: observed true values lie above `b - η`, false ones and `0` below `a + η`
  have hwT : ∀ σ ∈ T, b - η < w σ := fun σ hσ => by
    have := (abs_lt.mp (hdT σ hσ)).1; linarith [hT σ hσ]
  have hwF : ∀ τ ∈ F, w τ < a + η := fun τ hτ => by
    have := (abs_lt.mp (hdF τ hτ)).2; linarith [hF τ hτ]
  have hsep : a + η < θ ∧ θ < b - η := by constructor <;> (simp only [θ, hη]; linarith)
  -- every observed value lies on one side of `θ`
  have hside : ∀ v ∈ W, v < a + η ∨ b - η < v := by
    intro v hv
    rcases mem_vals.mp hv with rfl | ⟨σ, hσ, rfl⟩
    · left; linarith
    · rcases mem_union.mp hσ with h | h
      · exact Or.inr (hwT σ h)
      · exact Or.inl (hwF σ h)
  -- Step B: an expected value of the same group within `η`
  have hlow : ∀ v ∈ W, v < θ → ∃ e ∈ V, e ≤ a ∧ |v - e| < η := by
    intro v hv hvθ
    rcases mem_vals.mp hv with rfl | ⟨σ, hσ, rfl⟩
    · exact ⟨0, mem_vals.mpr (Or.inl rfl), ha0, by simpa using hη0⟩
    · rcases mem_union.mp hσ with h | h
      · exact absurd hvθ (not_lt.mpr (by linarith [hwT σ h, hsep.2]))
      · exact ⟨m σ, mem_vals.mpr (Or.inr ⟨σ, hσ, rfl⟩), hF σ h, hdF σ h⟩
  have hhigh : ∀ v ∈ W, θ < v → ∃ e ∈ V, b ≤ e ∧ |v - e| < η := by
    intro v hv hvθ
    rcases mem_vals.mp hv with rfl | ⟨σ, hσ, rfl⟩
    · exact absurd hvθ (not_lt.mpr (by linarith [hsep.1]))
    · rcases mem_union.mp hσ with h | h
      · exact ⟨m σ, mem_vals.mpr (Or.inr ⟨σ, hσ, rfl⟩), hT σ h, hdT σ h⟩
      · exact absurd hvθ (not_lt.mpr (by linarith [hwF σ h, hsep.1]))
  -- Step C: every expected value has an observed value within `η`
  have hobs : ∀ e ∈ V, ∃ v ∈ W, |v - e| < η := by
    intro e he
    rcases mem_vals.mp he with rfl | ⟨σ, hσ, rfl⟩
    · exact ⟨0, mem_vals.mpr (Or.inl rfl), by simpa using hη0⟩
    · exact ⟨w σ, mem_vals.mpr (Or.inr ⟨σ, hσ, rfl⟩), hdev σ hσ⟩
  -- Step D: a gap inside one group is shorter than `g₂ + 2η`
  have hshort : ∀ x y, IsGap W x y → (y < θ ∨ θ < x) → y - x < g₂ + 2 * η := by
    rintro x y ⟨hx, hy, hxy, hnone⟩ hgrp
    by_contra hlong
    push Not at hlong
    -- expected witnesses of the same group
    obtain ⟨ex, ey, hex, hey, hdx, hdy, hin⟩ : ∃ ex ey, ex ∈ V ∧ ey ∈ V ∧ |x - ex| < η ∧
        |y - ey| < η ∧ ∀ v₁ v₂, IsGap V v₁ v₂ → ex ≤ v₁ → v₂ ≤ ey → (v₁, v₂) ≠ (a, b) := by
      rcases hgrp with h | h
      · obtain ⟨ex, hex, hexa, hdx⟩ := hlow x hx (by linarith)
        obtain ⟨ey, hey, heya, hdy⟩ := hlow y hy h
        refine ⟨ex, ey, hex, hey, hdx, hdy, fun v₁ v₂ _ _ h2 he => ?_⟩
        simp only [Prod.mk.injEq] at he
        linarith [he.2]
      · obtain ⟨ex, hex, hexb, hdx⟩ := hhigh x hx h
        obtain ⟨ey, hey, heyb, hdy⟩ := hhigh y hy (by linarith)
        refine ⟨ex, ey, hex, hey, hdx, hdy, fun v₁ v₂ _ h1 _ he => ?_⟩
        simp only [Prod.mk.injEq] at he
        linarith [he.1]
    have hdx' := abs_lt.mp hdx
    have hdy' := abs_lt.mp hdy
    obtain ⟨e, he, hpe, heq⟩ := chain V hex hey (p := x + η) (q := y - η) (g := g₂)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun v₁ v₂ hg h1 h2 => hgaps v₁ v₂ hg (hin v₁ v₂ hg h1 h2))
    obtain ⟨v, hv, hdv⟩ := hobs e he
    have := abs_lt.mp hdv
    exact hnone v hv ⟨by linarith, by linarith⟩
  -- the cross gap
  obtain ⟨σb, hσb, hmb⟩ := hbV
  set Lo := W.filter (· < θ)
  set Hi := W.filter (θ < ·)
  have h0W : (0 : ℝ) ∈ W := mem_vals.mpr (Or.inl rfl)
  have hwbW : w σb ∈ W := mem_vals.mpr (Or.inr ⟨σb, mem_union_left _ hσb, rfl⟩)
  have hLo : Lo.Nonempty := ⟨0, mem_filter.mpr ⟨h0W, by linarith [hsep.1]⟩⟩
  have hHi : Hi.Nonempty := ⟨w σb, mem_filter.mpr ⟨hwbW, by linarith [hwT σb hσb, hsep.2]⟩⟩
  set xA := Lo.max' hLo
  set yB := Hi.min' hHi
  have hxA : xA ∈ W ∧ xA < θ := mem_filter.mp (max'_mem Lo hLo)
  have hyB : yB ∈ W ∧ θ < yB := mem_filter.mp (min'_mem Hi hHi)
  have hxA' : xA < a + η := by
    rcases hside xA hxA.1 with h | h
    · exact h
    · linarith [hsep.2, hxA.2]
  have hyB' : b - η < yB := by
    rcases hside yB hyB.1 with h | h
    · linarith [hsep.1, hyB.2]
    · exact h
  have hcross : IsGap W xA yB := ⟨hxA.1, hyB.1, by linarith [hxA.2, hyB.2], fun v hv ⟨h1, h2⟩ => by
    rcases lt_or_gt_of_ne (show v ≠ θ by
        rcases hside v hv with h | h <;> intro e <;> linarith [hsep.1, hsep.2]) with h | h
    · linarith [le_max' Lo v (mem_filter.mpr ⟨hv, h⟩)]
    · linarith [min'_le Hi v (mem_filter.mpr ⟨hv, h⟩)]⟩
  have hcrossLen : g₂ + 2 * η < yB - xA := by
    have : g₂ + 2 * η = b - a - 2 * η := by rw [hη]; ring
    linarith
  -- a largest gap straddles `θ`
  have hstraddle : ∀ x y, IsLargestGap W x y → x < θ ∧ θ < y := by
    rintro x y ⟨hg, hmax⟩
    have hge := hmax xA yB hcross
    have hxW := hg.1
    have hyW := hg.2.1
    have hnx : x ≠ θ := by
      rcases hside x hxW with h | h <;> intro e <;> linarith [hsep.1, hsep.2]
    have hny : y ≠ θ := by
      rcases hside y hyW with h | h <;> intro e <;> linarith [hsep.1, hsep.2]
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    have : y < θ ∨ θ < x := by
      rcases hc with h | h
      · exact Or.inr (lt_of_le_of_ne h (Ne.symm hnx))
      · exact Or.inl (lt_of_le_of_ne h hny)
    linarith [hshort x y hg this]
  refine ⟨?_, fun x y hxy => ?_⟩
  · -- existence of a largest gap
    set G := (W ×ˢ W).filter fun p => IsGap W p.1 p.2
    have hGne : G.Nonempty := ⟨(xA, yB), mem_filter.mpr ⟨mem_product.mpr ⟨hxA.1, hyB.1⟩, hcross⟩⟩
    obtain ⟨p, hp, hpmax⟩ := exists_max_image G (fun p => p.2 - p.1) hGne
    refine ⟨p.1, p.2, (mem_filter.mp hp).2, fun x' y' hg' => ?_⟩
    exact hpmax (x', y') (mem_filter.mpr ⟨mem_product.mpr ⟨hg'.1, hg'.2.1⟩, hg'⟩)
  · obtain ⟨hxθ, hθy⟩ := hstraddle x y hxy
    obtain ⟨⟨hxW, hyW, hlt, hnone⟩, -⟩ := hxy
    refine ⟨?_, fun σ hσ => ?_, fun τ hτ => ?_⟩
    · have : (0 : ℝ) ≤ x := by
        by_contra h
        push Not at h
        exact hnone 0 h0W ⟨h, by linarith [hsep.1]⟩
      linarith
    · have hσW : w σ ∈ W := mem_vals.mpr (Or.inr ⟨σ, mem_union_left _ hσ, rfl⟩)
      have : y ≤ w σ := by
        by_contra h
        push Not at h
        exact hnone _ hσW ⟨by linarith [hwT σ hσ, hsep.2], h⟩
      linarith
    · have hτW : w τ ∈ W := mem_vals.mpr (Or.inr ⟨τ, mem_union_right _ hτ, rfl⟩)
      have : w τ ≤ x := by
        by_contra h
        push Not at h
        exact hnone _ hτW ⟨h, by linarith [hwF τ hτ, hsep.1]⟩
      linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Proposition 8.3 (`prop:gap`), largest-gap threshold.**  Under the hypotheses of
`gap_separation` on the expected supports, let `L` units be independent for each split,
`Y σ u ∈ [0,1]` indicating that unit `u` proposes `σ`, with mean `m σ`.  The probability that the
observed values `w(σ)/L` (with `0`) have no largest gap, or that the midpoint of some largest gap
does not separate `T` from `F`, is at most `2 (|T| + |F|) exp(-L (G - g₂)²/8)`, `G = b - a`. -/
theorem gap_threshold (T F : Finset ι) (m : ι → ℝ) (a b g₂ : ℝ) (ha0 : 0 ≤ a)
    (hF : ∀ τ ∈ F, m τ ≤ a)
    (hbV : ∃ σ ∈ T, m σ = b) (hT : ∀ σ ∈ T, b ≤ m σ) (hg₂ : 0 ≤ g₂) (hG : g₂ < b - a)
    (hgaps : ∀ x y, IsGap (vals (T ∪ F) m) x y → (x, y) ≠ (a, b) → y - x ≤ g₂)
    {L : ℕ} (hL : 0 < L) (Y : ι → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ) :
    μ.real {ω | ¬ ((∃ x y, IsLargestGap (vals (T ∪ F) fun σ => (∑ u, Y σ u ω) / L) x y) ∧
        ∀ x y, IsLargestGap (vals (T ∪ F) fun σ => (∑ u, Y σ u ω) / L) x y →
          Separates T F (fun σ => (∑ u, Y σ u ω) / L) ((x + y) / 2))} ≤
      2 * (T.card + F.card) * exp (-L * (b - a - g₂) ^ 2 / 8) := by
  set η := (b - a - g₂) / 4
  have hη0 : 0 < η := by simp only [η]; linarith
  set A : ι → Set Ω := fun σ => {ω | η ≤ |(∑ u, Y σ u ω) / L - m σ|}
  have hsub : {ω | ¬ ((∃ x y, IsLargestGap (vals (T ∪ F) fun σ => (∑ u, Y σ u ω) / L) x y) ∧
      ∀ x y, IsLargestGap (vals (T ∪ F) fun σ => (∑ u, Y σ u ω) / L) x y →
        Separates T F (fun σ => (∑ u, Y σ u ω) / L) ((x + y) / 2))} ⊆ ⋃ σ ∈ T ∪ F, A σ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, A, Set.mem_setOf_eq, not_le] at hnot
    exact hω (gap_separation T F m _ a b g₂ ha0 hF hbV hT hg₂ hG hgaps hnot)
  have hcard : ((T ∪ F).card : ℝ) ≤ T.card + F.card := by exact_mod_cast card_union_le T F
  calc _ ≤ μ.real (⋃ σ ∈ T ∪ F, A σ) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ σ ∈ T ∪ F, μ.real (A σ) := measureReal_biUnion_finset_le _ A
    _ ≤ ∑ σ ∈ T ∪ F, 2 * exp (-2 * L * η ^ 2) :=
        sum_le_sum fun σ _ =>
          Consistency.two_tail hL (Y σ) (m σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) hη0.le
    _ = (T ∪ F).card * (2 * exp (-L * (b - a - g₂) ^ 2 / 8)) := by
        rw [sum_const, nsmul_eq_mul]; congr 3; simp only [η]; ring
    _ ≤ (T.card + F.card) * (2 * exp (-L * (b - a - g₂) ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (T.card + F.card) * exp (-L * (b - a - g₂) ^ 2 / 8) := by ring

end Stemma.GapThreshold
