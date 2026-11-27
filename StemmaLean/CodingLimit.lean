/-
The coding theorem as the number of units grows: Theorem 8.6(a) and (b) of the technical report
(`thm:coding`), from the expected-support orderings of `Coding.lean`.

`Coding.lean` proves, for every sufficiently small `ε > 0`, which family set has the largest
expected support.  Here the units are added.  The units propose families with the expected
supports of the attraction model on the quartet (`mU` for the unrooted splits, `Coding.m` for the
rooted clusters); the hypotheses are that their indicators are `[0,1]`-valued, independent across
units, with those means.

* (a), unrooted: if `ab < 2ρ`, the estimator is consistent, with failure probability at most
  `6 e^{-L γ²/2}` for some `γ > 0` (`unrooted_consistency`, from Theorem 7.4(a)); if `ab > 2ρ`
  (and `a, b > 0`), almost surely the false split `13|24` is eventually the unique maximum, and
  the probability that it is tends to one (`unrooted_false_selected`, from the strong law).
* (b), rooted: if `α²ab < 2ρ`, consistent, with failure probability at most `20 e^{-L γ²/2}`
  (`rooted_consistency`); if `α²ab > 2ρ`, almost surely the true family set is eventually lighter
  than the single cluster `{1,3}`, and the probability that it is a maximum tends to zero
  (`rooted_inconsistency`); and (for `ρ ≥ 0`) almost surely every maximum-weight laminar family
  eventually contains `{1,3}`, the probability that some optimum omits it tending to zero
  (`rooted_selects_13`).
* The companion quartet of the mathematical paper (Corollary 4.5, irreversible model): in the two
  strict cases of the long-branch boundary, consistency (`long_branch_consistent`) or selection of
  the false split `13|24` (`long_branch_inconsistent`).

On four witnesses the three non-trivial splits are the sides `{0,1}` (`12|34`), `{0,2}` (`13|24`)
and `{1,2}` (`14|23`, read from witness `4`), away from the reference witness `3` (witness `4`).
The law of the units is the hypothesis on their means: the attraction model itself is the finite
sum of `Quartet.lean`, not a measure built here.
-/
import Mathlib
import StemmaLean.Coding
import StemmaLean.Margin

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped Classical

namespace Stemma.CodingLimit

open Stemma.Splits Stemma.Quartet Stemma.Coding

/-! ### The strong law for two family sets, over any index of families -/

section slln

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If `m(S) > m(T)`, then almost surely `w(S) > w(T)` for all large `L` (Etemadi's strong law,
pairwise independence). -/
theorem ae_eventually_lt {ι : Type*} [Fintype ι] (Y : ι → ℕ → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hindep : Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ)
    (hident : ∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ)
    (m : ι → ℝ) (hmean : ∀ σ, μ[Y σ 0] = m σ) (T S : Finset ι)
    (hlt : ∑ σ ∈ T, m σ < ∑ σ ∈ S, m σ) :
    ∀ᵐ ω ∂μ, ∀ᶠ L in atTop,
      ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω := by
  set g : (ι → ℝ) → ℝ := fun v => ∑ σ ∈ S, v σ - ∑ σ ∈ T, v σ
  have hg : Measurable g :=
    (Finset.measurable_sum S fun σ _ => measurable_pi_apply σ).sub
      (Finset.measurable_sum T fun σ _ => measurable_pi_apply σ)
  set D : ℕ → Ω → ℝ := fun u ω => g (fun σ => Y σ u ω)
  have hYint : ∀ σ u, Integrable (Y σ u) μ := fun σ u =>
    Integrable.of_mem_Icc 0 1 (hmeas σ u).aemeasurable (ae_of_all _ (hb σ u))
  have hint : Integrable (D 0) μ := by
    simp only [D, g]
    exact (integrable_finsetSum S fun σ _ => hYint σ 0).sub
      (integrable_finsetSum T fun σ _ => hYint σ 0)
  have hmeanD : μ[D 0] = ∑ σ ∈ S, m σ - ∑ σ ∈ T, m σ := by
    simp only [D, g]
    rw [integral_sub (integrable_finsetSum S fun σ _ => hYint σ 0)
      (integrable_finsetSum T fun σ _ => hYint σ 0), integral_finsetSum S fun σ _ => hYint σ 0,
      integral_finsetSum T fun σ _ => hYint σ 0]
    simp [hmean]
  have H := strong_law_ae (μ := μ) D hint (fun i j hij => (hindep hij).comp hg hg)
    (fun u => (hident u).comp hg)
  have hsum : ∀ L ω, ∑ u ∈ range L, D u ω =
      ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω - ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω := by
    intro L ω
    simp only [D, g, sum_sub_distrib]
    rw [sum_comm, sum_comm (s := range L)]
  filter_upwards [H] with ω hω
  rw [hmeanD] at hω
  have hev := hω.eventually (lt_mem_nhds (sub_pos.mpr hlt))
  filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
  rw [smul_eq_mul, hsum] at hL
  have := (mul_pos_iff_of_pos_left (inv_pos.mpr hLpos)).mp hL
  linarith

lemma measurable_W {ι : Type*} {Y : ι → ℕ → Ω → ℝ} (hmeas : ∀ σ u, Measurable (Y σ u))
    (U : Finset ι) (L : ℕ) : Measurable fun ω => ∑ σ ∈ U, ∑ u ∈ range L, Y σ u ω :=
  Finset.measurable_sum U fun σ _ => Finset.measurable_sum _ fun u _ => hmeas σ u

end slln

/-! ### (a) The unrooted coding -/

/-- The three non-trivial splits of four witnesses, by their sides away from witness `4`. -/
def s12 : Finset (Fin 4) := {0, 1}
/-- `13|24`. -/
def s13 : Finset (Fin 4) := {0, 2}
/-- `14|23`, by its side `{2,3}`. -/
def s14 : Finset (Fin 4) := {1, 2}

lemma sides_four (σ : Finset (Fin 4)) (h : IsSide 3 σ) : σ = s12 ∨ σ = s13 ∨ σ = s14 := by
  revert σ; unfold IsSide Nontriv; decide

/-- The expected unrooted supports of the attraction model on the quartet. -/
noncomputable def mU (ρ a b α ε : ℝ) (σ : Finset (Fin 4)) : ℝ :=
  if σ = s12 then sU U12 ρ a b α ε else if σ = s13 then sU U13 ρ a b α ε
  else if σ = s14 then sU U14 ρ a b α ε else 0

lemma mU12 (ρ a b α ε : ℝ) : mU ρ a b α ε s12 = sU U12 ρ a b α ε := by simp [mU]
lemma mU13 (ρ a b α ε : ℝ) : mU ρ a b α ε s13 = sU U13 ρ a b α ε := by
  have h1 : s13 ≠ s12 := by decide
  simp [mU, h1]
lemma mU14 (ρ a b α ε : ℝ) : mU ρ a b α ε s14 = sU U14 ρ a b α ε := by
  have h1 : s14 ≠ s12 := by decide
  have h2 : s14 ≠ s13 := by decide
  simp [mU, h1, h2]

/-- On four witnesses, a system has at most one split. -/
lemma system_four {S : Finset (Finset (Fin 4))} (hS : IsSystem 3 S) :
    S = ∅ ∨ ∃ σ, IsSide 3 σ ∧ S = {σ} := by
  have h : S.card ≤ 1 := by have := card_le hS; simpa using this
  rcases Nat.lt_or_ge S.card 1 with h0 | h1
  · left; exact card_eq_zero.mp (by omega : S.card = 0)
  · right
    obtain ⟨σ, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
    exact ⟨σ, hS.1 σ (mem_singleton_self σ), rfl⟩

lemma binary_s12 : IsBinary 3 {s12} := by
  refine ⟨⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩, by simp⟩
  · rw [mem_singleton.mp hA]; unfold IsSide Nontriv s12; decide
  · exact absurd ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm) hab

lemma eventually_pos12 (ρ a b α : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < sU U12 ρ a b α ε := by
  filter_upwards [eventually_pos (cont_U12 ρ a b α) (by rw [zero_U12]; linarith)] with ε h
  simpa only [sU, scale_U12] using h

/-- **Theorem 8.6(a), consistent side.**  If `ab < 2ρ` (`ρ > 0`), then for every sufficiently
small `ε > 0` there is `γ > 0` such that, for units with the expected unrooted supports of the
attraction model, the estimator misses the true split `12|34` with probability at most
`6 e^{-L γ²/2}`, whatever `α`. -/
theorem unrooted_consistency (ρ a b α : ℝ) (hρ : 0 < ρ) (h : a * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ σ, iIndepFun (Y σ) μ) → (∀ σ u, μ[Y σ u] = mU ρ a b α ε σ) →
      (∀ σ, σ ≠ s12 → σ ≠ s13 → σ ≠ s14 → ∀ u ω, Y σ u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {s12} ∧
        ∑ σ ∈ {s12}, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  filter_upwards [unrooted_consistent ρ a b α hρ h, eventually_pos12 ρ a b α hρ] with ε hε h0
  obtain ⟨h13, h14⟩ := hε
  set m := mU ρ a b α ε
  set γ := min (min (m s12 - m s13) (m s12 - m s14)) (m s12)
  have hγ : 0 < γ := by
    simp only [γ, m, mU12, mU13, mU14, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, h0⟩
  refine ⟨γ, hγ, fun Ω _ μ _ L hL Y hmeas hb hind hmean hR => ?_⟩
  have hgap : ∀ S, IsSystem 3 S → S ≠ {s12} →
      γ * ({s12} \ S).card ≤ ∑ σ ∈ {s12} \ S, m σ - ∑ σ ∈ S \ {s12}, m σ := by
    intro S hS hne
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sdiff_empty, empty_sdiff, card_singleton, sum_singleton, sum_empty]
      have := min_le_right (min (m s12 - m s13) (m s12 - m s14)) (m s12)
      push_cast; linarith
    · have hσ12 : σ ≠ s12 := fun e => hne (by rw [e])
      have e1 : ({s12} : Finset (Finset (Fin 4))) \ {σ} = {s12} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr fun e => hσ12 e.symm)
      have e2 : ({σ} : Finset (Finset (Fin 4))) \ {s12} = {σ} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr hσ12)
      rw [e1, e2, card_singleton, sum_singleton, sum_singleton]
      push_cast
      rcases sides_four σ hσ with rfl | rfl | rfl
      · exact absurd rfl hσ12
      · have := min_le_left (min (m s12 - m s13) (m s12 - m s14)) (m s12)
        have := min_le_left (m s12 - m s13) (m s12 - m s14)
        linarith
      · have := min_le_left (min (m s12 - m s13) (m s12 - m s14)) (m s12)
        have := min_le_right (m s12 - m s13) (m s12 - m s14)
        linarith
  have := Consistency.consistency (μ := μ) 3 {s12} binary_s12 m γ hγ hgap hL Y hmeas hb hind
    hmean {s12, s13, s14}
    (fun σ hσ u ω => by
      simp only [mem_insert, mem_singleton, not_or] at hσ
      exact hR σ hσ.1 hσ.2.1 hσ.2.2 u ω)
    (fun σ hσ => by
      simp only [mem_insert, mem_singleton, not_or] at hσ
      simp [m, mU, hσ.1, hσ.2.1, hσ.2.2])
  have hc : (({s12, s13, s14} : Finset (Finset (Fin 4))).card : ℝ) = 3 := by
    rw [card_insert_of_notMem (by simp [s12, s13, s14] ; decide),
      card_insert_of_notMem (by simp [s13, s14]; decide), card_singleton]; norm_num
  rw [hc] at this
  exact this

/-- **Theorem 8.6(a), inconsistent side.**  If `ab > 2ρ` (`a, b > 0`), then for every
sufficiently small `ε > 0`, for i.i.d. units with the expected unrooted supports of the attraction
model, almost surely the false split `13|24` is eventually strictly heavier than every other
compatible set (so it is selected), and the probability that it is tends to one. -/
theorem unrooted_false_selected (ρ a b α : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 2 * ρ < a * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ) →
      (∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ) →
      (∀ σ, μ[Y σ 0] = mU ρ a b α ε σ) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω}ᶜ) atTop
        (𝓝 0) := by
  filter_upwards [unrooted_inconsistent ρ a b α ha hb h] with ε hε
  obtain ⟨h12, h14⟩ := hε
  intro Ω _ μ _ Y hmeas hb01 hindep hident hmean
  have e12 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {s12} {s13}
    (by simp only [sum_singleton, mU12, mU13]; exact h12)
  have e14 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {s14} {s13}
    (by simp only [sum_singleton, mU14, mU13]; exact h14)
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
      ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω := by
    filter_upwards [e12, e14] with ω h1 h2
    filter_upwards [h1, h2] with L hL1 hL2 S hS hne
    have hpos : 0 ≤ ∑ σ ∈ {s12}, ∑ u ∈ range L, Y σ u ω :=
      sum_nonneg fun σ _ => sum_nonneg fun u _ => (hb01 σ u ω).1
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sum_empty]; linarith
    · rcases sides_four σ hσ with rfl | rfl | rfl
      · exact hL1
      · exact absurd rfl hne
      · exact hL2
  refine ⟨hae, ?_⟩
  have hG : ∀ L, MeasurableSet {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
      ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω} := by
    intro L
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun S => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_W hmeas S L) (measurable_W hmeas _ L)
  exact Cutting.prob_tendsto_of_ae_eventually hG hae

/-! ### The companion quartet: the irreversible model (Corollary 4.5 of the mathematical paper)

The same argument for any expected supports with a strict order, applied to the quartet of
`Quartet.lean` under the irreversible model, with `p₂ = p₄ = 0` and halves of equal rate `r`.  The
tie `(1 - r) p₁ p₃ = r (2 - p₁ - p₃)` is not covered. -/

/-- Consistency for any unrooted expected supports on four witnesses with `m₁₂` the strict
maximum and positive. -/
theorem quartet_consistency (m : Finset (Fin 4) → ℝ) (h13 : m s13 < m s12) (h14 : m s14 < m s12)
    (h0 : 0 < m s12) (hz : ∀ σ, σ ≠ s12 → σ ≠ s13 → σ ≠ s14 → m σ = 0) :
    ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ σ, iIndepFun (Y σ) μ) → (∀ σ u, μ[Y σ u] = m σ) →
      (∀ σ, σ ≠ s12 → σ ≠ s13 → σ ≠ s14 → ∀ u ω, Y σ u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {s12} ∧
        ∑ σ ∈ {s12}, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  set γ := min (min (m s12 - m s13) (m s12 - m s14)) (m s12)
  have hγ : 0 < γ := by
    simp only [γ, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, h0⟩
  refine ⟨γ, hγ, fun Ω _ μ _ L hL Y hmeas hb hind hmean hR => ?_⟩
  have hgap : ∀ S, IsSystem 3 S → S ≠ {s12} →
      γ * ({s12} \ S).card ≤ ∑ σ ∈ {s12} \ S, m σ - ∑ σ ∈ S \ {s12}, m σ := by
    intro S hS hne
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sdiff_empty, empty_sdiff, card_singleton, sum_singleton, sum_empty]
      have := min_le_right (min (m s12 - m s13) (m s12 - m s14)) (m s12)
      push_cast; linarith
    · have hσ12 : σ ≠ s12 := fun e => hne (by rw [e])
      have e1 : ({s12} : Finset (Finset (Fin 4))) \ {σ} = {s12} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr fun e => hσ12 e.symm)
      have e2 : ({σ} : Finset (Finset (Fin 4))) \ {s12} = {σ} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr hσ12)
      rw [e1, e2, card_singleton, sum_singleton, sum_singleton]
      push_cast
      rcases sides_four σ hσ with rfl | rfl | rfl
      · exact absurd rfl hσ12
      · have := min_le_left (min (m s12 - m s13) (m s12 - m s14)) (m s12)
        have := min_le_left (m s12 - m s13) (m s12 - m s14)
        linarith
      · have := min_le_left (min (m s12 - m s13) (m s12 - m s14)) (m s12)
        have := min_le_right (m s12 - m s13) (m s12 - m s14)
        linarith
  have := Consistency.consistency (μ := μ) 3 {s12} binary_s12 m γ hγ hgap hL Y hmeas hb hind
    hmean {s12, s13, s14}
    (fun σ hσ u ω => by
      simp only [mem_insert, mem_singleton, not_or] at hσ
      exact hR σ hσ.1 hσ.2.1 hσ.2.2 u ω)
    (fun σ hσ => by
      simp only [mem_insert, mem_singleton, not_or] at hσ
      exact hz σ hσ.1 hσ.2.1 hσ.2.2)
  have hc : (({s12, s13, s14} : Finset (Finset (Fin 4))).card : ℝ) = 3 := by
    rw [card_insert_of_notMem (by simp [s12, s13, s14] ; decide),
      card_insert_of_notMem (by simp [s13, s14]; decide), card_singleton]; norm_num
  rw [hc] at this
  exact this

/-- Selection of `13|24` for any unrooted expected supports on four witnesses with `m₁₃` the
strict maximum: almost surely it is eventually strictly heavier than every other compatible set,
and the probability that it is not tends to zero. -/
theorem quartet_false_selected (m : Finset (Fin 4) → ℝ) (h12 : m s12 < m s13)
    (h14 : m s14 < m s13) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ) →
      (∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ) →
      (∀ σ, μ[Y σ 0] = m σ) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω}ᶜ) atTop
        (𝓝 0) := by
  intro Ω _ μ _ Y hmeas hb01 hindep hident hmean
  have e12 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {s12} {s13}
    (by simp only [sum_singleton]; exact h12)
  have e14 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {s14} {s13}
    (by simp only [sum_singleton]; exact h14)
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
      ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω := by
    filter_upwards [e12, e14] with ω h1 h2
    filter_upwards [h1, h2] with L hL1 hL2 S hS hne
    have hpos : 0 ≤ ∑ σ ∈ {s12}, ∑ u ∈ range L, Y σ u ω :=
      sum_nonneg fun σ _ => sum_nonneg fun u _ => (hb01 σ u ω).1
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sum_empty]; linarith
    · rcases sides_four σ hσ with rfl | rfl | rfl
      · exact hL1
      · exact absurd rfl hne
      · exact hL2
  refine ⟨hae, ?_⟩
  have hG : ∀ L, MeasurableSet {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
      ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω} := by
    intro L
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun S => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_W hmeas S L) (measurable_W hmeas _ L)
  exact Cutting.prob_tendsto_of_ae_eventually hG hae

/-- The expected supports of the irreversible model on the quartet, `p₂ = p₄ = 0`, halves of
equal rate `r` (Proposition 4.4). -/
noncomputable def mQ (r p₁ p₃ : ℝ) (σ : Finset (Fin 4)) : ℝ :=
  if σ = s12 then Quartet.supp r r p₁ 0 p₃ 0 Quartet.P12
  else if σ = s13 then Quartet.supp r r p₁ 0 p₃ 0 Quartet.P13
  else if σ = s14 then Quartet.supp r r p₁ 0 p₃ 0 Quartet.P14 else 0

lemma mQ12 (r p₁ p₃ : ℝ) : mQ r p₁ p₃ s12 = Quartet.supp r r p₁ 0 p₃ 0 Quartet.P12 := by
  simp [mQ]
lemma mQ13 (r p₁ p₃ : ℝ) : mQ r p₁ p₃ s13 = Quartet.supp r r p₁ 0 p₃ 0 Quartet.P13 := by
  have h1 : s13 ≠ s12 := by decide
  simp [mQ, h1]
lemma mQ14 (r p₁ p₃ : ℝ) : mQ r p₁ p₃ s14 = Quartet.supp r r p₁ 0 p₃ 0 Quartet.P14 := by
  have h1 : s14 ≠ s12 := by decide
  have h2 : s14 ≠ s13 := by decide
  simp [mQ, h1, h2]
lemma mQ_off (r p₁ p₃ : ℝ) (σ : Finset (Fin 4)) (h1 : σ ≠ s12) (h2 : σ ≠ s13) (h3 : σ ≠ s14) :
    mQ r p₁ p₃ σ = 0 := by
  simp [mQ, h1, h2, h3]

/-- **Corollary 4.5 (textual long-branch zone), consistent side, with units.**  If
`(1 - r) p₁ p₃ < r (2 - p₁ - p₃)` (`r < 1`, `p₁, p₃ ≥ 0`), there is `γ > 0` such that, for units
with the expected supports of the irreversible model, the estimator misses `12|34` with
probability at most `6 e^{-L γ²/2}`. -/
theorem long_branch_consistent (r p₁ p₃ : ℝ) (hr : r < 1) (hp₁ : 0 ≤ p₁) (hp₃ : 0 ≤ p₃)
    (h : (1 - r) * p₁ * p₃ < r * (2 - p₁ - p₃)) :
    ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ σ, iIndepFun (Y σ) μ) → (∀ σ u, μ[Y σ u] = mQ r p₁ p₃ σ) →
      (∀ σ, σ ≠ s12 → σ ≠ s13 → σ ≠ s14 → ∀ u ω, Y σ u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {s12} ∧
        ∑ σ ∈ {s12}, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  have hlb := (Quartet.long_branch r p₁ p₃ hr hp₁ hp₃).mpr h
  rw [max_lt_iff] at hlb
  have h13 : 0 ≤ Quartet.supp r r p₁ 0 p₃ 0 Quartet.P13 := by
    rw [Quartet.m13]; nlinarith [mul_nonneg (mul_nonneg hp₁ hp₃) (sq_nonneg (1 - r))]
  refine quartet_consistency _ ?_ ?_ ?_ (mQ_off r p₁ p₃)
  · rw [mQ13, mQ12]; exact hlb.1
  · rw [mQ14, mQ12]; exact hlb.2
  · rw [mQ12]; linarith [hlb.1]

/-- **Corollary 4.5 (textual long-branch zone), inconsistent side, with units.**  If
`r (2 - p₁ - p₃) < (1 - r) p₁ p₃` (`0 ≤ r < 1`, `p₁, p₃ ∈ [0,1]`), then for i.i.d. units with the
expected supports of the irreversible model, almost surely the false split `13|24` is eventually
strictly heavier than every other compatible set, and the probability that it is not tends to
zero. -/
theorem long_branch_inconsistent (r p₁ p₃ : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (hp₁ : 0 ≤ p₁)
    (hp₁' : p₁ ≤ 1) (hp₃ : 0 ≤ p₃) (hp₃' : p₃ ≤ 1)
    (h : r * (2 - p₁ - p₃) < (1 - r) * p₁ * p₃) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ σ u, Measurable (Y σ u)) → (∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ) →
      (∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ) →
      (∀ σ, μ[Y σ 0] = mQ r p₁ p₃ σ) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {s13} →
        ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ {s13}, ∑ u ∈ range L, Y σ u ω}ᶜ) atTop
        (𝓝 0) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hr2 : 0 ≤ r * (2 - p₁ - p₃) := mul_nonneg hr0 (by linarith)
  refine quartet_false_selected _ ?_ ?_
  · rw [mQ12, mQ13, Quartet.m12, Quartet.m13]
    have key : (1 - (r:ℝ)) * (1 - p₃) * (1 - 0) * (r + (1 - r) * p₁ * 0) +
        (1 - r) * (1 - p₁) * (1 - 0) * (r + (1 - r) * p₃ * 0) -
        (1 - r) * (1 - r) * (p₁ * p₃ * (1 - 0) * (1 - 0) + 0 * 0 * (1 - p₁) * (1 - p₃)) =
        (1 - r) * (r * (2 - p₁ - p₃) - (1 - r) * p₁ * p₃) := by ring
    have : (1 - r) * (r * (2 - p₁ - p₃) - (1 - r) * p₁ * p₃) < 0 :=
      mul_neg_of_pos_of_neg h1 (by linarith)
    linarith
  · rw [mQ14, mQ13, Quartet.m13, Quartet.m14]
    have : 0 < (1 - r) * ((1 - r) * p₁ * p₃) := mul_pos h1 (by linarith)
    nlinarith

/-! ### (b) The rooted coding -/

/-- On four witnesses a laminar family of proper clusters has at most two members. -/
lemma laminar_card {F : Finset (Fin 10)} (hF : Coding.Laminar F) : F.card ≤ 2 := by
  by_contra hc
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := two_lt_card.mp (by omega : 2 < F.card)
  have key : ∀ i j k : Fin 10, i ≠ j → i ≠ k → j ≠ k → lam i j → lam i k → lam j k → False := by
    decide
  exact key i j k hij hik hjk (hF i hi j hj) (hF i hi k hk) (hF j hj k hk)

lemma T_card : T.card = 2 := by decide

/-- The rooted competitors of `T`. -/
noncomputable def rcomp : Finset (Finset (Fin 10)) := univ.filter fun F => Coding.Laminar F ∧ F ≠ T

lemma rcomp_nonempty : rcomp.Nonempty :=
  ⟨∅, mem_filter.mpr ⟨mem_univ _, fun i hi => absurd hi (notMem_empty i), by decide⟩⟩

lemma match_T {F : Finset (Fin 10)} (hF : Coding.Laminar F) (hne : F ≠ T) :
    (T \ F).Nonempty ∧ (F \ T).card ≤ (T \ F).card := by
  have hFc := laminar_card hF
  have hTF : ¬ T ⊆ F := fun h => hne (eq_of_subset_of_card_le h (by rw [T_card]; exact hFc)).symm
  refine ⟨by rwa [sdiff_nonempty], ?_⟩
  have h1 := card_sdiff_add_card_inter F T
  have h2 := card_sdiff_add_card_inter T F
  rw [inter_comm] at h1
  rw [T_card] at h2
  omega

/-- **Theorem 8.6(b), consistent side.**  If `α²ab < 2ρ` (`ρ > 0`), then for every sufficiently
small `ε > 0` there is `γ > 0` such that, for units proposing the ten proper clusters with the
expected rooted supports of the attraction model, the estimator over laminar families misses the
true clusters `{1,2}`, `{3,4}` with probability at most `20 e^{-L γ²/2}`. -/
theorem rooted_consistency (ρ a b α : ℝ) (hρ : 0 < ρ) (h : a * α ^ 2 * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Fin 10 → Fin L → Ω → ℝ,
      (∀ c u, Measurable (Y c u)) → (∀ c u ω, Y c u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ c, iIndepFun (Y c) μ) → (∀ c u, μ[Y c u] = m ρ a b α ε c) →
      μ.real {ω | ∃ F, Coding.Laminar F ∧ F ≠ T ∧
        ∑ c ∈ T, (∑ u, Y c u ω) / L ≤ ∑ c ∈ F, (∑ u, Y c u ω) / L} ≤
        2 * 10 * exp (-L * γ ^ 2 / 2) := by
  filter_upwards [rooted_consistent ρ a b α hρ h] with ε hε
  set mm := m ρ a b α ε
  set γ := rcomp.inf' rcomp_nonempty fun F => (∑ c ∈ T \ F, mm c - ∑ c ∈ F \ T, mm c) / (T \ F).card
  have hdiff : ∀ F, Coding.Laminar F → F ≠ T → 0 < ∑ c ∈ T \ F, mm c - ∑ c ∈ F \ T, mm c := by
    intro F hF hne
    have := hε F hF hne
    simp only [Coding.weight] at this
    have e := sum_sdiff_sub_sum_sdiff (s₁ := F) (s₂ := T) (f := mm)
    linarith
  have hγ : 0 < γ := by
    rw [lt_inf'_iff]
    intro F hF
    simp only [rcomp, mem_filter, mem_univ, true_and] at hF
    exact div_pos (hdiff F hF.1 hF.2)
      (by exact_mod_cast card_pos.mpr (match_T hF.1 hF.2).1)
  refine ⟨γ, hγ, fun Ω _ μ _ L hL Y hmeas hb hind hmean => ?_⟩
  have hgap : ∀ F, Coding.Laminar F → F ≠ T →
      γ * (T \ F).card ≤ ∑ c ∈ T \ F, mm c - ∑ c ∈ F \ T, mm c := by
    intro F hF hne
    have hpos : (0 : ℝ) < (T \ F).card := by exact_mod_cast card_pos.mpr (match_T hF hne).1
    have := inf'_le (fun F => (∑ c ∈ T \ F, mm c - ∑ c ∈ F \ T, mm c) / (T \ F).card)
      (by simp [rcomp, hF, hne] : F ∈ rcomp)
    rwa [le_div_iff₀ hpos] at this
  have := Consistency.consistency_of_matching (μ := μ) Coding.Laminar T mm γ hγ
    (fun F hF hne => match_T hF hne) hgap hL Y hmeas hb hind hmean univ
    (fun c hc => absurd (mem_univ c) hc) (fun c hc => absurd (mem_univ c) hc)
  rw [card_univ, Fintype.card_fin] at this
  push_cast at this
  exact this

/-- **Theorem 8.6(b), inconsistent side.**  If `α²ab > 2ρ`, then for every sufficiently small
`ε > 0`, for i.i.d. units with the expected rooted supports, almost surely the single cluster
`{1,3}` is eventually heavier than the true family set, and the probability that the true family
set is a maximum over laminar families tends to zero. -/
theorem rooted_inconsistency (ρ a b α : ℝ) (h : 2 * ρ < a * α ^ 2 * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Fin 10 → ℕ → Ω → ℝ),
      (∀ c u, Measurable (Y c u)) → (∀ c u ω, Y c u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω c => Y c i ω) (fun ω c => Y c j ω) μ) →
      (∀ u, IdentDistrib (fun ω c => Y c u ω) (fun ω c => Y c 0 ω) μ μ) →
      (∀ c, μ[Y c 0] = m ρ a b α ε c) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop,
        ∑ c ∈ T, ∑ u ∈ range L, Y c u ω < ∑ c ∈ {1}, ∑ u ∈ range L, Y c u ω) ∧
      Tendsto (fun L => μ {ω | ∀ F, Coding.Laminar F →
        ∑ c ∈ F, ∑ u ∈ range L, Y c u ω ≤ ∑ c ∈ T, ∑ u ∈ range L, Y c u ω}) atTop (𝓝 0) := by
  filter_upwards [rooted_inconsistent ρ a b α h] with ε hε
  intro Ω _ μ _ Y hmeas hb hindep hident hmean
  have hae := ae_eventually_lt Y hmeas hb hindep hident _ hmean T {1} hε
  refine ⟨hae, ?_⟩
  have hP := Cutting.prob_tendsto_of_ae_eventually (μ := μ)
    (G := fun L => {ω | ∑ c ∈ T, ∑ u ∈ range L, Y c u ω < ∑ c ∈ {1}, ∑ u ∈ range L, Y c u ω})
    (fun L => measurableSet_lt (measurable_W hmeas T L) (measurable_W hmeas _ L)) hae
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP (fun _ => zero_le)
    fun L => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt] at hω ⊢
  exact hω {1} (by intro i hi j hj; rw [mem_singleton.mp hi, mem_singleton.mp hj]; decide)

/-- **Theorem 8.6(b), inconsistent side, every optimum contains `{1,3}`.** If `α²ab > 2ρ` (with
`ρ ≥ 0`), then almost surely, for all large `L`, every maximum-weight laminar family contains the
cluster `{1,3}`, and the probability that some maximum-weight laminar family omits `{1,3}` tends
to zero.  From `Coding.rooted_optimum_contains_13` and the strong law, over the finitely many
laminar families. -/
theorem rooted_selects_13 (ρ a b α : ℝ) (hρ : 0 ≤ ρ) (h : 2 * ρ < a * α ^ 2 * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Fin 10 → ℕ → Ω → ℝ),
      (∀ c u, Measurable (Y c u)) → (∀ c u ω, Y c u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω c => Y c i ω) (fun ω c => Y c j ω) μ) →
      (∀ u, IdentDistrib (fun ω c => Y c u ω) (fun ω c => Y c 0 ω) μ μ) →
      (∀ c, μ[Y c 0] = m ρ a b α ε c) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ F, Coding.Laminar F →
        (∀ F', Coding.Laminar F' →
          ∑ c ∈ F', ∑ u ∈ range L, Y c u ω ≤ ∑ c ∈ F, ∑ u ∈ range L, Y c u ω) →
        (1 : Fin 10) ∈ F) ∧
      Tendsto (fun L => μ {ω | ∃ F, Coding.Laminar F ∧
        (∀ F', Coding.Laminar F' →
          ∑ c ∈ F', ∑ u ∈ range L, Y c u ω ≤ ∑ c ∈ F, ∑ u ∈ range L, Y c u ω) ∧
        (1 : Fin 10) ∉ F}) atTop (𝓝 0) := by
  filter_upwards [rooted_optimum_contains_13 ρ a b α hρ h] with ε hε
  intro Ω _ μ _ Y hmeas hb hindep hident hmean
  -- the event that every laminar family omitting `{1,3}` is lighter than `{1,3}`
  set G : ℕ → Set Ω := fun L => {ω | ∀ F : Finset (Fin 10), Coding.Laminar F →
    (1 : Fin 10) ∉ F → ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ {1}, ∑ u ∈ range L, Y c u ω}
  have hGm : ∀ L, MeasurableSet (G L) := by
    intro L
    simp only [G, Set.ofPred_forall]
    exact MeasurableSet.iInter fun F => MeasurableSet.iInter fun _ => MeasurableSet.iInter
      fun _ => measurableSet_lt (measurable_W hmeas F L) (measurable_W hmeas _ L)
  have hF : ∀ F : Finset (Fin 10), ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, Coding.Laminar F →
      (1 : Fin 10) ∉ F →
      ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ {1}, ∑ u ∈ range L, Y c u ω := by
    intro F
    by_cases hc : Coding.Laminar F ∧ (1 : Fin 10) ∉ F
    · filter_upwards [ae_eventually_lt Y hmeas hb hindep hident _ hmean F {1}
        (hε.1 F hc.1 hc.2)] with ω hω
      filter_upwards [hω] with L hL _ _
      exact hL
    · exact ae_of_all _ fun ω => Eventually.of_forall fun L h1 h2 => absurd ⟨h1, h2⟩ hc
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ω ∈ G L := by
    filter_upwards [ae_all_iff.mpr hF] with ω hω
    exact eventually_all.mpr hω
  have hsub : ∀ L ω, ω ∈ G L → ∀ F, Coding.Laminar F →
      (∀ F', Coding.Laminar F' →
        ∑ c ∈ F', ∑ u ∈ range L, Y c u ω ≤ ∑ c ∈ F, ∑ u ∈ range L, Y c u ω) →
      (1 : Fin 10) ∈ F := by
    intro L ω hω F hlam hmax
    by_contra h1
    have hlt := hω F hlam h1
    have hle := hmax {1} (by intro i hi j hj; rw [mem_singleton.mp hi, mem_singleton.mp hj]; decide)
    linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with ω hω
    filter_upwards [hω] with L hL
    exact hsub L ω hL
  · have hP := Cutting.prob_tendsto_of_ae_eventually (μ := μ) (G := G) hGm hae
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP (fun _ => zero_le)
      fun L => measure_mono fun ω hω => ?_
    obtain ⟨F, hlam, hmax, h1⟩ := hω
    exact fun hG => h1 (hsub L ω hG F hlam hmax)

end Stemma.CodingLimit
