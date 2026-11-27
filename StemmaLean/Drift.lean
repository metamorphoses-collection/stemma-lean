/-
Proposition 8.14 of the technical report (`prop:drift`), drift towards the root, as the number of
units grows.

On the rooted tree `(((1,3),2),4)`, root at the vertex joining `{1,2,3}` and `4`, the edge above
`{1,3}` has rate `ρ ε²`, the edge above `{1,2,3}` rate `σ ε`, the pendant edges of `3` and `4`
rates `b ε` and `τ ε`, and those of `1` and `2` rate `0` (`DriftGen.lean`: the exact supports, as
polynomials, and their leading orders).  The true split is `13|24`, the true clusters `{1,3}` and
`{1,2,3}`.  For every sufficiently small fixed `ε > 0`:

* unrooted coding: if `((1 - α²)σ + τ) b < ρ`, the estimator is consistent, with failure
  probability at most `6 e^{-L γ²/2}` for some `γ > 0` (`drift_unrooted_consistency`); if
  `((1 - α²)σ + τ) b > ρ`, almost surely the false split `12|34` is eventually the unique
  maximum, and the probability that it is tends to one (`drift_unrooted_false`);
* rooted coding: if `(1 - α²) σ b < ρ`, consistent, with failure probability at most
  `20 e^{-L γ²/2}` (`drift_rooted_consistency`); if `(1 - α²) σ b > ρ`, almost surely the family
  `{{1,2}, {1,2,3}}`, which contains the false cluster `{1,2}`, is eventually strictly heavier
  than every other laminar family, so it is selected, and the probability that it is tends to one
  (`drift_rooted_false`).

The leading-order comparisons at the level of expected supports are
`supports_unrooted_consistent`, `supports_unrooted_drift`, `supports_rooted_consistent` and
`supports_rooted_drift`: each is a comparison of polynomials in `ε`, after division by `ε` or
`ε²`, at `ε = 0`, extended to small `ε` by continuity.

Witnesses `1, 2, 3, 4` are the indices `0, 1, 2, 3`.  The three non-trivial splits are the sides
`s12 = {0,1}` (`12|34`), `s13 = {0,2}` (`13|24`) and `s14 = {1,2}` (`14|23`), away from witness
`4`; the ten proper clusters are `Coding.cl` (`1 = {1,3}`, `0 = {1,2}`, `6 = {1,2,3}`).  As in
`CodingLimit.lean`, the law of the units is the hypothesis on their means.
-/
import StemmaLean.DriftGen
import StemmaLean.CodingLimit

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped Classical

namespace Stemma.Drift

open Stemma.Splits Stemma.CodingLimit

/-! ### Two consistency lemmas for any expected supports on four witnesses -/

/-- Consistency of `{t}` for any unrooted expected supports on four witnesses, `t` the strict
maximum among the three splits `t, o₁, o₂`, and positive. -/
theorem quartet_consistency_of (t o₁ o₂ : Finset (Fin 4))
    (hsides : ∀ s, IsSide 3 s → s = t ∨ s = o₁ ∨ s = o₂) (hbin : IsBinary 3 {t})
    (hcard : ({t, o₁, o₂} : Finset (Finset (Fin 4))).card = 3)
    (m : Finset (Fin 4) → ℝ) (h1 : m o₁ < m t) (h2 : m o₂ < m t)
    (h0 : 0 < m t) (hz : ∀ s, s ≠ t → s ≠ o₁ → s ≠ o₂ → m s = 0) :
    ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ s u, Measurable (Y s u)) → (∀ s u ω, Y s u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ s, iIndepFun (Y s) μ) → (∀ s u, μ[Y s u] = m s) →
      (∀ s, s ≠ t → s ≠ o₁ → s ≠ o₂ → ∀ u ω, Y s u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {t} ∧
        ∑ s ∈ {t}, (∑ u, Y s u ω) / L ≤ ∑ s ∈ S, (∑ u, Y s u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  set γ := min (min (m t - m o₁) (m t - m o₂)) (m t)
  have hγ : 0 < γ := by
    simp only [γ, lt_min_iff]; exact ⟨⟨by linarith, by linarith⟩, h0⟩
  refine ⟨γ, hγ, fun Ω _ μ _ L hL Y hmeas hb hind hmean hR => ?_⟩
  have hgap : ∀ S, IsSystem 3 S → S ≠ {t} →
      γ * ({t} \ S).card ≤ ∑ s ∈ {t} \ S, m s - ∑ s ∈ S \ {t}, m s := by
    intro S hS hne
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sdiff_empty, empty_sdiff, card_singleton, sum_singleton, sum_empty]
      have := min_le_right (min (m t - m o₁) (m t - m o₂)) (m t)
      push_cast; linarith
    · have hσt : σ ≠ t := fun e => hne (by rw [e])
      have e1 : ({t} : Finset (Finset (Fin 4))) \ {σ} = {t} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr fun e => hσt e.symm)
      have e2 : ({σ} : Finset (Finset (Fin 4))) \ {t} = {σ} :=
        sdiff_eq_self_of_disjoint (disjoint_singleton.mpr hσt)
      rw [e1, e2, card_singleton, sum_singleton, sum_singleton]
      push_cast
      rcases hsides σ hσ with rfl | rfl | rfl
      · exact absurd rfl hσt
      · have := min_le_left (min (m t - m σ) (m t - m o₂)) (m t)
        have := min_le_left (m t - m σ) (m t - m o₂)
        linarith
      · have := min_le_left (min (m t - m o₁) (m t - m σ)) (m t)
        have := min_le_right (m t - m o₁) (m t - m σ)
        linarith
  have := Consistency.consistency (μ := μ) 3 {t} hbin m γ hγ hgap hL Y hmeas hb hind
    hmean {t, o₁, o₂}
    (fun s hs u ω => by
      simp only [mem_insert, mem_singleton, not_or] at hs
      exact hR s hs.1 hs.2.1 hs.2.2 u ω)
    (fun s hs => by
      simp only [mem_insert, mem_singleton, not_or] at hs
      exact hz s hs.1 hs.2.1 hs.2.2)
  rw [hcard] at this
  exact_mod_cast this

/-- Selection of `{f}` for any unrooted expected supports on four witnesses, `f` the strict
maximum among the three splits `f, o₁, o₂`: almost surely `{f}` is eventually strictly heavier
than every other compatible set, and the probability that it is not tends to zero. -/
theorem quartet_selected_of (f o₁ o₂ : Finset (Fin 4))
    (hsides : ∀ s, IsSide 3 s → s = f ∨ s = o₁ ∨ s = o₂)
    (m : Finset (Fin 4) → ℝ) (h1 : m o₁ < m f) (h2 : m o₂ < m f) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ s u, Measurable (Y s u)) → (∀ s u ω, Y s u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω s => Y s i ω) (fun ω s => Y s j ω) μ) →
      (∀ u, IdentDistrib (fun ω s => Y s u ω) (fun ω s => Y s 0 ω) μ μ) →
      (∀ s, μ[Y s 0] = m s) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {f} →
        ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {f}, ∑ u ∈ range L, Y s u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {f} →
        ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {f}, ∑ u ∈ range L, Y s u ω}ᶜ) atTop
        (𝓝 0) := by
  intro Ω _ μ _ Y hmeas hb01 hindep hident hmean
  have e1 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {o₁} {f}
    (by simp only [sum_singleton]; exact h1)
  have e2 := ae_eventually_lt Y hmeas hb01 hindep hident _ hmean {o₂} {f}
    (by simp only [sum_singleton]; exact h2)
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {f} →
      ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {f}, ∑ u ∈ range L, Y s u ω := by
    filter_upwards [e1, e2] with ω h1 h2
    filter_upwards [h1, h2] with L hL1 hL2 S hS hne
    have hpos : 0 ≤ ∑ s ∈ {o₁}, ∑ u ∈ range L, Y s u ω :=
      sum_nonneg fun s _ => sum_nonneg fun u _ => (hb01 s u ω).1
    rcases system_four hS with rfl | ⟨σ, hσ, rfl⟩
    · simp only [sum_empty]; linarith
    · rcases hsides σ hσ with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact hL1
      · exact hL2
  refine ⟨hae, ?_⟩
  have hG : ∀ L, MeasurableSet {ω | ∀ S, IsSystem 3 S → S ≠ {f} →
      ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {f}, ∑ u ∈ range L, Y s u ω} := by
    intro L
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun S => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_W hmeas S L) (measurable_W hmeas _ L)
  exact Cutting.prob_tendsto_of_ae_eventually hG hae

lemma binary_s13 : IsBinary 3 {s13} := by
  refine ⟨⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩, by simp⟩
  · rw [mem_singleton.mp hA]; unfold IsSide Nontriv s13; decide
  · exact absurd ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm) hab

lemma card_three : ({s13, s12, s14} : Finset (Finset (Fin 4))).card = 3 := by
  rw [card_insert_of_notMem (by simp [s12, s13, s14]; decide),
    card_insert_of_notMem (by simp [s12, s14]; decide), card_singleton]

/-! ### (a) The unrooted coding -/

/-- The expected unrooted supports on the drift tree after the substitution. -/
noncomputable def mUD (ρ σ b τ α ε : ℝ) (s : Finset (Fin 4)) : ℝ :=
  if s = s12 then suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.U12
  else if s = s13 then suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Quartet.U13
  else if s = s14 then suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.U14 else 0

lemma mUD12 (ρ σ b τ α ε : ℝ) : mUD ρ σ b τ α ε s12 = ε ^ 2 * gDU12 ρ σ b τ α ε := by
  simp [mUD, scaleD_U12]
lemma mUD13 (ρ σ b τ α ε : ℝ) : mUD ρ σ b τ α ε s13 = ε ^ 2 * gDU13 ρ σ b τ α ε := by
  have h1 : s13 ≠ s12 := by decide
  simp [mUD, h1, scaleD_U13]
lemma mUD14 (ρ σ b τ α ε : ℝ) : mUD ρ σ b τ α ε s14 = ε ^ 2 * gDU14 ρ σ b τ α ε := by
  have h1 : s14 ≠ s12 := by decide
  have h2 : s14 ≠ s13 := by decide
  simp [mUD, h1, h2, scaleD_U14]
lemma mUD_off (ρ σ b τ α ε : ℝ) (s : Finset (Fin 4)) (h1 : s ≠ s13) (h2 : s ≠ s12)
    (h3 : s ≠ s14) : mUD ρ σ b τ α ε s = 0 := by
  simp [mUD, h1, h2, h3]

lemma sides13 (s : Finset (Fin 4)) (h : IsSide 3 s) : s = s13 ∨ s = s12 ∨ s = s14 := by
  rcases sides_four s h with h | h | h <;> simp [h]

lemma sides12 (s : Finset (Fin 4)) (h : IsSide 3 s) : s = s12 ∨ s = s13 ∨ s = s14 :=
  sides_four s h

/-- **Proposition 8.14, unrooted coding, at the level of expected supports.**  If
`((1 - α²)σ + τ) b < ρ` (`ρ > 0`), then for all sufficiently small `ε > 0` the true split `13|24`
has strictly larger expected support than `12|34` and `14|23`, and positive support. -/
theorem supports_unrooted_consistent (ρ σ b τ α : ℝ) (hρ : 0 < ρ)
    (h : ((1 - α ^ 2) * σ + τ) * b < ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), mUD ρ σ b τ α ε s12 < mUD ρ σ b τ α ε s13 ∧
      mUD ρ σ b τ α ε s14 < mUD ρ σ b τ α ε s13 ∧ 0 < mUD ρ σ b τ α ε s13 := by
  have e1 := Coding.eventually_pos (G := fun ε => gDU13 ρ σ b τ α ε - gDU12 ρ σ b τ α ε)
    ((contD_U13 ρ σ b τ α).sub (contD_U12 ρ σ b τ α)) (by simp [zeroD_U12, zeroD_U13]; linarith)
  have e2 := Coding.eventually_pos (G := fun ε => gDU13 ρ σ b τ α ε - gDU14 ρ σ b τ α ε)
    ((contD_U13 ρ σ b τ α).sub (contD_U14 ρ σ b τ α)) (by simp [zeroD_U13, zeroD_U14]; linarith)
  have e3 := Coding.eventually_pos (G := fun ε => gDU13 ρ σ b τ α ε)
    (contD_U13 ρ σ b τ α) (by simp [zeroD_U13]; linarith)
  filter_upwards [e1, e2, e3] with ε h1 h2 h3
  simp only [mUD12, mUD13, mUD14] at *
  refine ⟨by nlinarith, by nlinarith, h3⟩

/-- **Proposition 8.14, unrooted coding, the drift at the level of expected supports.**  If
`ρ < ((1 - α²)σ + τ) b` (`ρ ≥ 0`), then for all sufficiently small `ε > 0` the false split `12|34`
has strictly the largest expected support. -/
theorem supports_unrooted_drift (ρ σ b τ α : ℝ) (hρ : 0 ≤ ρ)
    (h : ρ < ((1 - α ^ 2) * σ + τ) * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), mUD ρ σ b τ α ε s13 < mUD ρ σ b τ α ε s12 ∧
      mUD ρ σ b τ α ε s14 < mUD ρ σ b τ α ε s12 := by
  have e1 := Coding.eventually_pos (G := fun ε => gDU12 ρ σ b τ α ε - gDU13 ρ σ b τ α ε)
    ((contD_U12 ρ σ b τ α).sub (contD_U13 ρ σ b τ α)) (by simp [zeroD_U12, zeroD_U13]; linarith)
  have e2 := Coding.eventually_pos (G := fun ε => gDU12 ρ σ b τ α ε - gDU14 ρ σ b τ α ε)
    ((contD_U12 ρ σ b τ α).sub (contD_U14 ρ σ b τ α)) (by simp [zeroD_U12, zeroD_U14]; linarith)
  filter_upwards [e1, e2] with ε h1 h2
  simp only [mUD12, mUD13, mUD14] at *
  constructor <;> nlinarith

/-- **Proposition 8.14 (`prop:drift`), unrooted coding, consistent side.**  If
`((1 - α²)σ + τ) b < ρ` (`ρ > 0`), then for every sufficiently small `ε > 0` there is `γ > 0`
such that, for units with the expected unrooted supports of the drift tree, the estimator misses
the true split `13|24` with probability at most `6 e^{-L γ²/2}`. -/
theorem drift_unrooted_consistency (ρ σ b τ α : ℝ) (hρ : 0 < ρ)
    (h : ((1 - α ^ 2) * σ + τ) * b < ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Finset (Fin 4) → Fin L → Ω → ℝ,
      (∀ s u, Measurable (Y s u)) → (∀ s u ω, Y s u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ s, iIndepFun (Y s) μ) → (∀ s u, μ[Y s u] = mUD ρ σ b τ α ε s) →
      (∀ s, s ≠ s13 → s ≠ s12 → s ≠ s14 → ∀ u ω, Y s u ω = 0) →
      μ.real {ω | ∃ S, IsSystem 3 S ∧ S ≠ {s13} ∧
        ∑ s ∈ {s13}, (∑ u, Y s u ω) / L ≤ ∑ s ∈ S, (∑ u, Y s u ω) / L} ≤
        2 * 3 * exp (-L * γ ^ 2 / 2) := by
  filter_upwards [supports_unrooted_consistent ρ σ b τ α hρ h] with ε ⟨h1, h2, h0⟩
  exact quartet_consistency_of s13 s12 s14 sides13 binary_s13 card_three _ h1 h2 h0
    (mUD_off ρ σ b τ α ε)

/-- **Proposition 8.14 (`prop:drift`), unrooted coding, the drift.**  If
`ρ < ((1 - α²)σ + τ) b` (`ρ ≥ 0`), then for every sufficiently small `ε > 0`, for i.i.d. units
with the expected unrooted supports of the drift tree, almost surely the false split `12|34` is
eventually strictly heavier than every other compatible set (so it is selected), and the
probability that it is tends to one. -/
theorem drift_unrooted_false (ρ σ b τ α : ℝ) (hρ : 0 ≤ ρ) (h : ρ < ((1 - α ^ 2) * σ + τ) * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Finset (Fin 4) → ℕ → Ω → ℝ),
      (∀ s u, Measurable (Y s u)) → (∀ s u ω, Y s u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω s => Y s i ω) (fun ω s => Y s j ω) μ) →
      (∀ u, IdentDistrib (fun ω s => Y s u ω) (fun ω s => Y s 0 ω) μ μ) →
      (∀ s, μ[Y s 0] = mUD ρ σ b τ α ε s) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ S, IsSystem 3 S → S ≠ {s12} →
        ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {s12}, ∑ u ∈ range L, Y s u ω) ∧
      Tendsto (fun L => μ {ω | ∀ S, IsSystem 3 S → S ≠ {s12} →
        ∑ s ∈ S, ∑ u ∈ range L, Y s u ω < ∑ s ∈ {s12}, ∑ u ∈ range L, Y s u ω}ᶜ) atTop
        (𝓝 0) := by
  filter_upwards [supports_unrooted_drift ρ σ b τ α hρ h] with ε ⟨h1, h2⟩
  exact quartet_selected_of s12 s13 s14 sides12 _ h1 h2

/-! ### (b) The rooted coding -/

/-- The expected rooted supports of the ten proper clusters (`Coding.cl`) on the drift tree. -/
noncomputable def mRD (ρ σ b τ α ε : ℝ) : Fin 10 → ℝ
  | 0 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C12
  | 1 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C13
  | 2 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C14
  | 3 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C23
  | 4 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C24
  | 5 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C34
  | 6 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C123
  | 7 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C124
  | 8 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C134
  | 9 => suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α Coding.C234

/-- The supports divided by `ε²`, for the clusters other than `{1,2,3}`. -/
def g2 (ρ σ b τ α ε : ℝ) : Fin 10 → ℝ
  | 0 => gDC12 ρ σ b τ α ε | 1 => gDC13 ρ σ b τ α ε | 2 => gDC14 ρ σ b τ α ε
  | 3 => gDC23 ρ σ b τ α ε | 4 => gDC24 ρ σ b τ α ε | 5 => gDC34 ρ σ b τ α ε | 6 => 0
  | 7 => gDC124 ρ σ b τ α ε | 8 => gDC134 ρ σ b τ α ε | 9 => gDC234 ρ σ b τ α ε

/-- The supports divided by `ε`. -/
def g1 (ρ σ b τ α ε : ℝ) (c : Fin 10) : ℝ :=
  if c = 6 then gDC123 ρ σ b τ α ε else ε * g2 ρ σ b τ α ε c

lemma mRD_eq2 (ρ σ b τ α ε : ℝ) (c : Fin 10) (hc : c ≠ 6) :
    mRD ρ σ b τ α ε c = ε ^ 2 * g2 ρ σ b τ α ε c := by
  fin_cases c <;> simp_all [mRD, g2, scaleD_C12, scaleD_C13, scaleD_C14, scaleD_C23, scaleD_C24,
    scaleD_C34, scaleD_C124, scaleD_C134, scaleD_C234]

lemma mRD_eq1 (ρ σ b τ α ε : ℝ) (c : Fin 10) :
    mRD ρ σ b τ α ε c = ε * g1 ρ σ b τ α ε c := by
  by_cases hc : c = 6
  · subst hc; simp [mRD, g1, scaleD_C123]
  · rw [mRD_eq2 _ _ _ _ _ _ c hc, g1, if_neg hc]; ring

lemma g2_cont (ρ σ b τ α : ℝ) (c : Fin 10) : Continuous (fun ε => g2 ρ σ b τ α ε c) := by
  fin_cases c
  · exact contD_C12 ..
  · exact contD_C13 ..
  · exact contD_C14 ..
  · exact contD_C23 ..
  · exact contD_C24 ..
  · exact contD_C34 ..
  · exact continuous_const
  · exact contD_C124 ..
  · exact contD_C134 ..
  · exact contD_C234 ..

lemma g1_cont (ρ σ b τ α : ℝ) (c : Fin 10) : Continuous (fun ε => g1 ρ σ b τ α ε c) := by
  by_cases hc : c = 6
  · simp only [g1, hc, if_true]; exact contD_C123 ..
  · simp only [g1, hc, if_false]; exact continuous_id.mul (g2_cont ρ σ b τ α c)

lemma g1_zero (ρ σ b τ α : ℝ) (c : Fin 10) : g1 ρ σ b τ α 0 c = if c = 6 then σ else 0 := by
  by_cases hc : c = 6
  · simp [g1, hc, zeroD_C123]
  · simp [g1, hc]

lemma g2_zero0 (ρ σ b τ α : ℝ) : g2 ρ σ b τ α 0 0 = (1 - α ^ 2) * σ * b := by
  simp only [g2, zeroD_C12]; ring
lemma g2_zero1 (ρ σ b τ α : ℝ) : g2 ρ σ b τ α 0 1 = ρ := by simp only [g2, zeroD_C13]
lemma g2_zero3 (ρ σ b τ α : ℝ) : g2 ρ σ b τ α 0 3 = 0 := by simp only [g2, zeroD_C23]

/-- Weight of a family of clusters. -/
noncomputable def WD (ρ σ b τ α ε : ℝ) (F : Finset (Fin 10)) : ℝ := ∑ c ∈ F, mRD ρ σ b τ α ε c

/-- The true family: the clusters `{1,3}` and `{1,2,3}`. -/
def Td : Finset (Fin 10) := {1, 6}

/-- The drifted family: the false cluster `{1,2}` and the true cluster `{1,2,3}`. -/
def Fd : Finset (Fin 10) := {0, 6}

/-- The clusters compatible with `{1,2,3}`: `{1,2}`, `{1,3}`, `{2,3}`. -/
lemma lam_six : ∀ c : Fin 10, Coding.lam c 6 → c ≠ 6 → c = 0 ∨ c = 1 ∨ c = 3 := by decide

/-- If `G` is continuous with `G 0 > 0`, then `ε G(ε) > 0` for all sufficiently small `ε > 0`. -/
lemma eventually_pos1 {G : ℝ → ℝ} (hG : Continuous G) (h0 : 0 < G 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε * G ε := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < G ε := (hG.tendsto 0).eventually (lt_mem_nhds h0)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds h1, h2] with ε hG' hε
  positivity

/-- The comparison for a family `{a, {1,2,3}}`: if `σ > 0` and the `ε²` coefficient of `a` is
positive and strictly larger than that of every other cluster compatible with `{1,2,3}`, then for
all sufficiently small `ε > 0` the family is strictly heavier than every other laminar family. -/
theorem weights_lt (ρ σ b τ α : ℝ) (hσ : 0 < σ) (a : Fin 10) (ha6 : a ≠ 6)
    (hpos : 0 < g2 ρ σ b τ α 0 a)
    (hlt : ∀ c, Coding.lam c 6 → c ≠ 6 → c ≠ a → g2 ρ σ b τ α 0 c < g2 ρ σ b τ α 0 a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : Finset (Fin 10), Coding.Laminar F → F ≠ {a, 6} →
      WD ρ σ b τ α ε F < WD ρ σ b τ α ε {a, 6} := by
  rw [eventually_all]
  intro F
  by_cases hF : Coding.Laminar F ∧ F ≠ {a, 6}
  · obtain ⟨hlam, hne⟩ := hF
    have hWA : ∀ ε, WD ρ σ b τ α ε {a, 6} = mRD ρ σ b τ α ε a + mRD ρ σ b τ α ε 6 := fun ε => by
      simp only [WD]; rw [sum_pair ha6]
    by_cases h6 : (6 : Fin 10) ∈ F
    · -- the order-`ε` terms cancel: compare at order `ε²`
      let G : ℝ → ℝ := fun ε => g2 ρ σ b τ α ε a - ∑ c ∈ F.erase 6, g2 ρ σ b τ α ε c
      have hG : Continuous G :=
        (g2_cont ρ σ b τ α a).sub (continuous_finsetSum _ fun c _ => g2_cont ρ σ b τ α c)
      have hcard : (F.erase 6).card ≤ 1 := by
        have := CodingLimit.laminar_card hlam
        rw [card_erase_of_mem h6]; omega
      have h0 : 0 < G 0 := by
        rcases card_le_one_iff_subset_singleton.mp hcard with ⟨c, hc⟩
        rcases subset_singleton_iff.mp hc with he | he
        · simp only [G, he, sum_empty]; linarith
        · simp only [G, he, sum_singleton]
          have hcF : c ∈ F := mem_of_mem_erase (he ▸ mem_singleton_self c)
          have hc6 : c ≠ 6 := ne_of_mem_erase (he ▸ mem_singleton_self c)
          have hca : c ≠ a := by
            rintro rfl
            apply hne
            rw [← insert_erase h6, he, pair_comm]
          linarith [hlt c (hlam c hcF 6 h6) hc6 hca]
      filter_upwards [Coding.eventually_pos hG h0] with ε hε _ _
      have hWF : WD ρ σ b τ α ε F = mRD ρ σ b τ α ε 6 + ∑ c ∈ F.erase 6, mRD ρ σ b τ α ε c := by
        simp only [WD]; rw [add_sum_erase _ _ h6]
      have hsum : ∑ c ∈ F.erase 6, mRD ρ σ b τ α ε c =
          ε ^ 2 * ∑ c ∈ F.erase 6, g2 ρ σ b τ α ε c := by
        rw [mul_sum]
        exact sum_congr rfl fun c hc => mRD_eq2 _ _ _ _ _ _ c (ne_of_mem_erase hc)
      rw [hWA, hWF, hsum, mRD_eq2 _ _ _ _ _ _ a ha6]
      simp only [G, mul_sub] at hε
      linarith
    · -- the order-`ε` term `σ ε` of `{1,2,3}` decides
      let G : ℝ → ℝ := fun ε => ∑ c ∈ ({a, 6} : Finset (Fin 10)), g1 ρ σ b τ α ε c -
        ∑ c ∈ F, g1 ρ σ b τ α ε c
      have hG : Continuous G :=
        (continuous_finsetSum _ fun c _ => g1_cont ρ σ b τ α c).sub
          (continuous_finsetSum _ fun c _ => g1_cont ρ σ b τ α c)
      have h0 : 0 < G 0 := by
        simp only [G, g1_zero, sum_ite_eq', if_neg h6, mem_insert, mem_singleton, or_true,
          if_true]
        linarith
      filter_upwards [eventually_pos1 hG h0] with ε hε _ _
      have : WD ρ σ b τ α ε {a, 6} - WD ρ σ b τ α ε F = ε * G ε := by
        simp only [WD, G, mRD_eq1, ← mul_sum]; ring
      linarith
  · exact Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hF

/-- **Proposition 8.14, rooted coding, at the level of expected supports.**  If
`(1 - α²) σ b < ρ` (`ρ, σ > 0`), then for all sufficiently small `ε > 0` the true family
`{{1,3}, {1,2,3}}` is strictly heavier than every other laminar family of clusters. -/
theorem supports_rooted_consistent (ρ σ b τ α : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : (1 - α ^ 2) * σ * b < ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : Finset (Fin 10), Coding.Laminar F → F ≠ Td →
      WD ρ σ b τ α ε F < WD ρ σ b τ α ε Td :=
  weights_lt ρ σ b τ α hσ 1 (by decide) (by rw [g2_zero1]; exact hρ) fun c hc h6 h1 => by
    rcases lam_six c hc h6 with rfl | rfl | rfl
    · rw [g2_zero0, g2_zero1]; exact h
    · exact absurd rfl h1
    · rw [g2_zero3, g2_zero1]; exact hρ

/-- **Proposition 8.14, rooted coding, the drift at the level of expected supports.**  If
`ρ < (1 - α²) σ b` (`ρ ≥ 0`, `σ > 0`), then for all sufficiently small `ε > 0` the family
`{{1,2}, {1,2,3}}` is strictly heavier than every other laminar family of clusters. -/
theorem supports_rooted_drift (ρ σ b τ α : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (h : ρ < (1 - α ^ 2) * σ * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : Finset (Fin 10), Coding.Laminar F → F ≠ Fd →
      WD ρ σ b τ α ε F < WD ρ σ b τ α ε Fd :=
  weights_lt ρ σ b τ α hσ 0 (by decide) (by rw [g2_zero0]; linarith) fun c hc h6 h0 => by
    rcases lam_six c hc h6 with rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [g2_zero0, g2_zero1]; exact h
    · rw [g2_zero3, g2_zero0]; linarith

lemma match_pair {A : Finset (Fin 10)} (hA : A.card = 2) {F : Finset (Fin 10)}
    (hF : Coding.Laminar F) (hne : F ≠ A) :
    (A \ F).Nonempty ∧ (F \ A).card ≤ (A \ F).card := by
  have hFc := CodingLimit.laminar_card hF
  have hAF : ¬ A ⊆ F := fun h => hne (eq_of_subset_of_card_le h (by rw [hA]; exact hFc)).symm
  refine ⟨by rwa [sdiff_nonempty], ?_⟩
  have h1 := card_sdiff_add_card_inter F A
  have h2 := card_sdiff_add_card_inter A F
  rw [inter_comm] at h1
  rw [hA] at h2
  omega

lemma Td_card : Td.card = 2 := by decide

/-- The rooted competitors of `Td`. -/
noncomputable def rcompD : Finset (Finset (Fin 10)) :=
  univ.filter fun F => Coding.Laminar F ∧ F ≠ Td

lemma rcompD_nonempty : rcompD.Nonempty :=
  ⟨∅, mem_filter.mpr ⟨mem_univ _, fun i hi => absurd hi (notMem_empty i), by decide⟩⟩

/-- **Proposition 8.14 (`prop:drift`), rooted coding, consistent side.**  If `(1 - α²) σ b < ρ`
(`ρ, σ > 0`), then for every sufficiently small `ε > 0` there is `γ > 0` such that, for units
proposing the ten proper clusters with the expected rooted supports of the drift tree, the
estimator over laminar families misses the true clusters `{1,3}`, `{1,2,3}` with probability at
most `20 e^{-L γ²/2}`. -/
theorem drift_rooted_consistency (ρ σ b τ α : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : (1 - α ^ 2) * σ * b < ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ γ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (L : ℕ), 0 < L → ∀ Y : Fin 10 → Fin L → Ω → ℝ,
      (∀ c u, Measurable (Y c u)) → (∀ c u ω, Y c u ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ c, iIndepFun (Y c) μ) → (∀ c u, μ[Y c u] = mRD ρ σ b τ α ε c) →
      μ.real {ω | ∃ F, Coding.Laminar F ∧ F ≠ Td ∧
        ∑ c ∈ Td, (∑ u, Y c u ω) / L ≤ ∑ c ∈ F, (∑ u, Y c u ω) / L} ≤
        2 * 10 * exp (-L * γ ^ 2 / 2) := by
  filter_upwards [supports_rooted_consistent ρ σ b τ α hρ hσ h] with ε hε
  set mm := mRD ρ σ b τ α ε
  set γ := rcompD.inf' rcompD_nonempty
    fun F => (∑ c ∈ Td \ F, mm c - ∑ c ∈ F \ Td, mm c) / (Td \ F).card
  have hdiff : ∀ F, Coding.Laminar F → F ≠ Td →
      0 < ∑ c ∈ Td \ F, mm c - ∑ c ∈ F \ Td, mm c := by
    intro F hF hne
    have := hε F hF hne
    simp only [WD] at this
    have e := sum_sdiff_sub_sum_sdiff (s₁ := F) (s₂ := Td) (f := mm)
    linarith
  have hγ : 0 < γ := by
    rw [lt_inf'_iff]
    intro F hF
    simp only [rcompD, mem_filter, mem_univ, true_and] at hF
    exact div_pos (hdiff F hF.1 hF.2)
      (by exact_mod_cast card_pos.mpr (match_pair Td_card hF.1 hF.2).1)
  refine ⟨γ, hγ, fun Ω _ μ _ L hL Y hmeas hb hind hmean => ?_⟩
  have hgap : ∀ F, Coding.Laminar F → F ≠ Td →
      γ * (Td \ F).card ≤ ∑ c ∈ Td \ F, mm c - ∑ c ∈ F \ Td, mm c := by
    intro F hF hne
    have hpos : (0 : ℝ) < (Td \ F).card := by
      exact_mod_cast card_pos.mpr (match_pair Td_card hF hne).1
    have := inf'_le (fun F => (∑ c ∈ Td \ F, mm c - ∑ c ∈ F \ Td, mm c) / (Td \ F).card)
      (by simp [rcompD, hF, hne] : F ∈ rcompD)
    rwa [le_div_iff₀ hpos] at this
  have := Consistency.consistency_of_matching (μ := μ) Coding.Laminar Td mm γ hγ
    (fun F hF hne => match_pair Td_card hF hne) hgap hL Y hmeas hb hind hmean univ
    (fun c hc => absurd (mem_univ c) hc) (fun c hc => absurd (mem_univ c) hc)
  rw [card_univ, Fintype.card_fin] at this
  push_cast at this
  exact this

/-- **Proposition 8.14 (`prop:drift`), rooted coding, the drift.**  If `(1 - α²) σ b > ρ`
(`ρ ≥ 0`, `σ > 0`), then for every sufficiently small `ε > 0`, for i.i.d. units with the
expected rooted supports of the drift tree, almost surely the family `{{1,2}, {1,2,3}}` is
eventually strictly heavier than every other laminar family, so the estimator selects the false
cluster `{1,2}`, and the probability that it does tends to one. -/
theorem drift_rooted_false (ρ σ b τ α : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (h : ρ < (1 - α ^ 2) * σ * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Fin 10 → ℕ → Ω → ℝ),
      (∀ c u, Measurable (Y c u)) → (∀ c u ω, Y c u ω ∈ Set.Icc (0 : ℝ) 1) →
      (Pairwise fun i j => IndepFun (fun ω c => Y c i ω) (fun ω c => Y c j ω) μ) →
      (∀ u, IdentDistrib (fun ω c => Y c u ω) (fun ω c => Y c 0 ω) μ μ) →
      (∀ c, μ[Y c 0] = mRD ρ σ b τ α ε c) →
      (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ F, Coding.Laminar F → F ≠ Fd →
        ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ Fd, ∑ u ∈ range L, Y c u ω) ∧
      Tendsto (fun L => μ {ω | ∀ F, Coding.Laminar F → F ≠ Fd →
        ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ Fd, ∑ u ∈ range L, Y c u ω}ᶜ) atTop
        (𝓝 0) := by
  filter_upwards [supports_rooted_drift ρ σ b τ α hρ hσ h] with ε hε
  intro Ω _ μ _ Y hmeas hb hindep hident hmean
  have hF : ∀ F : Finset (Fin 10), ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, Coding.Laminar F → F ≠ Fd →
      ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ Fd, ∑ u ∈ range L, Y c u ω := by
    intro F
    by_cases hc : Coding.Laminar F ∧ F ≠ Fd
    · filter_upwards [ae_eventually_lt Y hmeas hb hindep hident _ hmean F Fd
        (hε F hc.1 hc.2)] with ω hω
      filter_upwards [hω] with L hL _ _ using hL
    · exact ae_of_all _ fun ω => Eventually.of_forall fun L h1 h2 => absurd ⟨h1, h2⟩ hc
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ F, Coding.Laminar F → F ≠ Fd →
      ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ Fd, ∑ u ∈ range L, Y c u ω := by
    filter_upwards [ae_all_iff.mpr hF] with ω hω
    exact eventually_all.mpr hω
  refine ⟨hae, ?_⟩
  have hG : ∀ L, MeasurableSet {ω | ∀ F, Coding.Laminar F → F ≠ Fd →
      ∑ c ∈ F, ∑ u ∈ range L, Y c u ω < ∑ c ∈ Fd, ∑ u ∈ range L, Y c u ω} := by
    intro L
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun F => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_W hmeas F L) (measurable_W hmeas _ L)
  exact Cutting.prob_tendsto_of_ae_eventually hG hae

end Stemma.Drift
