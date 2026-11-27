/-
Certifying the margin with dependent units (Proposition 7.11 of the technical report,
`prop:gammablocks`).

The units form `J` independent blocks of `k` units, with arbitrary dependence inside a block, as in
`Blocks.lean` (`prop:blocks`).  For each non-trivial split `s` the observed support per unit
`w(s)/L` (`L = J k`) is the mean of the `J` block averages `w_j(s)/k ∈ [0,1]`, each of mean `m s`.
With `h = √(log(2N/δ)/(2J))`, `N` the number of non-trivial splits, the bounds are
`ℓ s = w(s)/L - h` and `u s = w(s)/L + h`.  Hoeffding's inequality (`Consistency.upper_tail`, on
the block averages and on their reflections `1 - w_j(s)/k`) makes each one-sided bound fail with
probability at most `e^{-2Jh²} = δ/(2N)`, and the event argument of Theorem 7.9
(`GammaConf.gamma_confidence`) concludes.

Formalised in two forms: `gamma_confidence_avg`, for any `J` independent `[0,1]`-valued variables
per split with common mean `m s` (the block averages), and `gamma_confidence_blocks`, for the units
of `J` blocks of `k`, stated as `Blocks.dependent_blocks` is.  As there, Lean needs independence
across blocks and equal block means, not identical distribution.
-/
import Mathlib
import StemmaLean.GammaConf
import StemmaLean.Consistency

open MeasureTheory ProbabilityTheory Finset Real
open scoped Classical

namespace Stemma.GammaBlocks

open Stemma.Splits Stemma.Margin Stemma.GammaConf

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Hoeffding radius `h = √(log(2N/δ)/(2J))`. -/
noncomputable def radius (N J : ℕ) (δ : ℝ) : ℝ := √(log (2 * N / δ) / (2 * J))

lemma radius_nonneg (N J : ℕ) (δ : ℝ) : 0 ≤ radius N J δ := sqrt_nonneg _

/-- `e^{-2 J h²} = δ / (2N)` for `0 < δ ≤ 1` and `N ≥ 1`. -/
lemma exp_radius {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    exp (-2 * J * radius N J δ ^ 2) = δ / (2 * N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hq : 1 ≤ 2 * (N : ℝ) / δ := by
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog : 0 ≤ log (2 * N / δ) := log_nonneg hq
  unfold radius
  rw [sq_sqrt (div_nonneg hlog (by positivity))]
  have e : -2 * (J : ℝ) * (log (2 * N / δ) / (2 * J)) = -log (2 * N / δ) := by
    field_simp
  rw [e, exp_neg, exp_log (by positivity), inv_div]

/-- The mean of the reflected variables `1 - X j` is `1 -` the mean of the `X j`. -/
lemma mean_reflect {J : ℕ} (hJ : 0 < J) (x : Fin J → ℝ) :
    (∑ j, (1 - x j)) / J = 1 - (∑ j, x j) / J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- The general form: `a s` is the mean of `J` independent `[0,1]`-valued variables `X s j` of
common mean `m s`. -/
theorem gamma_confidence_of_mean (r : Fin n) {J : ℕ} (hJ : 0 < J)
    (X : Finset (Fin n) → Fin J → Ω → ℝ) (hX : ∀ s j, Measurable (X s j))
    (hb : ∀ s j ω, X s j ω ∈ Set.Icc (0 : ℝ) 1) (hind : ∀ s, iIndepFun (X s) μ)
    (m : Finset (Fin n) → ℝ) (hmean : ∀ s j, μ[X s j] = m s)
    (a : Finset (Fin n) → Ω → ℝ) (ha : ∀ s ω, a s ω = (∑ j, X s j ω) / J)
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ¬ ∀ T (hT : IsBinary r T) (hTne : T.Nonempty),
        loMargin r (fun s => a s ω - radius (sides r).card J δ)
          (fun s => a s ω + radius (sides r).card J δ) T hTne ≤ margin r m T hTne} ≤ δ ∧
    μ.real {ω | ∃ T, ∃ (_ : IsBinary r T) (hTne : T.Nonempty),
        0 < loMargin r (fun s => a s ω - radius (sides r).card J δ)
          (fun s => a s ω + radius (sides r).card J δ) T hTne ∧
        ¬ ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T} ≤ δ := by
  by_cases hδ1 : 1 < δ
  · exact ⟨measureReal_le_one.trans hδ1.le, measureReal_le_one.trans hδ1.le⟩
  have hδ1' : δ ≤ 1 := le_of_not_gt hδ1
  set h := radius (sides r).card J δ
  have hh : 0 ≤ h := radius_nonneg _ _ _
  refine gamma_confidence r m (fun s ω => a s ω - h) (fun s ω => a s ω + h) hδ.le ?_ ?_
  · intro s hs
    have hN : 0 < (sides r).card := card_pos.mpr ⟨s, hs⟩
    rw [← exp_radius hN hJ hδ hδ1']
    refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
      (Consistency.upper_tail hJ (X s) (m s) (hX s) (hb s) (hind s) (hmean s) hh)
    have hω' : m s < a s ω - h := hω
    show h ≤ (∑ j, X s j ω) / J - m s
    rw [← ha s ω]
    linarith
  · intro s hs
    have hN : 0 < (sides r).card := card_pos.mpr ⟨s, hs⟩
    rw [← exp_radius hN hJ hδ hδ1']
    have hint : ∀ j, Integrable (X s j) μ := fun j =>
      Integrable.of_mem_Icc 0 1 (hX s j).aemeasurable (ae_of_all _ (hb s j))
    refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
      (Consistency.upper_tail (μ := μ) hJ (fun j ω => 1 - X s j ω) (1 - m s)
        (fun j => measurable_const.sub (hX s j))
        (fun j ω => by have := hb s j ω; constructor <;> linarith [this.1, this.2])
        ((hind s).comp (fun _ x => 1 - x) (fun _ => measurable_const.sub measurable_id))
        (fun j => by rw [integral_sub (integrable_const _) (hint j), hmean s j]; simp) hh)
    have hω' : a s ω + h < m s := hω
    show h ≤ (∑ j, (1 - X s j ω)) / J - (1 - m s)
    rw [mean_reflect hJ, ← ha s ω]
    linarith

/-- **Proposition 7.11 (`prop:gammablocks`), block-average form.**  For each non-trivial split `s`
let `X s j ∈ [0,1]`, `j < J`, be independent with common mean `m s` (the block supports
`w_j(s)/k`), `h = √(log(2N/δ)/(2J))`, `N = |sides r|`, and take the bounds
`ℓ s = (∑ⱼ X s j)/J - h`, `u s = (∑ⱼ X s j)/J + h`.  Then the conclusions of Theorem 7.9 hold:
(i) with probability at least `1 - δ`, `γ(T) ≥ γ_lo(T)` for every binary `T` simultaneously, and
(ii) a false certificate has probability at most `δ`. -/
theorem gamma_confidence_avg (r : Fin n) {J : ℕ} (hJ : 0 < J)
    (X : Finset (Fin n) → Fin J → Ω → ℝ) (hX : ∀ s j, Measurable (X s j))
    (hb : ∀ s j ω, X s j ω ∈ Set.Icc (0 : ℝ) 1) (hind : ∀ s, iIndepFun (X s) μ)
    (m : Finset (Fin n) → ℝ) (hmean : ∀ s j, μ[X s j] = m s) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ¬ ∀ T (hT : IsBinary r T) (hTne : T.Nonempty),
        loMargin r (fun s => (∑ j, X s j ω) / J - radius (sides r).card J δ)
          (fun s => (∑ j, X s j ω) / J + radius (sides r).card J δ) T hTne ≤
          margin r m T hTne} ≤ δ ∧
    μ.real {ω | ∃ T, ∃ (_ : IsBinary r T) (hTne : T.Nonempty),
        0 < loMargin r (fun s => (∑ j, X s j ω) / J - radius (sides r).card J δ)
          (fun s => (∑ j, X s j ω) / J + radius (sides r).card J δ) T hTne ∧
        ¬ ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T} ≤ δ :=
  gamma_confidence_of_mean r hJ X hX hb hind m hmean (fun s ω => (∑ j, X s j ω) / J)
    (fun _ _ => rfl) hδ

/-- The observed support per unit, `w(s)/L` with `L = J k`. -/
noncomputable def rate {J k : ℕ} (Y : Finset (Fin n) → Fin J → Fin k → Ω → ℝ)
    (s : Finset (Fin n)) (ω : Ω) : ℝ :=
  (∑ j, ∑ i, Y s j i ω) / (J * k)

/-- **Proposition 7.11 (`prop:gammablocks`), certifying the margin with dependent units.**  The
units are indexed by a block `j : Fin J` and a position `i : Fin k`; `Y s j i ∈ [0,1]` indicates
that unit `(j, i)` proposes `s`.  The blocks are independent (`iIndepFun` of the block vectors
across `j`), with arbitrary dependence inside a block, and `E[w_j(s)] = k m s` for every block,
`w_j(s) = ∑ᵢ Y s j i`.  With `h = √(log(2N/δ)/(2J))`, `N = |sides r|`, put
`ℓ s = w(s)/L - h` and `u s = w(s)/L + h` (`rate Y s = w(s)/L`).  Then (i) with probability at
least `1 - δ`, `γ(T) ≥ γ_lo(T)` for every binary `T` simultaneously, and (ii) the probability that
some binary `T` has `γ_lo(T) > 0` without being the unique maximum of `m` over compatible sets is at
most `δ`. -/
theorem gamma_confidence_blocks (r : Fin n) {J k : ℕ} (hJ : 0 < J) (hk : 0 < k)
    (Y : Finset (Fin n) → Fin J → Fin k → Ω → ℝ)
    (hmeas : ∀ s j i, Measurable (Y s j i)) (hb : ∀ s j i ω, Y s j i ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ s, iIndepFun (fun j ω => fun i => Y s j i ω) μ)
    (m : Finset (Fin n) → ℝ) (hmean : ∀ s j, μ[fun ω => ∑ i, Y s j i ω] = k * m s)
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ¬ ∀ T (hT : IsBinary r T) (hTne : T.Nonempty),
        loMargin r (fun s => rate Y s ω - radius (sides r).card J δ)
          (fun s => rate Y s ω + radius (sides r).card J δ) T hTne ≤ margin r m T hTne} ≤ δ ∧
    μ.real {ω | ∃ T, ∃ (_ : IsBinary r T) (hTne : T.Nonempty),
        0 < loMargin r (fun s => rate Y s ω - radius (sides r).card J δ)
          (fun s => rate Y s ω + radius (sides r).card J δ) T hTne ∧
        ¬ ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T} ≤ δ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  -- block averages
  set X : Finset (Fin n) → Fin J → Ω → ℝ := fun s j ω => (∑ i, Y s j i ω) / k with hXdef
  have hXmeas : ∀ s j, Measurable (X s j) := fun s j =>
    (Finset.measurable_sum _ fun i _ => hmeas s j i).div_const _
  have hXb : ∀ s j ω, X s j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro s j ω
    have h0 : 0 ≤ ∑ i, Y s j i ω := Finset.sum_nonneg fun i _ => (hb s j i ω).1
    have h1 : ∑ i, Y s j i ω ≤ k := by
      calc ∑ i, Y s j i ω ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb s j i ω).2
        _ = k := by simp
    exact ⟨div_nonneg h0 hkpos.le, (div_le_one hkpos).mpr h1⟩
  have hXind : ∀ s, iIndepFun (X s) μ := by
    intro s
    have hf : ∀ _j : Fin J, Measurable (fun v : Fin k → ℝ => (∑ i, v i) / k) := fun _ =>
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _
    exact (hind s).comp (fun _ v => (∑ i, v i) / k) hf
  have hXmean : ∀ s j, μ[X s j] = m s := by
    intro s j
    simp only [hXdef]
    rw [integral_div, hmean s j]
    field_simp
  refine gamma_confidence_of_mean r hJ X hXmeas hXb hXind m hXmean (rate Y) (fun s ω => ?_) hδ
  simp only [rate, hXdef, ← Finset.sum_div]
  rw [div_div, mul_comm (k : ℝ)]

end Stemma.GammaBlocks
