/-
The margin and its consequences: Lemma 7.3 (`lem:gamma`, computing γ), Corollary 7.6
(`cor:samplesize`, sample size) and Theorem 7.4(b) (`thm:consistency`, inconsistency when another
compatible set has larger expected support).
-/
import Mathlib
import StemmaLean.Bernstein
import StemmaLean.Cutting

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped Classical

namespace Stemma.Margin

open Splits

variable {n : ℕ}

/-! ### Lemma 7.3, computing γ -/

/-- The competitors of `T`: the pairwise compatible sets of non-trivial splits other than `T`. -/
noncomputable def competitors (r : Fin n) (T : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  univ.filter fun S => IsSystem r S ∧ S ≠ T

/-- The ratio of Definition 7.2 for one competitor. -/
noncomputable def ratio (m : Finset (Fin n) → ℝ) (T S : Finset (Finset (Fin n))) : ℝ :=
  (∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ) / (T \ S).card

lemma competitors_nonempty {r : Fin n} {T : Finset (Finset (Fin n))} (hTne : T.Nonempty) :
    (competitors r T).Nonempty :=
  ⟨∅, by
    simp only [competitors, mem_filter, mem_univ, true_and]
    exact ⟨⟨by simp, fun a ha => by simp at ha⟩, (nonempty_iff_ne_empty.mp hTne).symm⟩⟩

/-- **Definition 7.2 (`def:gamma`), the margin**: the minimum of the ratio over the competitors
(for `T` with at least one split, so that `∅` is a competitor). -/
noncomputable def margin (r : Fin n) (m : Finset (Fin n) → ℝ) (T : Finset (Finset (Fin n)))
    (hTne : T.Nonempty) : ℝ :=
  (competitors r T).inf' (competitors_nonempty hTne) (ratio m T)

/-- The shifted supports `m^{(g)}`: `m σ - g` on `T`, `m σ` elsewhere. -/
noncomputable def shift (T : Finset (Finset (Fin n))) (m : Finset (Fin n) → ℝ) (g : ℝ) :
    Finset (Fin n) → ℝ := fun σ => if σ ∈ T then m σ - g else m σ

lemma shift_diff (T S : Finset (Finset (Fin n))) (m : Finset (Fin n) → ℝ) (g : ℝ) :
    wt (shift T m g) T - wt (shift T m g) S =
      (∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ) - g * (T \ S).card := by
  unfold wt
  rw [← sum_sdiff_sub_sum_sdiff]
  have h1 : ∑ σ ∈ T \ S, shift T m g σ = ∑ σ ∈ T \ S, m σ - g * (T \ S).card := by
    rw [sum_congr rfl fun σ hσ => (show shift T m g σ = m σ - g by
      simp [shift, (mem_sdiff.mp hσ).1]), sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ σ ∈ S \ T, shift T m g σ = ∑ σ ∈ S \ T, m σ :=
    sum_congr rfl fun σ hσ => by simp [shift, (mem_sdiff.mp hσ).2]
  rw [h1, h2]; ring

/-- **Lemma 7.3 (`lem:gamma`), computing γ.**  For binary `T` and any real `g`, `T` is a maximum
of the shifted supports `m^{(g)}` over compatible sets if and only if `g ≤ γ`.  The set of such
`g` is therefore a half-line, which makes bisection valid (`bisect_spec`, in the bracket
`[-1, 1]` of `margin_mem_Icc`). -/
theorem computing_gamma {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) (g : ℝ) :
    (∀ S, IsSystem r S → wt (shift T m g) S ≤ wt (shift T m g) T) ↔ g ≤ margin r m T hTne := by
  have hpos : ∀ S ∈ competitors r T, (0 : ℝ) < (T \ S).card := fun S hS => by
    simp only [competitors, mem_filter, mem_univ, true_and] at hS
    exact_mod_cast card_pos.mpr (displacement_matching hT hS.1 hS.2).1
  unfold margin
  rw [le_inf'_iff]
  constructor
  · intro h S hS
    have := h S (by simp [competitors] at hS; exact hS.1)
    have hd := shift_diff T S m g
    rw [ratio, le_div_iff₀ (hpos S hS)]
    linarith
  · intro h S hS
    by_cases e : S = T
    · rw [e]
    have hc : S ∈ competitors r T := by simp [competitors, hS, e]
    have := h S hc
    rw [ratio, le_div_iff₀ (hpos S hc)] at this
    have hd := shift_diff T S m g
    linarith

/-- The margin satisfies the margin inequality used by the consistency theorems. -/
lemma margin_gap {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) :
    ∀ S, IsSystem r S → S ≠ T →
      margin r m T hTne * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ := by
  intro S hS hne
  have hc : S ∈ competitors r T := by simp [competitors, hS, hne]
  have hpos : (0 : ℝ) < (T \ S).card :=
    by exact_mod_cast card_pos.mpr (displacement_matching hT hS hne).1
  have := inf'_le (ratio m T) hc
  rw [ratio, le_div_iff₀ hpos] at this
  exact this

/-- **Lemma 7.3, the bracket.**  For binary `T` with at least one split and supports in `[0,1]`,
`γ ∈ [-1, 1]`: the empty set is a competitor, of ratio `m(T)/|T| ≤ 1`, and every competitor has
`|S \ T| ≤ |T \ S|`, so its ratio is at least `-|S \ T|/|T \ S| ≥ -1`. -/
theorem margin_mem_Icc {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1) :
    margin r m T hTne ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpos : ∀ S ∈ competitors r T, (0 : ℝ) < (T \ S).card := fun S hS => by
    simp only [competitors, mem_filter, mem_univ, true_and] at hS
    exact_mod_cast card_pos.mpr (displacement_matching hT hS.1 hS.2).1
  have he : (∅ : Finset (Finset (Fin n))) ∈ competitors r T := by
    simp only [competitors, mem_filter, mem_univ, true_and]
    exact ⟨⟨by simp, fun a ha => by simp at ha⟩, (nonempty_iff_ne_empty.mp hTne).symm⟩
  constructor
  · unfold margin
    rw [le_inf'_iff]
    intro S hS
    have hS' := hS
    simp only [competitors, mem_filter, mem_univ, true_and] at hS'
    have hcard : ((S \ T).card : ℝ) ≤ (T \ S).card := by
      exact_mod_cast (displacement_matching hT hS'.1 hS'.2).2.1
    have hA : 0 ≤ ∑ σ ∈ T \ S, m σ := sum_nonneg fun σ _ => hm0 σ
    have hB : ∑ σ ∈ S \ T, m σ ≤ (S \ T).card := by
      have := sum_le_sum fun σ (_ : σ ∈ S \ T) => hm1 σ
      simpa using this
    rw [ratio, le_div_iff₀ (hpos S hS)]
    linarith
  · refine (inf'_le (ratio m T) he).trans ?_
    have h := hpos ∅ he
    rw [ratio, div_le_one h]
    simp only [sdiff_empty, empty_sdiff, sum_empty, sub_zero]
    have := sum_le_sum fun σ (_ : σ ∈ T) => hm1 σ
    simpa using this

open scoped Classical in
/-- **Lemma 7.3, the bisection.**  Start from the bracket `[-1, 1]`; at each step test the
midpoint `c` by comparing optimum values (is `T` a maximum of `m^{(c)}`?), and keep the upper
half if the test succeeds, the lower half otherwise. -/
noncomputable def bisect (r : Fin n) (T : Finset (Finset (Fin n))) (m : Finset (Fin n) → ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (-1, 1)
  | k + 1 =>
    let c := ((bisect r T m k).1 + (bisect r T m k).2) / 2
    if ∀ S, IsSystem r S → wt (shift T m c) S ≤ wt (shift T m c) T then (c, (bisect r T m k).2)
    else ((bisect r T m k).1, c)

/-- **Lemma 7.3, bisection is valid.**  For binary `T` with supports in `[0,1]`, after `k` steps
the bracket `[a_k, b_k]` contains `γ` and has width `2 · 2^{-k}`; so `|a_k - γ| ≤ 2 · 2^{-k}`, one
optimisation per step. -/
theorem bisect_spec {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1)
    (k : ℕ) :
    (bisect r T m k).1 ≤ margin r m T hTne ∧ margin r m T hTne ≤ (bisect r T m k).2 ∧
      (bisect r T m k).2 - (bisect r T m k).1 = 2 / 2 ^ k := by
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := margin_mem_Icc hT hTne m hm0 hm1
    simp only [bisect]; norm_num; exact ⟨h1, h2⟩
  | succ k ih =>
    obtain ⟨ha, hb, hw⟩ := ih
    set c := ((bisect r T m k).1 + (bisect r T m k).2) / 2 with hc
    have e : (2 : ℝ) / 2 ^ (k + 1) = (2 / 2 ^ k) / 2 := by rw [pow_succ, div_div]
    by_cases ht : ∀ S, IsSystem r S → wt (shift T m c) S ≤ wt (shift T m c) T
    · have hcg := (computing_gamma hT hTne m c).mp ht
      simp only [bisect, ← hc, if_pos ht]
      refine ⟨hcg, hb, ?_⟩
      rw [e, ← hw, hc]; ring
    · have hcg : margin r m T hTne < c := not_le.mp fun h => ht ((computing_gamma hT hTne m c).mpr h)
      simp only [bisect, ← hc, if_neg ht]
      refine ⟨ha, hcg.le, ?_⟩
      rw [e, ← hw, hc]; ring

/-- The lower end of the bracket converges to `γ`: `0 ≤ γ - a_k ≤ 2 · 2^{-k}`. -/
theorem bisect_error {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1)
    (k : ℕ) :
    |margin r m T hTne - (bisect r T m k).1| ≤ 2 / 2 ^ k := by
  obtain ⟨ha, hb, hw⟩ := bisect_spec hT hTne m hm0 hm1 k
  rw [abs_of_nonneg (by linarith)]; linarith

/-! ### Corollary 7.6, sample size -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Corollary 7.6 (`cor:samplesize`), sample size.**  Under the hypotheses of
`Bernstein.consistency_bernstein`, if `0 < ε < 1`, `m σ ≤ m_max` on `R` and
`L ≥ (8 m_max + 4γ/3)/γ² · log(2|R|/ε)`, the failure probability is at most `ε`.  With
`R = T ∪ F`, `|R| = n − 3 + K`, the report's statement. -/
theorem sample_size (r : Fin n) (T : Finset (Finset (Fin n))) (hT : IsBinary r T)
    (m : Finset (Fin n) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ S, IsSystem r S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0)
    {ε mmax : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hmax : ∀ σ ∈ R, m σ ≤ mmax)
    (hLbig : (8 * mmax + 4 * γ / 3) / γ ^ 2 * Real.log (2 * R.card / ε) ≤ L) :
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤ ε := by
  refine (Bernstein.consistency_bernstein r T hT m γ hγ hgap hL Y hmeas hb hind hmean R hR
    hmR).trans ?_
  rcases R.eq_empty_or_nonempty with hRe | hRne
  · simp [hRe, hε.le]
  have hm0 : ∀ σ, 0 ≤ m σ := fun σ => by
    rw [← hmean σ ⟨0, hL⟩]; exact integral_nonneg fun ω => (hb σ _ ω).1
  obtain ⟨σ₀, hσ₀⟩ := hRne
  have hmax0 : 0 ≤ mmax := (hm0 σ₀).trans (hmax σ₀ hσ₀)
  have hRpos : (0 : ℝ) < R.card := by exact_mod_cast card_pos.mpr ⟨σ₀, hσ₀⟩
  set D := 8 * mmax + 4 * γ / 3
  have hD : 0 < D := by positivity
  have hq : 0 < 2 * R.card / ε := by positivity
  -- each term is at most `ε / |R|`
  have hterm : ∀ σ ∈ R, 2 * exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) ≤ ε / R.card := by
    intro σ hσ
    have hDσ : 0 < 8 * m σ + 4 * γ / 3 := by have := hm0 σ; positivity
    have hle : L * γ ^ 2 / D ≤ L * γ ^ 2 / (8 * m σ + 4 * γ / 3) := by
      apply div_le_div_of_nonneg_left (by positivity) hDσ; have := hmax σ hσ; simp only [D]
      linarith
    have hlog : Real.log (2 * R.card / ε) ≤ L * γ ^ 2 / D := by
      rw [le_div_iff₀ hD]
      have h := mul_le_mul_of_nonneg_right hLbig (sq_nonneg γ)
      have e : D / γ ^ 2 * Real.log (2 * R.card / ε) * γ ^ 2 =
          Real.log (2 * R.card / ε) * D := by field_simp
      rw [e] at h; linarith
    have : exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) ≤ ε / (2 * R.card) := by
      calc exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) ≤ exp (-Real.log (2 * R.card / ε)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = ε / (2 * R.card) := by
            rw [Real.exp_neg, Real.exp_log hq, inv_div]
    calc 2 * exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) ≤ 2 * (ε / (2 * R.card)) := by linarith
      _ = ε / R.card := by field_simp
  calc ∑ σ ∈ R, 2 * exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) ≤ ∑ _σ ∈ R, ε / R.card :=
        sum_le_sum hterm
    _ = ε := by rw [sum_const, nsmul_eq_mul]; field_simp

/-! ### Theorem 7.4(b), inconsistency -/

/-- **Theorem 7.4(b) (`thm:consistency`).**  Units form an infinite sequence; the vectors
`(Y σ u)_σ` of indicators are pairwise independent and identically distributed across `u`, with
values in `[0,1]` and means `m σ`.  If some compatible `S` has `m(S) > m(T)`, then almost surely
`w(S) > w(T)` for all large `L`, and the probability that `T` is a maximum-weight compatible set
for the supports of the first `L` units tends to `0`.  (`T` need not be binary; the report states
`P(Ŝ_L = T) → 0`, which follows since `Ŝ_L = T` requires `T` to be a maximum.) -/
theorem inconsistency (r : Fin n) (T S : Finset (Finset (Fin n))) (hS : IsSystem r S)
    (Y : Finset (Fin n) → ℕ → Ω → ℝ) (hmeas : ∀ σ u, Measurable (Y σ u))
    (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hindep : Pairwise fun i j => IndepFun (fun ω σ => Y σ i ω) (fun ω σ => Y σ j ω) μ)
    (hident : ∀ u, IdentDistrib (fun ω σ => Y σ u ω) (fun ω σ => Y σ 0 ω) μ μ)
    (m : Finset (Fin n) → ℝ) (hmean : ∀ σ, μ[Y σ 0] = m σ)
    (hlt : ∑ σ ∈ T, m σ < ∑ σ ∈ S, m σ) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop,
      ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω) ∧
    Tendsto (fun L => μ {ω | ∀ S', IsSystem r S' →
        ∑ σ ∈ S', ∑ u ∈ range L, Y σ u ω ≤ ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω}) atTop (𝓝 0) := by
  set g : (Finset (Fin n) → ℝ) → ℝ := fun v => ∑ σ ∈ S, v σ - ∑ σ ∈ T, v σ
  have hg : Measurable g :=
    (Finset.measurable_sum S fun σ _ => measurable_pi_apply σ).sub
      (Finset.measurable_sum T fun σ _ => measurable_pi_apply σ)
  set D : ℕ → Ω → ℝ := fun u ω => g (fun σ => Y σ u ω)
  have hVmeas : ∀ u, Measurable fun ω σ => Y σ u ω := fun u =>
    measurable_pi_iff.mpr fun σ => hmeas σ u
  have hDmeas : ∀ u, Measurable (D u) := fun u => hg.comp (hVmeas u)
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
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop,
      ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω := by
    filter_upwards [H] with ω hω
    rw [hmeanD] at hω
    have hev := hω.eventually (lt_mem_nhds (sub_pos.mpr hlt))
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
    rw [smul_eq_mul, hsum] at hL
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr hLpos)).mp hL
    linarith
  refine ⟨hae, ?_⟩
  have hmeasW : ∀ (U : Finset (Finset (Fin n))) L,
      Measurable fun ω => ∑ σ ∈ U, ∑ u ∈ range L, Y σ u ω := fun U L =>
    Finset.measurable_sum U fun σ _ => Finset.measurable_sum _ fun u _ => hmeas σ u
  have hP := Cutting.prob_tendsto_of_ae_eventually (μ := μ)
    (G := fun L => {ω | ∑ σ ∈ T, ∑ u ∈ range L, Y σ u ω < ∑ σ ∈ S, ∑ u ∈ range L, Y σ u ω})
    (fun L => measurableSet_lt (hmeasW T L) (hmeasW S L)) hae
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP (fun _ => zero_le)
    fun L => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt] at hω ⊢
  exact hω S hS

end Stemma.Margin
