/-
Bernstein's form of the consistency bound (Theorem 7.4(a) of the technical report,
`thm:consistency`, first inequality):
`P(T is not the unique optimum) ≤ ∑_{σ ∈ R} 2 exp(-L γ² / (8 m_σ + 4 γ / 3))`.

Mathlib (v4.36) has no Bernstein inequality.  It is proved here for averages of independent
`[0,1]`-valued variables of mean `m`, `P(|Ȳ - m| ≥ t) ≤ 2 exp(-L t² / (2 (m + t/3)))`, from the
Chernoff bound of `Chernoff.lean`, the convexity bound `E e^{sY} ≤ 1 + m (e^s - 1)`, and the series
bound `e^s - 1 - s ≤ s² / (2 (1 - s/3))` for `0 ≤ s < 3` (from `(k+2)! ≥ 2·3^k`).  The variance
enters through `Var Y ≤ E Y² ≤ E Y = m`, as in the report.
-/
import Mathlib
import StemmaLean.Chernoff
import StemmaLean.Consistency

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped Nat

namespace Stemma.Bernstein

/-! ### The series bound -/

lemma two_mul_three_pow_le (k : ℕ) : 2 * 3 ^ k ≤ (k + 2)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

/-- `e^s ≤ 1 + s + s² / (2 (1 - s/3))` for `0 ≤ s < 3`. -/
lemma exp_le_bernstein {s : ℝ} (h0 : 0 ≤ s) (h3 : s < 3) :
    exp s ≤ 1 + s + s ^ 2 / (2 * (1 - s / 3)) := by
  have hE : HasSum (fun k : ℕ => s ^ k / (k ! : ℝ)) (exp s) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp s
  have hE2 : HasSum (fun k : ℕ => s ^ (k + 2) / ((k + 2) ! : ℝ)) (exp s - (1 + s)) := by
    have := (hasSum_nat_add_iff' 2).mpr hE
    simpa [Finset.sum_range_succ] using this
  have hq0 : 0 ≤ s / 3 := by positivity
  have hq1 : s / 3 < 1 := by linarith
  have hG : HasSum (fun k : ℕ => s ^ 2 / 2 * (s / 3) ^ k) (s ^ 2 / 2 * (1 - s / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hle : exp s - (1 + s) ≤ s ^ 2 / 2 * (1 - s / 3)⁻¹ := by
    refine hasSum_le (fun k => ?_) hE2 hG
    rw [show s ^ 2 / 2 * (s / 3) ^ k = s ^ (k + 2) / (2 * 3 ^ k) by
      rw [div_pow, pow_add]; field_simp]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast two_mul_three_pow_le k
  have : s ^ 2 / 2 * (1 - s / 3)⁻¹ = s ^ 2 / (2 * (1 - s / 3)) := by
    field_simp
  linarith

/-- `e^{-s} - 1 + s ≤ e^s - 1 - s` for `s ≥ 0` (`sinh s ≥ s`). -/
lemma exp_neg_le (s : ℝ) (h0 : 0 ≤ s) : exp (-s) - 1 + s ≤ exp s - 1 - s := by
  have := Real.self_le_sinh_iff.mpr h0
  rw [Real.sinh_eq] at this
  linarith

/-! ### Bernstein's inequality for averages of `[0,1]` variables -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Bernstein exponent: for `m ≥ 0`, `t > 0`, some `s ≥ 0` gives both
`-s t + m (e^s - 1 - s) ≤ -t² / (2 (m + t/3))`. -/
lemma bernstein_exponent {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t) :
    ∃ s : ℝ, 0 ≤ s ∧ -s * t + m * (exp s - 1 - s) ≤ -(t ^ 2 / (2 * (m + t / 3))) := by
  rcases hm.lt_or_eq with hm | hm
  · set D := m + t / 3
    have hD : 0 < D := by positivity
    refine ⟨t / D, by positivity, ?_⟩
    have hs3 : t / D < 3 := by rw [div_lt_iff₀ hD]; simp only [D]; linarith
    have hb := exp_le_bernstein (by positivity : 0 ≤ t / D) hs3
    have h1 : 1 - t / D / 3 = m / D := by field_simp; simp only [D]; ring
    have key : m * ((t / D) ^ 2 / (2 * (1 - t / D / 3))) = t ^ 2 / (2 * D) := by
      rw [h1]; field_simp
    have : m * (exp (t / D) - 1 - t / D) ≤ t ^ 2 / (2 * D) := by
      rw [← key]; apply mul_le_mul_of_nonneg_left _ hm.le; linarith
    have e : -(t / D) * t = -(t ^ 2 / D) := by ring
    rw [e]
    have : t ^ 2 / D = 2 * (t ^ 2 / (2 * D)) := by field_simp
    linarith
  · subst hm
    refine ⟨3 / 2, by norm_num, ?_⟩
    have : t ^ 2 / (2 * (0 + t / 3)) = 3 / 2 * t := by field_simp; ring
    rw [this]; simp

/-- Upper tail: `P((m + t) L ≤ ∑ Y) ≤ exp(-L t² / (2 (m + t/3)))`. -/
lemma bernstein_upper {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m t : ℝ}
    (hm : ∀ u, μ[Y u] = m) (hm0 : 0 ≤ m) (ht : 0 < t) :
    μ.real {ω | (m + t) * L ≤ ∑ u, Y u ω} ≤ exp (-(L * (t ^ 2 / (2 * (m + t / 3))))) := by
  obtain ⟨s, hs, hexp⟩ := bernstein_exponent hm0 ht
  refine (Chernoff.upper_tail Y hmeas hb hind hm (m + t) hs).trans ?_
  have hbr : 1 + (exp s - 1) * m ≤ exp ((exp s - 1) * m) := by
    have := Real.add_one_le_exp ((exp s - 1) * m); linarith
  calc (exp (-s * (m + t)) * (1 + (exp s - 1) * m)) ^ L
      ≤ (exp (-s * (m + t)) * exp ((exp s - 1) * m)) ^ L := by
        gcongr
        · have : 0 ≤ 1 + (exp s - 1) * m := by
            have : 1 ≤ exp s := Real.one_le_exp hs; nlinarith
          positivity
    _ = exp (L * (-s * t + m * (exp s - 1 - s))) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        nlinarith

/-- Lower tail: `P(∑ Y ≤ (m - t) L) ≤ exp(-L t² / (2 (m + t/3)))`. -/
lemma bernstein_lower {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m t : ℝ}
    (hm : ∀ u, μ[Y u] = m) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (ht : 0 < t) :
    μ.real {ω | ∑ u, Y u ω ≤ (m - t) * L} ≤ exp (-(L * (t ^ 2 / (2 * (m + t / 3))))) := by
  obtain ⟨s, hs, hexp⟩ := bernstein_exponent hm0 ht
  refine (Chernoff.lower_tail Y hmeas hb hind hm (m - t) hs).trans ?_
  have hbr : 1 + (exp (-s) - 1) * m ≤ exp ((exp (-s) - 1) * m) := by
    have := Real.add_one_le_exp ((exp (-s) - 1) * m); linarith
  have hsinh := exp_neg_le s hs
  calc (exp (s * (m - t)) * (1 + (exp (-s) - 1) * m)) ^ L
      ≤ (exp (s * (m - t)) * exp ((exp (-s) - 1) * m)) ^ L := by
        gcongr
        · have : 0 ≤ 1 + (exp (-s) - 1) * m := by nlinarith [exp_pos (-s)]
          positivity
    _ = exp (L * (-s * t + m * (exp (-s) - 1 + s))) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        have : m * (exp (-s) - 1 + s) ≤ m * (exp s - 1 - s) := mul_le_mul_of_nonneg_left hsinh hm0
        nlinarith

/-- **Bernstein's inequality** for the average of `L` independent `[0,1]`-valued variables of mean
`m`: `P(|Ȳ - m| ≥ t) ≤ 2 exp(-L t² / (2 (m + t/3)))`. -/
theorem bernstein_two {L : ℕ} (hL : 0 < L) (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m t : ℝ}
    (hm : ∀ u, μ[Y u] = m) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (ht : 0 < t) :
    μ.real {ω | t ≤ |(∑ u, Y u ω) / L - m|} ≤ 2 * exp (-(L * (t ^ 2 / (2 * (m + t / 3))))) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : {ω | t ≤ |(∑ u, Y u ω) / L - m|} ⊆
      {ω | (m + t) * L ≤ ∑ u, Y u ω} ∪ {ω | ∑ u, Y u ω ≤ (m - t) * L} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right
      have : (∑ u, Y u ω) / L ≤ m - t := by linarith
      rwa [div_le_iff₀ hLpos] at this
    · left
      have : m + t ≤ (∑ u, Y u ω) / L := by linarith
      rwa [le_div_iff₀ hLpos] at this
  calc μ.real _ ≤ μ.real ({ω | (m + t) * L ≤ ∑ u, Y u ω} ∪ {ω | ∑ u, Y u ω ≤ (m - t) * L}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (bernstein_upper Y hmeas hb hind hm hm0 ht)
        (bernstein_lower Y hmeas hb hind hm hm0 hm1 ht)
    _ = _ := by ring

/-- Consistency, Bernstein form, for any family system with the matching property (taken as the
hypothesis `hmatch`, as in `Consistency.consistency_of_matching`). -/
theorem consistency_bernstein_of_matching {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Compat : Finset ι → Prop) (T : Finset ι) (m : ι → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hmatch : ∀ S, Compat S → S ≠ T → (T \ S).Nonempty ∧ (S \ T).card ≤ (T \ S).card)
    (hgap : ∀ S, Compat S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : ι → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset ι) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, Compat S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      ∑ σ ∈ R, 2 * exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) := by
  set A : ι → Set Ω := fun σ => {ω | γ / 2 ≤ |(∑ u, Y σ u ω) / L - m σ|}
  have hsub : {ω | ∃ S, Compat S ∧ S ≠ T ∧
      ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ⊆ ⋃ σ ∈ R, A σ := by
    intro ω hω
    obtain ⟨S, hS, hne, hle⟩ := hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, A, Set.mem_ofPred_eq, not_le] at hnot
    have hdev : ∀ σ, |(∑ u, Y σ u ω) / L - m σ| < γ / 2 := by
      intro σ
      by_cases hσ : σ ∈ R
      · exact hnot σ hσ
      · simp [hR σ hσ, hmR σ hσ]; linarith
    have := Consistency.counting_core Compat T m (fun σ => (∑ u, Y σ u ω) / L) γ hγ.le hmatch
      hgap hdev S hS hne
    linarith
  have hm01 : ∀ σ, 0 ≤ m σ ∧ m σ ≤ 1 := by
    intro σ
    set u0 : Fin L := ⟨0, hL⟩
    have hint : Integrable (Y σ u0) μ :=
      Integrable.of_mem_Icc 0 1 (hmeas σ u0).aemeasurable (ae_of_all _ (hb σ u0))
    have h1 : ∫ ω, Y σ u0 ω ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ :=
      integral_mono hint (integrable_const _) fun ω => (hb σ u0 ω).2
    rw [← hmean σ u0]
    refine ⟨integral_nonneg fun ω => (hb σ u0 ω).1, ?_⟩
    simpa using h1
  calc _ ≤ μ.real (⋃ σ ∈ R, A σ) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ σ ∈ R, μ.real (A σ) := measureReal_biUnion_finset_le R A
    _ ≤ ∑ σ ∈ R, 2 * exp (-(L * ((γ / 2) ^ 2 / (2 * (m σ + γ / 2 / 3))))) :=
        sum_le_sum fun σ _ =>
          bernstein_two hL (Y σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) (hm01 σ).1 (hm01 σ).2
            (by positivity)
    _ = _ := by
        refine sum_congr rfl fun σ _ => ?_
        have h0 := (hm01 σ).1
        congr 2
        have : 0 < 8 * m σ + 4 * γ / 3 := by positivity
        have : 0 < m σ + γ / 2 / 3 := by positivity
        field_simp
        ring

/-- **Theorem 7.4(a) (`thm:consistency`), Bernstein form.**  Under the hypotheses of
`Consistency.consistency` (binary `T`, independent units with `Y σ u ∈ [0,1]` of mean `m σ`, the
margin inequality for `γ > 0`, splits outside `R` never proposed), the probability that some
other compatible set of non-trivial splits is at least as heavy as `T` is at most
`∑_{σ ∈ R} 2 exp(-L γ² / (8 m_σ + 4 γ / 3))`; with `R = T ∪ F` this is the report's first bound.
The matching property is Lemma 6.1, proved. -/
theorem consistency_bernstein {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsBinary r T) (m : Finset (Fin n) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ S, Splits.IsSystem r S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, Splits.IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      ∑ σ ∈ R, 2 * exp (-(L * γ ^ 2 / (8 * m σ + 4 * γ / 3))) :=
  consistency_bernstein_of_matching (Splits.IsSystem r) T m γ hγ
    (fun S hS hne => by
      obtain ⟨h1, h2, -⟩ := Splits.displacement_matching hT hS hne
      exact ⟨h1, h2⟩)
    hgap hL Y hmeas hb hind hmean R hR hmR

end Stemma.Bernstein
