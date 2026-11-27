/-
Chernoff bounds: the pairwise bound (Theorem 7.1 of the technical report, `thm:pairwise`) and the
Bédier threshold (Theorem 8.2, `thm:bedier`), in its Kullback–Leibler form and its simplified form.

Model.  Units `u : Fin L` are independent: the vectors `(Y σ u)_σ` are independent across `u`
(`iIndepFun`).  `Y σ u` indicates that unit `u` proposes split `σ` (values in `{0,1}` for the
pairwise bound, in `[0,1]` for the threshold), with mean `m σ` for every unit.  A split with
`m σ = 0` is never proposed (`hzero`).  For the pairwise bound, a unit never proposes two splits
in conflict: this is Lemma 3.5 (`Stemma.exclusivity`), entered as the hypothesis `hexcl`.

Concentration is Mathlib's exponential Chernoff inequality (`measure_ge_le_exp_mul_mgf`) with the
multiplicativity of the moment generating function over independent sums (`iIndepFun.mgf_sum`).
-/
import Mathlib
import StemmaLean.Splits

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped Classical

namespace Stemma.Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### A Chernoff bound for sums of independent bounded variables -/

lemma integrable_exp_of_abs_le {X : Ω → ℝ} (hX : Measurable X) {C : ℝ} (hC : ∀ ω, |X ω| ≤ C)
    (t : ℝ) : Integrable (fun ω => exp (t * X ω)) μ := by
  refine Integrable.of_bound (C := exp (|t| * C)) ?_ (ae_of_all _ fun ω => ?_)
  · exact (measurable_const.mul hX).exp.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
    calc t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ |t| * C := mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg _)

/-- If each of `L` independent variables bounded by `1` has `mgf ≤ B` at `t ≥ 0`, then
`P(ε ≤ ∑ X) ≤ exp(-t ε) B^L`. -/
lemma chernoff_sum {L : ℕ} (X : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hbd : ∀ u ω, |X u ω| ≤ 1) (hind : iIndepFun X μ) {t B : ℝ} (ht : 0 ≤ t)
    (hB : ∀ u, mgf (X u) μ t ≤ B) (ε : ℝ) :
    μ.real {ω | ε ≤ ∑ u, X u ω} ≤ exp (-t * ε) * B ^ L := by
  have hsum : (fun ω => ∑ u, X u ω) = ∑ u, X u := by ext ω; simp [Finset.sum_apply]
  have hbdS : ∀ ω, |∑ u, X u ω| ≤ L := fun ω => by
    calc |∑ u, X u ω| ≤ ∑ u, |X u ω| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u : Fin L, (1 : ℝ) := sum_le_sum fun u _ => hbd u ω
      _ = L := by simp
  have hint := integrable_exp_of_abs_le (μ := μ)
    (Finset.measurable_sum _ fun u _ => hmeas u) hbdS t
  have H := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ u, X u ω) ε ht hint
  refine H.trans (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
  rw [hsum, hind.mgf_sum hmeas]
  calc ∏ u ∈ (univ : Finset (Fin L)), mgf (X u) μ t ≤ ∏ _u ∈ (univ : Finset (Fin L)), B := by
        gcongr with u _
        · exact fun i _ => mgf_nonneg
        · exact hB u
    _ = B ^ L := by simp

/-- The moment generating function of a `[0,1]`-valued variable of mean `m`:
`mgf Y t ≤ 1 + (exp t - 1) m`, by convexity of `exp`. -/
lemma mgf_le_unit {Y : Ω → ℝ} (hmeas : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)
    {m : ℝ} (hm : μ[Y] = m) (t : ℝ) : mgf Y μ t ≤ 1 + (exp t - 1) * m := by
  have hpt : ∀ ω, exp (t * Y ω) ≤ 1 + (exp t - 1) * Y ω := by
    intro ω
    have h := hb ω
    have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (sub_nonneg.mpr h.2) h.1
      (by ring : (1 - Y ω) + Y ω = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at this
    calc exp (t * Y ω) = exp (Y ω * t) := by rw [mul_comm]
      _ ≤ (1 - Y ω) + Y ω * exp t := this
      _ = _ := by ring
  have hYint : Integrable Y μ := Integrable.of_mem_Icc 0 1 hmeas.aemeasurable (ae_of_all _ hb)
  have hbd : ∀ ω, |Y ω| ≤ 1 := fun ω => abs_le.mpr ⟨by linarith [(hb ω).1], (hb ω).2⟩
  unfold mgf
  calc μ[fun ω => exp (t * Y ω)] ≤ μ[fun ω => 1 + (exp t - 1) * Y ω] :=
        integral_mono (f := fun ω => exp (t * Y ω)) (g := fun ω => 1 + (exp t - 1) * Y ω)
          (integrable_exp_of_abs_le hmeas hbd t)
          ((integrable_const _).add (hYint.const_mul _)) hpt
    _ = 1 + (exp t - 1) * m := by
        rw [integral_add (integrable_const _) (hYint.const_mul _), integral_const_mul, hm]
        simp

/-- The moment generating function of `B - A` for two exclusive indicators `A, B` of means
`a, b`: `1 + (exp(-t) - 1) a + (exp t - 1) b`. -/
lemma mgf_pair {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hA01 : ∀ ω, A ω = 0 ∨ A ω = 1) (hB01 : ∀ ω, B ω = 0 ∨ B ω = 1)
    (hexcl : ∀ ω, A ω * B ω = 0) {a b : ℝ} (ha : μ[A] = a) (hb : μ[B] = b) (t : ℝ) :
    mgf (fun ω => B ω - A ω) μ t = 1 + (exp (-t) - 1) * a + (exp t - 1) * b := by
  have hpt : ∀ ω, exp (t * (B ω - A ω)) = 1 + (exp (-t) - 1) * A ω + (exp t - 1) * B ω := by
    intro ω
    rcases hA01 ω with h1 | h1 <;> rcases hB01 ω with h2 | h2
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · have := hexcl ω; rw [h1, h2] at this; norm_num at this
  have iA : Integrable A μ := Integrable.of_mem_Icc 0 1 hA.aemeasurable
    (ae_of_all _ fun ω => by rcases hA01 ω with h | h <;> simp [h])
  have iB : Integrable B μ := Integrable.of_mem_Icc 0 1 hB.aemeasurable
    (ae_of_all _ fun ω => by rcases hB01 ω with h | h <;> simp [h])
  unfold mgf
  simp_rw [hpt]
  have h1 : μ[fun ω => 1 + (exp (-t) - 1) * A ω + (exp t - 1) * B ω] =
      μ[fun ω => 1 + (exp (-t) - 1) * A ω] + μ[fun ω => (exp t - 1) * B ω] :=
    integral_add ((integrable_const _).add (iA.const_mul _)) (iB.const_mul _)
  have h2 : μ[fun ω => 1 + (exp (-t) - 1) * A ω] =
      μ[fun _ => (1 : ℝ)] + μ[fun ω => (exp (-t) - 1) * A ω] :=
    integral_add (integrable_const _) (iA.const_mul _)
  rw [h1, h2, integral_const_mul, integral_const_mul, ha, hb]
  simp

/-! ### Theorem 7.1, the pairwise bound -/

/-- `P(w τ ≥ w σ) ≤ (1 + (e^{-t} - 1) m_σ + (e^t - 1) m_τ)^L` for exclusive indicators. -/
lemma pair_tail {L : ℕ} (A B : Fin L → Ω → ℝ) (hA : ∀ u, Measurable (A u))
    (hB : ∀ u, Measurable (B u)) (hA01 : ∀ u ω, A u ω = 0 ∨ A u ω = 1)
    (hB01 : ∀ u ω, B u ω = 0 ∨ B u ω = 1) (hexcl : ∀ u ω, A u ω * B u ω = 0)
    (hind : iIndepFun (fun u ω => B u ω - A u ω) μ) {a b : ℝ} (ha : ∀ u, μ[A u] = a)
    (hb : ∀ u, μ[B u] = b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ u, A u ω ≤ ∑ u, B u ω} ≤ (1 + (exp (-t) - 1) * a + (exp t - 1) * b) ^ L := by
  have hset : {ω | ∑ u, A u ω ≤ ∑ u, B u ω} = {ω | (0 : ℝ) ≤ ∑ u, (B u ω - A u ω)} := by
    ext ω; simp [Finset.sum_sub_distrib]
  rw [hset]
  have hbd : ∀ u ω, |B u ω - A u ω| ≤ 1 := by
    intro u ω
    rcases hA01 u ω with h1 | h1 <;> rcases hB01 u ω with h2 | h2 <;> simp [h1, h2]
  have H := chernoff_sum (μ := μ) (fun u ω => B u ω - A u ω) (fun u => (hB u).sub (hA u)) hbd
    hind ht (B := 1 + (exp (-t) - 1) * a + (exp t - 1) * b)
    (fun u => (mgf_pair (hA u) (hB u) (hA01 u) (hB01 u) (hexcl u) (ha u) (hb u) t).le) 0
  simpa using H

/-- Optimising `t`: for `0 < b < a`, the infimum of the bracket is `1 - (√a - √b)²`. -/
lemma pair_tail_opt {L : ℕ} (A B : Fin L → Ω → ℝ) (hA : ∀ u, Measurable (A u))
    (hB : ∀ u, Measurable (B u)) (hA01 : ∀ u ω, A u ω = 0 ∨ A u ω = 1)
    (hB01 : ∀ u ω, B u ω = 0 ∨ B u ω = 1) (hexcl : ∀ u ω, A u ω * B u ω = 0)
    (hind : iIndepFun (fun u ω => B u ω - A u ω) μ) {a b : ℝ} (ha : ∀ u, μ[A u] = a)
    (hb : ∀ u, μ[B u] = b) (hb0 : 0 < b) (hba : b < a) :
    μ.real {ω | ∑ u, A u ω ≤ ∑ u, B u ω} ≤ (1 - (√a - √b) ^ 2) ^ L := by
  have ha0 : 0 < a := hb0.trans hba
  set x := √a; set y := √b
  have hx : 0 < x := Real.sqrt_pos.mpr ha0
  have hy : 0 < y := Real.sqrt_pos.mpr hb0
  have hxa : x ^ 2 = a := Real.sq_sqrt ha0.le
  have hyb : y ^ 2 = b := Real.sq_sqrt hb0.le
  have hyx : y < x := Real.sqrt_lt_sqrt hb0.le hba
  set t := Real.log (x / y)
  have ht : 0 ≤ t := Real.log_nonneg ((one_le_div hy).mpr hyx.le)
  have e1 : exp t = x / y := Real.exp_log (div_pos hx hy)
  have e2 : exp (-t) = y / x := by rw [Real.exp_neg, e1, inv_div]
  have H := pair_tail A B hA hB hA01 hB01 hexcl hind ha hb ht
  rw [e1, e2] at H
  refine H.trans (le_of_eq ?_)
  congr 1
  rw [← hxa, ← hyb]
  field_simp
  ring

/-- `P(w σ ≤ 0) ≤ (1 - m_σ)^L`, from the pair bound with no rival and `t → ∞`. -/
lemma zero_tail {L : ℕ} (A : Fin L → Ω → ℝ) (hA : ∀ u, Measurable (A u))
    (hA01 : ∀ u ω, A u ω = 0 ∨ A u ω = 1)
    (hind : iIndepFun (fun u ω => -A u ω) μ) {a : ℝ} (ha : ∀ u, μ[A u] = a) :
    μ.real {ω | ∑ u, A u ω ≤ 0} ≤ (1 - a) ^ L := by
  have hind' : iIndepFun (fun u ω => (fun _ _ => (0 : ℝ)) u ω - A u ω) μ := by
    simpa using hind
  have hb : ∀ t : ℝ, 0 ≤ t → μ.real {ω | ∑ u, A u ω ≤ 0} ≤ (1 + (exp (-t) - 1) * a) ^ L := by
    intro t ht
    have H := pair_tail (μ := μ) A (fun _ _ => 0) hA (fun _ => measurable_const) hA01
      (fun _ _ => Or.inl rfl) (fun _ _ => by simp) hind' (a := a) (b := 0) ha
      (fun _ => by simp) ht
    simpa using H
  have hlim : Tendsto (fun t : ℝ => (1 + (exp (-t) - 1) * a) ^ L) atTop (𝓝 ((1 - a) ^ L)) := by
    have h0 : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add ((h0.sub_const 1).mul_const a)).pow L
    convert this using 2; ring
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun t ht => hb t ht⟩)

/-- The false splits that occur at all and cross a true split, as pairs `(τ, σ)`. -/
noncomputable def conflictPairs {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (m : Finset (Fin n) → ℝ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((univ.filter fun τ => Splits.IsSide r τ ∧ τ ∉ T ∧ 0 < m τ) ×ˢ T).filter
    fun p => ¬ Compat p.1 p.2

/-- **Theorem 7.1 (`thm:pairwise`), pairwise bound.**  Let `T` be (the split system of) a binary
stemma, with i.i.d. units as in the file header, and `m τ < m σ` whenever a false split `τ` with
`m τ > 0` and a true split `σ` are in conflict.  Then the probability that `T` is not the unique
solution for the observed supports `w σ = ∑ᵤ Y σ u` (ties counted as failures) is at most
`∑_{(τ,σ) in conflict} (1 - (√m_σ - √m_τ)²)^L + ∑_{σ ∈ T} (1 - m_σ)^L`.
The report's hypothesis `m_σ > 0` for true `σ` is not needed. -/
theorem pairwise_bound {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsBinary r T) {L : ℕ} (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (h01 : ∀ σ u ω, Y σ u ω = 0 ∨ Y σ u ω = 1)
    (hexcl : ∀ σ τ u ω, ¬ Compat σ τ → Y σ u ω * Y τ u ω = 0)
    (hind : iIndepFun (fun u ω => fun σ => Y σ u ω) μ) (m : Finset (Fin n) → ℝ)
    (hmnn : ∀ σ, 0 ≤ m σ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (hzero : ∀ σ, m σ = 0 → ∀ u ω, Y σ u ω = 0)
    (hsep : ∀ τ σ, Splits.IsSide r τ → τ ∉ T → 0 < m τ → σ ∈ T → ¬ Compat τ σ → m τ < m σ) :
    μ.real {ω | ¬ Splits.IsUniqueSolution r (fun σ => ∑ u, Y σ u ω) T} ≤
      ∑ p ∈ conflictPairs r T m, (1 - (√(m p.2) - √(m p.1)) ^ 2) ^ L +
        ∑ σ ∈ T, (1 - m σ) ^ L := by
  set P := conflictPairs r T m
  let E1 : Finset (Fin n) × Finset (Fin n) → Set Ω :=
    fun p => {ω | ∑ u, Y p.2 u ω ≤ ∑ u, Y p.1 u ω}
  let E2 : Finset (Fin n) → Set Ω := fun σ => {ω | ∑ u, Y σ u ω ≤ 0}
  have hsub : {ω | ¬ Splits.IsUniqueSolution r (fun σ => ∑ u, Y σ u ω) T} ⊆
      (⋃ p ∈ P, E1 p) ∪ ⋃ σ ∈ T, E2 σ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, E1, E2, Set.mem_ofPred_eq,
      not_le] at hnot
    apply hω
    apply Splits.local_separation hT
    · intro A _; exact sum_nonneg fun u _ => by rcases h01 A u ω with h | h <;> simp [h]
    · intro τ σ hτ hτT hσ hc
      by_cases hm : 0 < m τ
      · have hp : (τ, σ) ∈ P := by
          simp only [P, conflictPairs, mem_filter, mem_product, mem_univ, true_and]
          exact ⟨⟨⟨hτ, hτT, hm⟩, hσ⟩, hc⟩
        exact hnot.1 _ hp
      · have hm0 : m τ = 0 := le_antisymm (not_lt.mp hm) (hmnn τ)
        have hw : ∑ u, Y τ u ω = 0 := by simp [hzero τ hm0]
        rw [hw]; exact hnot.2 σ hσ
  have hindD : ∀ σ τ : Finset (Fin n), iIndepFun (fun u ω => Y τ u ω - Y σ u ω) μ :=
    fun σ τ => hind.comp (fun _ v => v τ - v σ)
      (fun _ => (measurable_pi_apply τ).sub (measurable_pi_apply σ))
  have hindN : ∀ σ : Finset (Fin n), iIndepFun (fun u ω => -Y σ u ω) μ :=
    fun σ => hind.comp (fun _ v => -v σ) (fun _ => (measurable_pi_apply σ).neg)
  calc μ.real _ ≤ μ.real ((⋃ p ∈ P, E1 p) ∪ ⋃ σ ∈ T, E2 σ) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (⋃ p ∈ P, E1 p) + μ.real (⋃ σ ∈ T, E2 σ) := measureReal_union_le _ _
    _ ≤ ∑ p ∈ P, μ.real (E1 p) + ∑ σ ∈ T, μ.real (E2 σ) :=
        add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _)
    _ ≤ _ := by
        refine add_le_add (sum_le_sum fun p hp => ?_) (sum_le_sum fun σ _ => ?_)
        · simp only [P, conflictPairs, mem_filter, mem_product, mem_univ, true_and] at hp
          obtain ⟨⟨⟨hτ, hτT, hm⟩, hσ⟩, hc⟩ := hp
          exact pair_tail_opt (Y p.2) (Y p.1) (hmeas p.2) (hmeas p.1) (h01 p.2) (h01 p.1)
            (fun u ω => by rw [mul_comm]; exact hexcl p.1 p.2 u ω hc) (hindD p.2 p.1)
            (hmean p.2) (hmean p.1) hm (hsep p.1 p.2 hτ hτT hm hσ hc)
        · exact zero_tail (Y σ) (hmeas σ) (h01 σ) (hindN σ) (hmean σ)

/-! ### Binomial tails and the Kullback–Leibler exponent -/

/-- `P(∑ Y ≤ c L) ≤ (e^{s c} (1 + (e^{-s} - 1) m))^L` for `s ≥ 0`. -/
lemma lower_tail {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m : ℝ}
    (hm : ∀ u, μ[Y u] = m) (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ∑ u, Y u ω ≤ c * L} ≤ (exp (s * c) * (1 + (exp (-s) - 1) * m)) ^ L := by
  have hset : {ω | ∑ u, Y u ω ≤ c * L} = {ω | -(c * L) ≤ ∑ u, -Y u ω} := by
    ext ω; simp [Finset.sum_neg_distrib]
  rw [hset]
  have hbd : ∀ u ω, |-Y u ω| ≤ 1 := fun u ω => by
    rw [abs_neg]; exact abs_le.mpr ⟨by linarith [(hb u ω).1], (hb u ω).2⟩
  have hind' : iIndepFun (fun u ω => -Y u ω) μ := hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have H := chernoff_sum (μ := μ) (fun u ω => -Y u ω) (fun u => (hmeas u).neg) hbd hind' hs
    (B := 1 + (exp (-s) - 1) * m) (fun u => by
      have : mgf (fun ω => -Y u ω) μ s = mgf (Y u) μ (-s) := mgf_neg
      rw [this]; exact mgf_le_unit (hmeas u) (hb u) (hm u) (-s)) (-(c * L))
  refine H.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]; congr 1; ring_nf

/-- `P(c L ≤ ∑ Y) ≤ (e^{-s c} (1 + (e^{s} - 1) m))^L` for `s ≥ 0`. -/
lemma upper_tail {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m : ℝ}
    (hm : ∀ u, μ[Y u] = m) (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | c * L ≤ ∑ u, Y u ω} ≤ (exp (-s * c) * (1 + (exp s - 1) * m)) ^ L := by
  have hbd : ∀ u ω, |Y u ω| ≤ 1 := fun u ω =>
    abs_le.mpr ⟨by linarith [(hb u ω).1], (hb u ω).2⟩
  have H := chernoff_sum (μ := μ) Y hmeas hbd hind hs (B := 1 + (exp s - 1) * m)
    (fun u => mgf_le_unit (hmeas u) (hb u) (hm u) s) (c * L)
  refine H.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]; congr 1; ring_nf

/-- The binary Kullback–Leibler divergence `KL(c ‖ m)`. -/
noncomputable def kl (c m : ℝ) : ℝ := c * Real.log (c / m) + (1 - c) * Real.log ((1 - c) / (1 - m))

lemma kl_expand {c m : ℝ} (hc : 0 < c) (hc1 : c < 1) (hm : 0 < m) (hm1 : m < 1) :
    kl c m = c * (Real.log c - Real.log m) + (1 - c) * (Real.log (1 - c) - Real.log (1 - m)) := by
  unfold kl
  rw [Real.log_div hc.ne' hm.ne', Real.log_div (by linarith) (by linarith)]

/-- Lower tail of a true split: for `0 < c < m < 1`, `P(∑ Y ≤ c L) ≤ exp(-L KL(c ‖ m))`. -/
lemma true_tail_kl {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m c : ℝ}
    (hm : ∀ u, μ[Y u] = m) (hc : 0 < c) (hcm : c < m) (hm1 : m < 1) :
    μ.real {ω | ∑ u, Y u ω ≤ c * L} ≤ exp (-(L * kl c m)) := by
  have hm0 : 0 < m := hc.trans hcm
  have hc1 : c < 1 := hcm.trans hm1
  have p1 : 0 < m * (1 - c) := mul_pos hm0 (by linarith)
  have p2 : 0 < c * (1 - m) := mul_pos hc (by linarith)
  set s := Real.log (m * (1 - c)) - Real.log (c * (1 - m))
  have hs : 0 ≤ s := by
    rw [sub_nonneg]; apply Real.log_le_log p2; nlinarith
  have es : exp (-s) = c * (1 - m) / (m * (1 - c)) := by
    rw [show -s = Real.log (c * (1 - m)) - Real.log (m * (1 - c)) by ring, Real.exp_sub,
      Real.exp_log p2, Real.exp_log p1]
  have H := lower_tail Y hmeas hb hind hm c hs
  refine H.trans (le_of_eq ?_)
  have hbr : 1 + (exp (-s) - 1) * m = exp (Real.log (1 - m) - Real.log (1 - c)) := by
    rw [es, Real.exp_sub, Real.exp_log (by linarith), Real.exp_log (by linarith)]
    field_simp; ring
  rw [hbr, ← Real.exp_add, ← Real.exp_nat_mul, kl_expand hc hc1 hm0 hm1]
  congr 1
  simp only [s, Real.log_mul hm0.ne' (by linarith : (1 - c) ≠ 0),
    Real.log_mul hc.ne' (by linarith : (1 - m) ≠ 0)]
  ring

/-- Upper tail of a false split: for `0 < m < c < 1`, `P(c L ≤ ∑ Y) ≤ exp(-L KL(c ‖ m))`. -/
lemma false_tail_kl {L : ℕ} (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ) {m c : ℝ}
    (hm : ∀ u, μ[Y u] = m) (hm0 : 0 < m) (hmc : m < c) (hc1 : c < 1) :
    μ.real {ω | c * L ≤ ∑ u, Y u ω} ≤ exp (-(L * kl c m)) := by
  have hc : 0 < c := hm0.trans hmc
  have hm1 : m < 1 := hmc.trans hc1
  have p1 : 0 < m * (1 - c) := mul_pos hm0 (by linarith)
  have p2 : 0 < c * (1 - m) := mul_pos hc (by linarith)
  set s := Real.log (c * (1 - m)) - Real.log (m * (1 - c))
  have hs : 0 ≤ s := by
    rw [sub_nonneg]; apply Real.log_le_log p1; nlinarith
  have es : exp s = c * (1 - m) / (m * (1 - c)) := by
    rw [Real.exp_sub, Real.exp_log p2, Real.exp_log p1]
  have H := upper_tail Y hmeas hb hind hm c hs
  refine H.trans (le_of_eq ?_)
  have hbr : 1 + (exp s - 1) * m = exp (Real.log (1 - m) - Real.log (1 - c)) := by
    rw [es, Real.exp_sub, Real.exp_log (by linarith), Real.exp_log (by linarith)]
    field_simp; ring
  rw [hbr, ← Real.exp_add, ← Real.exp_nat_mul, kl_expand hc hc1 hm0 hm1]
  congr 1
  simp only [s, Real.log_mul hm0.ne' (by linarith : (1 - c) ≠ 0),
    Real.log_mul hc.ne' (by linarith : (1 - m) ≠ 0)]
  ring

/-- A true split of rate `1` is never below the threshold: `P(∑ Y ≤ c L) = 0` for `c < 1`,
`L > 0` (Chernoff with `s → ∞`). -/
lemma true_tail_one {L : ℕ} (hL : 0 < L) (Y : Fin L → Ω → ℝ) (hmeas : ∀ u, Measurable (Y u))
    (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (hm : ∀ u, μ[Y u] = 1) {c : ℝ} (hc1 : c < 1) :
    μ.real {ω | ∑ u, Y u ω ≤ c * L} ≤ 0 := by
  have hbd : ∀ s : ℝ, 0 ≤ s →
      μ.real {ω | ∑ u, Y u ω ≤ c * L} ≤ exp (-(s * (1 - c))) ^ L := by
    intro s hs
    refine (lower_tail Y hmeas hb hind hm c hs).trans (le_of_eq ?_)
    congr 1; rw [show 1 + (exp (-s) - 1) * 1 = exp (-s) by ring, ← Real.exp_add]; congr 1; ring
  have hlim : Tendsto (fun s : ℝ => exp (-(s * (1 - c))) ^ L) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s * (1 - c)) atTop atTop :=
      tendsto_id.atTop_mul_const (by linarith)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).pow L
    rw [zero_pow hL.ne'] at h2
    exact h2
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun s hs => hbd s hs⟩)

/-- `KL(c ‖ m) ≥ (√c - √m)²` for `c, m ∈ (0,1)` (through the Hellinger affinity, with
`log z ≤ z - 1`). -/
lemma kl_ge_sq {c m : ℝ} (hc : 0 < c) (hc1 : c < 1) (hm : 0 < m) (hm1 : m < 1) :
    (√c - √m) ^ 2 ≤ kl c m := by
  set p := √c; set q := √m; set p' := √(1 - c); set q' := √(1 - m)
  have hp : 0 < p := Real.sqrt_pos.mpr hc
  have hq : 0 < q := Real.sqrt_pos.mpr hm
  have hp' : 0 < p' := Real.sqrt_pos.mpr (by linarith)
  have hq' : 0 < q' := Real.sqrt_pos.mpr (by linarith)
  have ep : p ^ 2 = c := Real.sq_sqrt hc.le
  have eq_ : q ^ 2 = m := Real.sq_sqrt hm.le
  have ep' : p' ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have eq' : q' ^ 2 = 1 - m := Real.sq_sqrt (by linarith)
  -- `c log(c/m) ≥ 2 c (1 - q/p)` and the same for the complements
  have h1 : c * Real.log (c / m) ≥ 2 * (p ^ 2 - p * q) := by
    have : Real.log (c / m) = -(2 * Real.log (q / p)) := by
      rw [← ep, ← eq_, ← Real.log_rpow (div_pos hq hp)]
      rw [show (q / p) ^ (2 : ℝ) = q ^ 2 / p ^ 2 by rw [div_rpow hq.le hp.le]; norm_cast]
      rw [← Real.log_inv, inv_div]
    rw [this]
    have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [← ep]
    have : p ^ 2 * (q / p - 1) = p * q - p ^ 2 := by field_simp
    nlinarith [sq_nonneg p]
  have h2 : (1 - c) * Real.log ((1 - c) / (1 - m)) ≥ 2 * (p' ^ 2 - p' * q') := by
    have : Real.log ((1 - c) / (1 - m)) = -(2 * Real.log (q' / p')) := by
      rw [← ep', ← eq', ← Real.log_rpow (div_pos hq' hp')]
      rw [show (q' / p') ^ (2 : ℝ) = q' ^ 2 / p' ^ 2 by rw [div_rpow hq'.le hp'.le]; norm_cast]
      rw [← Real.log_inv, inv_div]
    rw [this]
    have hl := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    rw [← ep']
    have : p' ^ 2 * (q' / p' - 1) = p' * q' - p' ^ 2 := by field_simp
    nlinarith [sq_nonneg p']
  unfold kl
  nlinarith [sq_nonneg (p' - q')]

/-! ### Theorem 8.2, the Bédier threshold -/

/-- The false splits that occur at all. -/
noncomputable def falseOcc {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (m : Finset (Fin n) → ℝ) : Finset (Finset (Fin n)) :=
  univ.filter fun τ => Splits.IsSide r τ ∧ τ ∉ T ∧ 0 < m τ

/-- The solution of the problem restricted to the splits of weight greater than `t` is `T`. -/
def RestrictedUnique {n : ℕ} (r : Fin n) (w : Finset (Fin n) → ℝ) (t : ℝ)
    (T : Finset (Finset (Fin n))) : Prop :=
  (∀ σ ∈ T, t < w σ) ∧
    ∀ S, Splits.IsSystem r S → (∀ τ ∈ S, t < w τ) → S ≠ T → Splits.wt w S < Splits.wt w T

/-- The union bound: failure of the threshold estimator needs a true split at or below `c L`
or an occurring false split above it. -/
lemma threshold_union {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsSystem r T) (hTne : T.Nonempty) {L : ℕ} (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1) (m : Finset (Fin n) → ℝ)
    (hmnn : ∀ σ, 0 ≤ m σ) (hzero : ∀ σ, m σ = 0 → ∀ u ω, Y σ u ω = 0) {c : ℝ} (hc : 0 ≤ c) :
    μ.real {ω | ¬ RestrictedUnique r (fun σ => ∑ u, Y σ u ω) (c * L) T} ≤
      ∑ σ ∈ T, μ.real {ω | ∑ u, Y σ u ω ≤ c * L} +
        ∑ τ ∈ falseOcc r T m, μ.real {ω | c * L ≤ ∑ u, Y τ u ω} := by
  have hsub : {ω | ¬ RestrictedUnique r (fun σ => ∑ u, Y σ u ω) (c * L) T} ⊆
      (⋃ σ ∈ T, {ω | ∑ u, Y σ u ω ≤ c * L}) ∪
        ⋃ τ ∈ falseOcc r T m, {ω | c * L ≤ ∑ u, Y τ u ω} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
      not_le] at hnot
    apply hω
    obtain ⟨-, hpos, hlt⟩ := Splits.threshold hT hTne (fun σ => ∑ u, Y σ u ω)
      (fun A _ => sum_nonneg fun u _ => (hb A u ω).1) (c * L)
      (fun τ hτ hτT => by
        by_cases hm : 0 < m τ
        · have : τ ∈ falseOcc r T m := by simp [falseOcc, hτ, hτT, hm]
          exact (hnot.2 τ this).le
        · have hm0 : m τ = 0 := le_antisymm (not_lt.mp hm) (hmnn τ)
          simp only [hzero τ hm0, sum_const_zero]; positivity)
      (fun σ hσ => hnot.1 σ hσ)
    exact ⟨fun σ hσ => hnot.1 σ hσ, hlt⟩
  calc _ ≤ μ.real ((⋃ σ ∈ T, {ω | ∑ u, Y σ u ω ≤ c * L}) ∪
        ⋃ τ ∈ falseOcc r T m, {ω | c * L ≤ ∑ u, Y τ u ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := (measureReal_union_le _ _).trans
        (add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _))

/-- **Theorem 8.2 (`thm:bedier`), Bédier threshold, Kullback–Leibler form.**  Let `T` be the split
system of any stemma with at least one split, with independent units, `Y σ u ∈ [0,1]` of mean
`m σ ≤ 1`, splits of rate `0` never proposed, and `b = min_T m > a = max_{τ ∉ T} m ≥ 0` (entered as
`b ≤ m σ` on `T`, `m τ ≤ a` off `T`).  For `c ∈ (a, b)`, the probability that the solution
restricted to splits of weight greater than `c L` is not `T` is at most
`∑_{σ ∈ T} exp(-L KL(c ‖ m σ)) + ∑_{τ ∈ F} exp(-L KL(c ‖ m τ))`.
For `m σ = 1` the report's term is `0` (`KL = ∞`); Lean's real-valued `kl c 1 = c log c` gives a
term `≥ 1`, a weaker but valid bound; `bedier_threshold_kl` omits those terms, as the report
does. -/
theorem bedier_threshold {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsSystem r T) (hTne : T.Nonempty) {L : ℕ} (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (m : Finset (Fin n) → ℝ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (hmnn : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1) (hzero : ∀ σ, m σ = 0 → ∀ u ω, Y σ u ω = 0)
    {a b c : ℝ} (ha0 : 0 ≤ a) (hac : a < c) (hcb : c < b)
    (htrue : ∀ σ ∈ T, b ≤ m σ) (hfalse : ∀ τ, Splits.IsSide r τ → τ ∉ T → m τ ≤ a) :
    μ.real {ω | ¬ RestrictedUnique r (fun σ => ∑ u, Y σ u ω) (c * L) T} ≤
      ∑ σ ∈ T, exp (-(L * kl c (m σ))) + ∑ τ ∈ falseOcc r T m, exp (-(L * kl c (m τ))) := by
  have hc0 : 0 < c := lt_of_le_of_lt ha0 hac
  have hc1 : c < 1 := by obtain ⟨σ, hσ⟩ := hTne; linarith [htrue σ hσ, hm1 σ]
  refine (threshold_union r T hT hTne Y hb m hmnn hzero hc0.le).trans
    (add_le_add (sum_le_sum fun σ hσ => ?_) (sum_le_sum fun τ hτ => ?_))
  · have hcm : c < m σ := hcb.trans_le (htrue σ hσ)
    rcases (hm1 σ).lt_or_eq with h1 | h1
    · exact true_tail_kl (Y σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) hc0 hcm h1
    · -- `m σ = 1`: the Lean value `kl c 1 = c log c ≤ 0` makes the term at least `1`
      refine measureReal_le_one.trans (Real.one_le_exp ?_)
      have : kl c (m σ) = c * Real.log c := by simp [kl, h1]
      rw [this]
      have : c * Real.log c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc0.le (Real.log_nonpos hc0.le (by linarith))
      have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
  · simp only [falseOcc, mem_filter, mem_univ, true_and] at hτ
    obtain ⟨hτs, hτT, hm⟩ := hτ
    exact false_tail_kl (Y τ) (hmeas τ) (hb τ) (hind τ) (hmean τ) hm
      ((hfalse τ hτs hτT).trans_lt hac) hc1

/-- **Theorem 8.2 (`thm:bedier`), Kullback–Leibler form with the report's convention for rate
`1`.**  Under the hypotheses of `bedier_threshold`, with `L ≥ 1`, the failure probability is at
most `∑_{σ ∈ T, m σ < 1} exp(-L KL(c ‖ m σ)) + ∑_{τ ∈ F} exp(-L KL(c ‖ m τ))`: a true split of rate
`1` contributes nothing (`KL(c ‖ 1) = ∞`, its term is `0`; `true_tail_one`). -/
theorem bedier_threshold_kl {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsSystem r T) (hTne : T.Nonempty) {L : ℕ} (hL : 0 < L)
    (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (m : Finset (Fin n) → ℝ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (hmnn : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1) (hzero : ∀ σ, m σ = 0 → ∀ u ω, Y σ u ω = 0)
    {a b c : ℝ} (ha0 : 0 ≤ a) (hac : a < c) (hcb : c < b)
    (htrue : ∀ σ ∈ T, b ≤ m σ) (hfalse : ∀ τ, Splits.IsSide r τ → τ ∉ T → m τ ≤ a) :
    μ.real {ω | ¬ RestrictedUnique r (fun σ => ∑ u, Y σ u ω) (c * L) T} ≤
      ∑ σ ∈ T.filter (fun σ => m σ < 1), exp (-(L * kl c (m σ))) +
        ∑ τ ∈ falseOcc r T m, exp (-(L * kl c (m τ))) := by
  have hc0 : 0 < c := lt_of_le_of_lt ha0 hac
  have hc1 : c < 1 := by obtain ⟨σ, hσ⟩ := hTne; linarith [htrue σ hσ, hm1 σ]
  refine (threshold_union r T hT hTne Y hb m hmnn hzero hc0.le).trans
    (add_le_add ?_ (sum_le_sum fun τ hτ => ?_))
  · rw [← sum_filter_add_sum_filter_not T (fun σ => m σ < 1)]
    have h1 : ∑ σ ∈ T.filter (fun σ => m σ < 1), μ.real {ω | ∑ u, Y σ u ω ≤ c * L} ≤
        ∑ σ ∈ T.filter (fun σ => m σ < 1), exp (-(L * kl c (m σ))) :=
      sum_le_sum fun σ hσ => by
        obtain ⟨hσT, h⟩ := mem_filter.mp hσ
        exact true_tail_kl (Y σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) hc0
          (hcb.trans_le (htrue σ hσT)) h
    have h2 : ∑ σ ∈ T.filter (fun σ => ¬ m σ < 1), μ.real {ω | ∑ u, Y σ u ω ≤ c * L} ≤ 0 :=
      sum_nonpos fun σ hσ => by
        obtain ⟨-, h⟩ := mem_filter.mp hσ
        have h1 : m σ = 1 := le_antisymm (hm1 σ) (not_lt.mp h)
        exact true_tail_one hL (Y σ) (hmeas σ) (hb σ) (hind σ)
          (fun u => (hmean σ u).trans h1) hc1
    linarith
  · simp only [falseOcc, mem_filter, mem_univ, true_and] at hτ
    obtain ⟨hτs, hτT, hm⟩ := hτ
    exact false_tail_kl (Y τ) (hmeas τ) (hb τ) (hind τ) (hmean τ) hm
      ((hfalse τ hτs hτT).trans_lt hac) hc1

/-- **Theorem 8.2 (`thm:bedier`), simplified form.**  With `c = ((√a + √b)/2)²` and the
hypotheses of `bedier_threshold` (here `a < b` only), the probability of failure is at most
`(|T| + K) exp(-L (√b - √a)² / 4)`, `K = |F|` the number of false splits that occur. -/
theorem bedier_threshold_simple {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsSystem r T) (hTne : T.Nonempty) {L : ℕ} (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (m : Finset (Fin n) → ℝ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (hmnn : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1) (hzero : ∀ σ, m σ = 0 → ∀ u ω, Y σ u ω = 0)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (htrue : ∀ σ ∈ T, b ≤ m σ) (hfalse : ∀ τ, Splits.IsSide r τ → τ ∉ T → m τ ≤ a) :
    μ.real {ω | ¬ RestrictedUnique r (fun σ => ∑ u, Y σ u ω) (((√a + √b) / 2) ^ 2 * L) T} ≤
      (T.card + (falseOcc r T m).card) * exp (-(L * (√b - √a) ^ 2 / 4)) := by
  set c := ((√a + √b) / 2) ^ 2
  have hsa : 0 ≤ √a := Real.sqrt_nonneg a
  have hsab : √a < √b := Real.sqrt_lt_sqrt ha0 hab
  have hsc : √c = (√a + √b) / 2 := Real.sqrt_sq (by linarith)
  have hac : a < c := by
    have : √a < √c := by rw [hsc]; linarith
    exact (Real.sqrt_lt_sqrt_iff ha0).mp this
  have hcb : c < b := by
    have : √c < √b := by rw [hsc]; linarith
    exact (Real.sqrt_lt_sqrt_iff (by positivity)).mp this
  have hc0 : 0 < c := lt_of_le_of_lt ha0 hac
  have hc1 : c < 1 := by obtain ⟨σ, hσ⟩ := hTne; linarith [htrue σ hσ, hm1 σ]
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set e := exp (-(L * (√b - √a) ^ 2 / 4))
  have hkey : ∀ x : ℝ, ((√b - √a) / 2) ^ 2 ≤ x → exp (-(L * x)) ≤ e := by
    intro x hx; apply Real.exp_le_exp.mpr; nlinarith
  refine (threshold_union r T hT hTne Y hb m hmnn hzero hc0.le).trans ?_
  have hsum : (T.card + (falseOcc r T m).card : ℝ) * e =
      ∑ _σ ∈ T, e + ∑ _τ ∈ falseOcc r T m, e := by simp; ring
  rw [hsum]
  refine add_le_add (sum_le_sum fun σ hσ => ?_) (sum_le_sum fun τ hτ => ?_)
  · have hbm := htrue σ hσ
    have hcm : c < m σ := hcb.trans_le hbm
    rcases (hm1 σ).lt_or_eq with h1 | h1
    · refine (true_tail_kl (Y σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) hc0 hcm h1).trans
        (hkey _ ((?_ : _ ≤ (√c - √(m σ)) ^ 2).trans
          (kl_ge_sq hc0 (hcm.trans h1) (hc0.trans hcm) h1)))
      have : √b ≤ √(m σ) := Real.sqrt_le_sqrt hbm
      rw [hsc]; nlinarith
    · rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · subst hL0; simp [e, measureReal_le_one]
      · exact (true_tail_one hLpos (Y σ) (hmeas σ) (hb σ) (hind σ)
          (fun u => (hmean σ u).trans h1) (by linarith [hcb, hm1 σ])).trans (exp_pos _).le
  · simp only [falseOcc, mem_filter, mem_univ, true_and] at hτ
    obtain ⟨hτs, hτT, hm⟩ := hτ
    have hma := hfalse τ hτs hτT
    have hmc : m τ < c := hma.trans_lt hac
    refine (false_tail_kl (Y τ) (hmeas τ) (hb τ) (hind τ) (hmean τ) hm hmc
      hc1).trans (hkey _ ((?_ : _ ≤ (√c - √(m τ)) ^ 2).trans
        (kl_ge_sq hc0 hc1 hm (by linarith))))
    have : √(m τ) ≤ √a := Real.sqrt_le_sqrt hma
    rw [hsc]; nlinarith

end Stemma.Chernoff
