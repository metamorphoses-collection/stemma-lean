/-
Clopper–Pearson bounds and their coverage, and Theorem 7.9 of the technical report
(`thm:gammaconf`) without the coverage hypothesis.

* `binomial_law`: the support `w(s)` of a split, the number of units among `L` independent
  `{0,1}` indicators of mean `m` that propose it, is binomial: `P(w = k) = C(L,k) m^k (1-m)^(L-k)`.
* `cpUpper L β k = sup {p ∈ [0,1] | P_p(X ≤ k) ≥ β}` and
  `cpLower L β k = inf {p ∈ [0,1] | P_p(X ≥ k) ≥ β}` are the one-sided Clopper–Pearson bounds at
  level `β`, for `X` binomial with parameters `L` and `p`.
* `cpUpper_coverage`, `cpLower_coverage`: `P_p(cpUpper(X) < p) ≤ β` and `P_p(cpLower(X) > p) ≤ β`
  for every `p ∈ [0,1]` and `β ≤ 1`.  The argument is elementary: if the upper bound at `k` is
  below `p`, then `P_p(X ≤ k) < β` by the definition of the supremum, and the event is contained
  in `{X ≤ k*}` for the largest such `k*`; symmetrically for the lower bound.
* `gamma_confidence_cp`: Theorem 7.9 for i.i.d. units, with the Clopper–Pearson bounds at level
  `δ / (2N)` computed from the observed supports.

Mathlib has neither the binomial law of a sum of independent Bernoulli variables nor the
Clopper–Pearson bounds; both are proved here with finite sums.
-/
import Mathlib
import StemmaLean.GammaConf

open MeasureTheory ProbabilityTheory Finset
open scoped Classical

namespace Stemma.ClopperPearson

/-- `P_p(X ≤ k)` for `X` binomial with parameters `L`, `p`. -/
noncomputable def cdf (L k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ range (k + 1), (L.choose i : ℝ) * p ^ i * (1 - p) ^ (L - i)

/-- `P_p(X ≥ k)`. -/
noncomputable def tail (L k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Ico k (L + 1), (L.choose i : ℝ) * p ^ i * (1 - p) ^ (L - i)

/-- The one-sided Clopper–Pearson upper bound at level `β`. -/
noncomputable def cpUpper (L : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  sSup {p | p ∈ Set.Icc (0 : ℝ) 1 ∧ β ≤ cdf L k p}

/-- The one-sided Clopper–Pearson lower bound at level `β`. -/
noncomputable def cpLower (L : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  sInf {p | p ∈ Set.Icc (0 : ℝ) 1 ∧ β ≤ tail L k p}

lemma binom_total (L : ℕ) (p : ℝ) :
    ∑ i ∈ range (L + 1), (L.choose i : ℝ) * p ^ i * (1 - p) ^ (L - i) = 1 := by
  calc ∑ i ∈ range (L + 1), (L.choose i : ℝ) * p ^ i * (1 - p) ^ (L - i)
      = ∑ i ∈ range (L + 1), p ^ i * (1 - p) ^ (L - i) * (L.choose i : ℝ) :=
        sum_congr rfl fun i _ => by ring
    _ = (p + (1 - p)) ^ L := (add_pow p (1 - p) L).symm
    _ = 1 := by rw [show p + (1 - p) = 1 by ring, one_pow]

lemma cdf_ge (L k : ℕ) (hk : L ≤ k) (p : ℝ) : cdf L k p = 1 := by
  unfold cdf
  refine Eq.trans ?_ (binom_total L p)
  refine (sum_subset (range_subset_range.mpr (by omega)) fun i hi hi' => ?_).symm
  have : L < i := by simp at hi hi'; omega
  simp [Nat.choose_eq_zero_of_lt this]

lemma tail_zero (L : ℕ) (p : ℝ) : tail L 0 p = 1 := by
  unfold tail; refine Eq.trans ?_ (binom_total L p); rw [range_eq_Ico]

section law

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The binomial law of a support.**  If `L` units propose a split independently, each with
probability `m`, the number `w` of units proposing it is binomial with parameters `L` and `m`. -/
theorem binomial_law {L : ℕ} (Y : Fin L → Ω → ℝ) (hY : ∀ u, Measurable (Y u))
    (h01 : ∀ u ω, Y u ω = 0 ∨ Y u ω = 1) (hind : iIndepFun Y μ) {m : ℝ}
    (hm : ∀ u, μ.real {ω | Y u ω = 1} = m) (k : ℕ) :
    μ.real {ω | (univ.filter fun u => Y u ω = 1).card = k} =
      (L.choose k : ℝ) * m ^ k * (1 - m) ^ (L - k) := by
  set E : Finset (Fin L) → Set Ω := fun S => {ω | univ.filter (fun u => Y u ω = 1) = S}
  have hEm : ∀ S, MeasurableSet (E S) := by
    intro S
    have : E S = ⋂ u, {ω | Y u ω = 1 ↔ u ∈ S} := by
      ext ω; simp [E, Finset.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun u => ?_
    have hm1 : MeasurableSet {ω | Y u ω = 1} := measurableSet_eq_fun (hY u) measurable_const
    by_cases hu : u ∈ S <;> simp only [hu, iff_true, iff_false]
    · exact hm1
    · exact hm1.compl
  -- the probability of one pattern
  have hE : ∀ S : Finset (Fin L), μ.real (E S) = m ^ S.card * (1 - m) ^ (L - S.card) := by
    intro S
    set t : Fin L → Set ℝ := fun u => if u ∈ S then {1} else {1}ᶜ
    have ht : ∀ u ∈ (univ : Finset (Fin L)), MeasurableSet (t u) := fun u _ => by
      simp only [t]; split_ifs
      · exact measurableSet_singleton 1
      · exact (measurableSet_singleton 1).compl
    have h := hind.measure_inter_preimage_eq_mul univ ht
    have heq : (⋂ u ∈ (univ : Finset (Fin L)), Y u ⁻¹' t u) = E S := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, mem_univ, forall_true_left, t, E,
        Finset.ext_iff, mem_filter, true_and, Set.mem_ofPred_eq]
      refine forall_congr' fun u => ?_
      by_cases hu : u ∈ S <;> simp [hu]
    rw [heq] at h
    have hu1 : ∀ u, (μ (Y u ⁻¹' t u)).toReal = if u ∈ S then m else 1 - m := by
      intro u
      by_cases hu : u ∈ S
      · simp only [t, hu, if_true]; rw [← measureReal_def]; exact hm u
      · simp only [t, hu, if_false]
        rw [← measureReal_def, Set.preimage_compl,
          measureReal_compl ((hY u) (measurableSet_singleton 1)), probReal_univ]
        have : Y u ⁻¹' {1} = {ω | Y u ω = 1} := rfl
        rw [this, hm u]
    rw [measureReal_def, h, ENNReal.toReal_prod]
    simp only [hu1]
    rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter]
    congr
    rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ S),
      card_univ, Fintype.card_fin]
  have hunion : {ω | (univ.filter fun u => Y u ω = 1).card = k} =
      ⋃ S ∈ (univ : Finset (Fin L)).powersetCard k, E S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_powersetCard, E, exists_prop]
    constructor
    · intro h; exact ⟨_, ⟨subset_univ _, h⟩, rfl⟩
    · rintro ⟨S, ⟨-, hS⟩, rfl⟩; exact hS
  rw [hunion, measureReal_biUnion_finset _ (fun S _ => hEm S)]
  · rw [sum_congr rfl fun S hS => by rw [hE S, (mem_powersetCard.mp hS).2], sum_const,
      card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro S _ S' _ hSS'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact hSS' (h1.symm.trans h2)

end law

/-! ### Coverage -/

section coverage

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {L : ℕ} {X : Ω → ℕ} (hX : Measurable X) {p : ℝ}
  (hbin : ∀ k, μ.real {ω | X ω = k} = (L.choose k : ℝ) * p ^ k * (1 - p) ^ (L - k))
include hX hbin

lemma prob_le (k : ℕ) : μ.real {ω | X ω ≤ k} = cdf L k p := by
  have : {ω | X ω ≤ k} = ⋃ i ∈ range (k + 1), {ω | X ω = i} := by
    ext ω; simp [Nat.lt_succ_iff]
  rw [this, measureReal_biUnion_finset (f := fun i => {ω | X ω = i}) _
    (fun i _ => hX (measurableSet_singleton i))]
  · exact sum_congr rfl fun i _ => hbin i
  · intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact hij (h1.symm.trans h2)

lemma prob_ge (k : ℕ) : μ.real {ω | k ≤ X ω} ≤ tail L k p + μ.real {ω | L < X ω} := by
  have : {ω | k ≤ X ω} ⊆ (⋃ i ∈ Ico k (L + 1), {ω | X ω = i}) ∪ {ω | L < X ω} := by
    intro ω hω
    by_cases h : X ω ≤ L
    · left; simp only [Set.mem_iUnion, mem_Ico, exists_prop, Set.mem_ofPred_eq]
      exact ⟨X ω, ⟨hω, by omega⟩, rfl⟩
    · right; simp only [Set.mem_ofPred_eq]; omega
  refine (measureReal_mono this (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
  refine add_le_add ?_ le_rfl
  rw [measureReal_biUnion_finset (f := fun i => {ω | X ω = i}) _
    (fun i _ => hX (measurableSet_singleton i))]
  · exact (sum_congr rfl fun i _ => hbin i).le
  · intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact hij (h1.symm.trans h2)

lemma prob_gt_L : μ.real {ω | L < X ω} = 0 := by
  have h1 := prob_le hX hbin L
  rw [cdf_ge L L le_rfl] at h1
  have hc : {ω | L < X ω} = {ω | X ω ≤ L}ᶜ := by ext ω; simp
  rw [hc, measureReal_compl (measurableSet_le hX measurable_const), h1, probReal_univ, sub_self]

/-- **Coverage of the Clopper–Pearson upper bound.**  `P_p(cpUpper(X) < p) ≤ β`. -/
theorem cpUpper_coverage (hp : p ∈ Set.Icc (0 : ℝ) 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) :
    μ.real {ω | cpUpper L β (X ω) < p} ≤ β := by
  -- at an outcome whose bound is below `p`, `P_p(X ≤ k) < β`
  have key : ∀ k, cpUpper L β k < p → cdf L k p < β := by
    intro k hk
    by_contra h
    push Not at h
    have : p ≤ cpUpper L β k :=
      le_csSup ⟨1, fun x hx => hx.1.2⟩ ⟨hp, h⟩
    linarith
  set A : Finset ℕ := (range L).filter fun k => cpUpper L β k < p
  have hA : ∀ k, cpUpper L β k < p → k ∈ A := by
    intro k hk
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hk⟩
    by_contra h
    have := key k hk
    rw [cdf_ge L k (by simpa using h)] at this
    linarith
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have : {ω | cpUpper L β (X ω) < p} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; have := hA _ h; rw [hAe] at this; exact notMem_empty _ this
    rw [this, measureReal_empty]; exact hβ0
  · set kstar := A.max' hAne
    have hk : cpUpper L β kstar < p := (mem_filter.mp (A.max'_mem hAne)).2
    have hsub : {ω | cpUpper L β (X ω) < p} ⊆ {ω | X ω ≤ kstar} := fun ω hω =>
      A.le_max' _ (hA _ hω)
    calc μ.real {ω | cpUpper L β (X ω) < p} ≤ μ.real {ω | X ω ≤ kstar} :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ = cdf L kstar p := prob_le hX hbin kstar
      _ ≤ β := (key kstar hk).le

/-- **Coverage of the Clopper–Pearson lower bound.**  `P_p(cpLower(X) > p) ≤ β`. -/
theorem cpLower_coverage (hp : p ∈ Set.Icc (0 : ℝ) 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) :
    μ.real {ω | p < cpLower L β (X ω)} ≤ β := by
  have key : ∀ k, p < cpLower L β k → tail L k p < β := by
    intro k hk
    by_contra h
    push Not at h
    have : cpLower L β k ≤ p := csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hp, h⟩
    linarith
  by_cases hex : ∃ k, p < cpLower L β k
  · set kmin := Nat.find hex
    have hk : p < cpLower L β kmin := Nat.find_spec hex
    have hsub : {ω | p < cpLower L β (X ω)} ⊆ {ω | kmin ≤ X ω} := fun ω hω =>
      Nat.find_min' hex hω
    calc μ.real {ω | p < cpLower L β (X ω)} ≤ μ.real {ω | kmin ≤ X ω} :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ tail L kmin p + μ.real {ω | L < X ω} := prob_ge hX hbin kmin
      _ = tail L kmin p := by rw [prob_gt_L hX hbin, add_zero]
      _ ≤ β := (key kmin hk).le
  · push Not at hex
    have : {ω | p < cpLower L β (X ω)} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hex _
    rw [this, measureReal_empty]; exact hβ0

end coverage

/-! ### Theorem 7.9 with the Clopper–Pearson bounds -/

section margin

open Stemma.Splits Stemma.Margin Stemma.GammaConf

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The observed support of `s`: the number of units proposing it. -/
noncomputable def supp {L : ℕ} (Y : Finset (Fin n) → Fin L → Ω → ℝ) (s : Finset (Fin n))
    (ω : Ω) : ℕ :=
  (univ.filter fun u => Y s u ω = 1).card

lemma measurable_supp {L : ℕ} {Y : Finset (Fin n) → Fin L → Ω → ℝ}
    (hY : ∀ s u, Measurable (Y s u)) (s : Finset (Fin n)) : Measurable (supp Y s) := by
  have : supp Y s = fun ω => ∑ u, if Y s u ω = 1 then 1 else 0 := by
    funext ω; unfold supp; rw [card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun u _ =>
    Measurable.ite (measurableSet_eq_fun (hY s u) measurable_const) measurable_const
      measurable_const

/-- **Theorem 7.9 (`thm:gammaconf`), with the Clopper–Pearson bounds.**  Let the `L ≥ 1` units be
independent for each split, `Y s u ∈ {0,1}` indicating that unit `u` proposes `s`, with
probability `m s`.  With `ℓ s` and `u s` the one-sided Clopper–Pearson bounds at level
`δ / (2N)` computed from the observed support of `s`, (i) with probability at least `1 - δ`,
`γ(T) ≥ γ_lo(T)` for every binary stemma `T` simultaneously, and (ii) a false certificate has
probability at most `δ`. -/
theorem gamma_confidence_cp (r : Fin n) {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hY : ∀ s u, Measurable (Y s u)) (h01 : ∀ s u ω, Y s u ω = 0 ∨ Y s u ω = 1)
    (hind : ∀ s, iIndepFun (Y s) μ) (m : Finset (Fin n) → ℝ)
    (hm : ∀ s u, μ.real {ω | Y s u ω = 1} = m s) {δ : ℝ} (hδ : 0 ≤ δ) :
    let β := δ / (2 * (sides r).card)
    μ.real {ω | ¬ ∀ T (hT : IsBinary r T) (hTne : T.Nonempty),
        loMargin r (fun s => cpLower L β (supp Y s ω)) (fun s => cpUpper L β (supp Y s ω)) T hTne
          ≤ margin r m T hTne} ≤ δ ∧
    μ.real {ω | ∃ T, ∃ (_ : IsBinary r T) (hTne : T.Nonempty),
        0 < loMargin r (fun s => cpLower L β (supp Y s ω)) (fun s => cpUpper L β (supp Y s ω))
          T hTne ∧ ¬ ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T} ≤ δ := by
  intro β
  by_cases hδ1 : 1 < δ
  · exact ⟨measureReal_le_one.trans hδ1.le, measureReal_le_one.trans hδ1.le⟩
  push Not at hδ1
  have hβ0 : 0 ≤ β := div_nonneg hδ (by positivity)
  have hβ1 : β ≤ 1 := by
    rcases Nat.eq_zero_or_pos (sides r).card with h | h
    · show δ / (2 * ((sides r).card : ℝ)) ≤ 1
      rw [h, Nat.cast_zero, mul_zero, div_zero]; exact zero_le_one
    · have : (1 : ℝ) ≤ 2 * (sides r).card := by
        have : (1 : ℝ) ≤ (sides r).card := by exact_mod_cast h
        linarith
      calc β ≤ δ := div_le_self hδ this
        _ ≤ 1 := hδ1
  have hm01 : ∀ s, m s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    have := hm s ⟨0, hL⟩
    exact ⟨this ▸ measureReal_nonneg, this ▸ measureReal_le_one⟩
  have hbin : ∀ s k, μ.real {ω | supp Y s ω = k} =
      (L.choose k : ℝ) * m s ^ k * (1 - m s) ^ (L - k) := fun s k =>
    binomial_law (Y s) (hY s) (h01 s) (hind s) (hm s) k
  exact gamma_confidence r m (fun s ω => cpLower L β (supp Y s ω))
    (fun s ω => cpUpper L β (supp Y s ω)) hδ
    (fun s _ => cpLower_coverage (measurable_supp hY s) (hbin s) (hm01 s) hβ0 hβ1)
    (fun s _ => cpUpper_coverage (measurable_supp hY s) (hbin s) (hm01 s) hβ0 hβ1)

end margin

end Stemma.ClopperPearson
