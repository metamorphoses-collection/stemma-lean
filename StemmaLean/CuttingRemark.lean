/-
The closing remark of the proof of Theorem 7.14(b) of the technical report
(`thm:cuttingconsistency`), on splits with `m_σ = 0`.

* `displayed_without_proposal`: a unique maximum does not imply that every split of `T` is ever
  observed on all witnesses; a split may be displayed through the restriction of another proposal.
  On five witnesses, the proposal `{0,1,2}` with witness `2` illegible records the partial split
  `01 | 34`, which the split `{0,1}` displays although it was not proposed.
* `observed_in_full`: if `m_σ > 0` and `δ < 1`, with i.i.d. units following the illegibility model,
  almost surely some unit eventually proposes `σ` with every witness legible: each split of `T` is
  eventually observed in full (`all_observed_in_full`).
-/
import Mathlib
import StemmaLean.FragmentaryUnits

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped Classical ENNReal

namespace Stemma.CuttingRemark

open Stemma.Splits Stemma.Cutting Stemma.Fragmentary Stemma.CuttingIllegible
  Stemma.FragmentaryUnits

/-- **Theorem 7.14(b), closing remark (first part).**  A split can be displayed without being
proposed: on five witnesses, with reference witness `4`, the sides `σ = {0,1}` and
`σ' = {0,1,2}` are distinct non-trivial splits; on the legible witnesses `O = {0,1,3,4}` the
proposal `σ'` is non-trivial and its recorded partial split is displayed by `{σ}`.  So a unit
that proposes only `σ'` adds weight to every stemma containing `σ`, even if `m_σ = 0`. -/
theorem displayed_without_proposal :
    let σ : Finset (Fin 5) := {0, 1}
    let σ' : Finset (Fin 5) := {0, 1, 2}
    let O : Finset (Fin 5) := {0, 1, 3, 4}
    IsSide 4 σ ∧ IsSide 4 σ' ∧ σ ≠ σ' ∧ NontrivOn O σ' ∧ Displays {σ} (canon O σ') := by
  intro σ σ' O
  refine ⟨by unfold IsSide Nontriv; decide, by unfold IsSide Nontriv; decide, by decide,
    by unfold NontrivOn; decide, ?_⟩
  rw [displays_canon (by decide)]
  exact ⟨σ, mem_singleton_self _, by unfold SameRestr; decide⟩

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : ℕ → Finset (Fin n) → Ω → ℝ} {I : ℕ → Fin n → Ω → ℝ}

/-- Unit `u` proposes `σ` with every witness legible. -/
def Full (Z : ℕ → Finset (Fin n) → Ω → ℝ) (I : ℕ → Fin n → Ω → ℝ) (σ : Finset (Fin n))
    (u : ℕ) : Set Ω :=
  {ω | Z u σ ω = 1 ∧ ∀ x, I u x ω = 0}

/-- The same event as a set of unit data. -/
def fullSet (σ : Finset (Fin n)) : Set (UnitData n) := {v | v.1 σ = 1 ∧ ∀ x, v.2 x = 0}

lemma measurableSet_fullSet (σ : Finset (Fin n)) : MeasurableSet (fullSet σ) := by
  unfold fullSet
  refine MeasurableSet.inter (s₁ := {v : UnitData n | v.1 σ = 1}) (s₂ := {v | ∀ x, v.2 x = 0}) ?_ ?_
  · exact measurableSet_eq_fun ((measurable_pi_apply σ).comp measurable_fst) measurable_const
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x =>
      measurableSet_eq_fun ((measurable_pi_apply x).comp measurable_snd) measurable_const

lemma full_eq (σ : Finset (Fin n)) (u : ℕ) : Full Z I σ u = VN Z I u ⁻¹' fullSet σ := rfl

variable (hZ : ∀ u σ, Measurable (Z u σ)) (hIm : ∀ u x, Measurable (I u x))
  (hV : iIndepFun (VN Z I) μ) (hident : ∀ u, IdentDistrib (VN Z I u) (VN Z I 0) μ μ)

include hZ hIm hV hident in
/-- **Theorem 7.14(b), closing remark (second part).**  Let unit `0` follow the illegibility
model (witnesses illegible independently, with probability at most `δ < 1`, independently of the
readings), units i.i.d.  If `m_σ > 0`, almost surely some unit eventually proposes `σ` with every
witness legible. -/
theorem observed_in_full (hI01 : ∀ x ω, I 0 x ω = 0 ∨ I 0 x ω = 1)
    (hindZI : IndepFun (fun ω σ => Z 0 σ ω) (fun ω x => I 0 x ω) μ) (hindI : iIndepFun (I 0) μ)
    {δ : ℝ} (hδ1 : δ < 1) (hδ : ∀ x, μ.real {ω | I 0 x ω = 1} ≤ δ) {σ : Finset (Fin n)}
    (hm : 0 < mC μ (Z 0) σ) :
    ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∃ u < L, ω ∈ Full Z I σ u := by
  -- the probability `q` that one unit observes `σ` in full is positive
  have hq : 0 < μ.real (Full Z I σ 0) := by
    have e : Full Z I σ 0 = {ω | Z 0 σ ω = 1} ∩ {ω | ∀ x ∈ (univ : Finset (Fin n)), I 0 x ω = 0} :=
      by ext ω; simp [Full]
    rw [e, meas_inter_illegible (hZ 0) (hIm 0) hI01 hindZI hindI σ univ 0]
    refine mul_pos hm (prod_pos fun x _ => ?_)
    have hc : {ω | I 0 x ω = 0} = {ω | I 0 x ω = 1}ᶜ := by
      ext ω; rcases hI01 x ω with h | h <;> simp [h]
    rw [hc, measureReal_compl (measurableSet_eq_fun (hIm 0 x) measurable_const)]
    simp only [probReal_univ]
    linarith [hδ x]
  set q := μ (Full Z I σ 0)
  have hq0 : 0 < q := pos_iff_ne_zero.mpr fun h => by
    simp [measureReal_def, q, h] at hq
  -- no unit among the first `L` observes it, with probability `(1 - q)^L`
  have hS := measurableSet_fullSet (n := n) σ
  have hmeasV : ∀ u, Measurable (VN Z I u) := measurable_VN hZ hIm
  have hnone : ∀ L, μ (⋂ u ∈ range L, (Full Z I σ u)ᶜ) = (1 - q) ^ L := by
    intro L
    have h := hV.measure_inter_preimage_eq_mul (range L) (sets := fun _ => (fullSet σ)ᶜ)
      (fun _ _ => hS.compl)
    simp only [full_eq, ← Set.preimage_compl]
    rw [h]
    have hu : ∀ u, μ (VN Z I u ⁻¹' (fullSet σ)ᶜ) = 1 - q := fun u => by
      rw [(hident u).measure_mem_eq hS.compl, Set.preimage_compl,
        prob_compl_eq_one_sub (hS.preimage (hmeasV 0))]
      rfl
    rw [prod_congr rfl fun u _ => hu u, prod_const, card_range]
  have hlim : Tendsto (fun L => (1 - q) ^ L) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne')
  have hzero : μ (⋂ u, (Full Z I σ u)ᶜ) = 0 := by
    refine le_antisymm (ge_of_tendsto' hlim fun L => ?_) zero_le
    rw [← hnone L]
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_iInter] at hω ⊢
    exact fun u _ => hω u
  have hae : ∀ᵐ ω ∂μ, ∃ u, ω ∈ Full Z I σ u := by
    rw [ae_iff]
    convert hzero using 2
    ext ω; simp
  filter_upwards [hae] with ω ⟨u, hu⟩
  exact eventually_atTop.mpr ⟨u + 1, fun L hL => ⟨u, by omega, hu⟩⟩

include hZ hIm hV hident in
/-- **Theorem 7.14(b), closing remark.**  If every split of `T` has `m_σ > 0` and `δ < 1`, almost
surely each split of `T` is eventually observed in full. -/
theorem all_observed_in_full (hI01 : ∀ x ω, I 0 x ω = 0 ∨ I 0 x ω = 1)
    (hindZI : IndepFun (fun ω σ => Z 0 σ ω) (fun ω x => I 0 x ω) μ) (hindI : iIndepFun (I 0) μ)
    {δ : ℝ} (hδ1 : δ < 1) (hδ : ∀ x, μ.real {ω | I 0 x ω = 1} ≤ δ)
    {T : Finset (Finset (Fin n))} (hm : ∀ σ ∈ T, 0 < mC μ (Z 0) σ) :
    ∀ᵐ ω ∂μ, ∀ σ ∈ T, ∀ᶠ L in atTop, ∃ u < L, ω ∈ Full Z I σ u := by
  have h : ∀ σ : T, ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∃ u < L, ω ∈ Full Z I σ.1 u := fun σ =>
    observed_in_full hZ hIm hV hident hI01 hindZI hindI hδ1 hδ (hm σ.1 σ.2)
  filter_upwards [ae_all_iff.mpr h] with ω hω σ hσ
  exact hω ⟨σ, hσ⟩

end Stemma.CuttingRemark
