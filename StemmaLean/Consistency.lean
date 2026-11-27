/-
Consistency of the best-supported stemma (Theorem 2.7(a) of the mathematical paper, Hoeffding form;
Theorem 7.4 of the technical report), and the probability in the Bédier effect.

The combinatorial input is the matching property of a binary true stemma (Lemma 6.1 of the
technical report): for every compatible split set `S ≠ T`, `T \ S` is non-empty and
`|S \ T| ≤ |T \ S|`.  It is proved in `Splits.lean` (`displacement_matching`), and
`consistency` below uses it, with no matching hypothesis.  The general form
`consistency_of_matching` keeps the matching property as a hypothesis, for any family system that
has it.  The margin `γ` enters through its defining inequality.  Concentration is Mathlib's
Hoeffding inequality.
-/
import Mathlib
import StemmaLean.Splits

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Stemma.Consistency

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Counting core -/

/-- **Counting core.** If every observed (normalised) support lies within `γ/2` of its expectation,
the true family set is strictly heavier than every other compatible family set. -/
theorem counting_core (Compat : Finset ι → Prop) (T : Finset ι) (m w : ι → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hmatch : ∀ S, Compat S → S ≠ T → (T \ S).Nonempty ∧ (S \ T).card ≤ (T \ S).card)
    (hgap : ∀ S, Compat S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    (hdev : ∀ σ, |w σ - m σ| < γ / 2) :
    ∀ S, Compat S → S ≠ T → ∑ σ ∈ S, w σ < ∑ σ ∈ T, w σ := by
  intro S hS hne
  obtain ⟨hA, hcard⟩ := hmatch S hS hne
  have hg := hgap S hS hne
  have key := Finset.sum_sdiff_sub_sum_sdiff (s₁ := S) (s₂ := T) (f := w)
  -- lower bound on the true families outside `S`
  have hlow : ∑ σ ∈ T \ S, (m σ - γ / 2) < ∑ σ ∈ T \ S, w σ :=
    Finset.sum_lt_sum_of_nonempty hA fun σ _ => by
      have := hdev σ; rw [abs_lt] at this; linarith
  -- upper bound on the false families of `S`
  have hup : ∑ σ ∈ S \ T, w σ ≤ ∑ σ ∈ S \ T, (m σ + γ / 2) :=
    Finset.sum_le_sum fun σ _ => by
      have := hdev σ; rw [abs_lt] at this; linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlow
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hup
  have hc : ((S \ T).card : ℝ) ≤ (T \ S).card := by exact_mod_cast hcard
  nlinarith

/-! ### Hoeffding bound for one family -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One-sided Hoeffding bound for the mean of `L` independent `[0,1]`-valued variables. -/
lemma upper_tail {L : ℕ} (hL : 0 < L) (Y : Fin L → Ω → ℝ) (m : ℝ)
    (hmeas : ∀ u, Measurable (Y u)) (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (hmean : ∀ u, μ[Y u] = m) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ u, Y u ω) / L - m} ≤ exp (-2 * L * t ^ 2) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : ∀ u ∈ (Finset.univ : Finset (Fin L)),
      HasSubgaussianMGF (fun ω => Y u ω - m) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro u _
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := Y u) (hmeas u).aemeasurable
      (ae_of_all _ (hb u))
    simpa [hmean u] using this
  have hind' : iIndepFun (fun u ω => Y u ω - m) μ :=
    hind.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have H := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub (ε := L * t) (by positivity)
  have hset : {ω | t ≤ (∑ u, Y u ω) / L - m} = {ω | L * t ≤ ∑ u, (Y u ω - m)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [le_sub_iff_add_le, le_div_iff₀ hLpos]
    constructor <;> intro h <;> nlinarith
  rw [hset]
  refine H.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  field_simp
  ring

/-- Two-sided Hoeffding bound. -/
lemma two_tail {L : ℕ} (hL : 0 < L) (Y : Fin L → Ω → ℝ) (m : ℝ)
    (hmeas : ∀ u, Measurable (Y u)) (hb : ∀ u ω, Y u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (hmean : ∀ u, μ[Y u] = m) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ u, Y u ω) / L - m|} ≤ 2 * exp (-2 * L * t ^ 2) := by
  -- the reflected variables `1 - Y` have mean `1 - m`
  have h1 := upper_tail hL Y m hmeas hb hind hmean ht
  have h2 := upper_tail (μ := μ) hL (fun u ω => 1 - Y u ω) (1 - m)
    (fun u => measurable_const.sub (hmeas u))
    (fun u ω => by have := hb u ω; constructor <;> linarith [this.1, this.2])
    (hind.comp (fun _ x => 1 - x) (fun _ => measurable_const.sub measurable_id))
    (fun u => by
      rw [integral_sub (integrable_const _) (Integrable.of_mem_Icc 0 1 (hmeas u).aemeasurable
        (ae_of_all _ (hb u))), hmean u]; simp) ht
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsplit : {ω | t ≤ |(∑ u, Y u ω) / L - m|} ⊆
      {ω | t ≤ (∑ u, Y u ω) / L - m} ∪ {ω | t ≤ (∑ u, (1 - Y u ω)) / L - (1 - m)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e : (∑ u, (1 - Y u ω)) / L - (1 - m) = -((∑ u, Y u ω) / L - m) := by
      rw [Finset.sum_sub_distrib]; simp; field_simp; ring
    rw [e]
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; exact h
  calc μ.real {ω | t ≤ |(∑ u, Y u ω) / L - m|}
      ≤ μ.real ({ω | t ≤ (∑ u, Y u ω) / L - m} ∪ {ω | t ≤ (∑ u, (1 - Y u ω)) / L - (1 - m)}) :=
        measureReal_mono hsplit (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ exp (-2 * L * t ^ 2) + exp (-2 * L * t ^ 2) := add_le_add h1 h2
    _ = 2 * exp (-2 * L * t ^ 2) := by ring

/-! ### Consistency bound -/

/-- Consistency (Hoeffding form) for any family system with the matching property, which is
taken as the hypothesis `hmatch`; `consistency` below discharges it for binary stemmata.  Units
are `L` independent draws; `Y σ u` indicates that unit `u` proposes family `σ`, with
expectation `m σ`.  Families outside `R` are never proposed and have `m σ = 0`.  If `γ > 0` satisfies the margin inequality and the matching property holds, the
probability that some other compatible family set is at least as heavy as the true one is at most
`2 |R| exp(-L γ² / 2)`. -/
theorem consistency_of_matching (Compat : Finset ι → Prop) (T : Finset ι) (m : ι → ℝ) (γ : ℝ)
    (hγ : 0 < γ)
    (hmatch : ∀ S, Compat S → S ≠ T → (T \ S).Nonempty ∧ (S \ T).card ≤ (T \ S).card)
    (hgap : ∀ S, Compat S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : ι → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset ι) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, Compat S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      2 * R.card * exp (-L * γ ^ 2 / 2) := by
  set A : ι → Set Ω := fun σ => {ω | γ / 2 ≤ |(∑ u, Y σ u ω) / L - m σ|}
  have hsub : {ω | ∃ S, Compat S ∧ S ≠ T ∧
      ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ⊆ ⋃ σ ∈ R, A σ := by
    intro ω hω
    obtain ⟨S, hS, hne, hle⟩ := hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, A, Set.mem_setOf_eq, not_le] at hnot
    have hdev : ∀ σ, |(∑ u, Y σ u ω) / L - m σ| < γ / 2 := by
      intro σ
      by_cases hσ : σ ∈ R
      · exact hnot σ hσ
      · simp [hR σ hσ, hmR σ hσ]; linarith
    have := counting_core Compat T m (fun σ => (∑ u, Y σ u ω) / L) γ hγ.le hmatch hgap hdev S hS hne
    linarith
  calc _ ≤ μ.real (⋃ σ ∈ R, A σ) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ σ ∈ R, μ.real (A σ) := measureReal_biUnion_finset_le R A
    _ ≤ ∑ σ ∈ R, 2 * exp (-2 * L * (γ / 2) ^ 2) :=
        Finset.sum_le_sum fun σ _ =>
          two_tail hL (Y σ) (m σ) (hmeas σ) (hb σ) (hind σ) (hmean σ) (by positivity)
    _ = 2 * R.card * exp (-L * γ ^ 2 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring_nf

/-- **Theorem 7.4(a) (`thm:consistency`), Hoeffding form.**  Let `T` be (the split system of) a
binary stemma on `n` witnesses, each split recorded by its side away from `r` (`Splits.lean`).
Units are `L` independent draws; `Y σ u ∈ [0,1]` indicates that unit `u` proposes split `σ`, with
expectation `m σ`; splits outside `R` are never proposed and have `m σ = 0`.  If `γ > 0` satisfies
the margin inequality of Definition 7.2 (`γ |T \ S| ≤ m(T \ S) - m(S \ T)` for every compatible
`S ≠ T`), the probability that some other compatible set of non-trivial splits is at least as heavy
as `T` is at most `2 |R| exp(-L γ² / 2)`.  The matching property is Lemma 6.1, proved.  With
`R = T ∪ F`, `|R| ≤ n - 3 + K`, the report's bound.  Bernstein's form is not formalised. -/
theorem consistency {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n))) (hT : Splits.IsBinary r T)
    (m : Finset (Fin n) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ S, Splits.IsSystem r S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, Splits.IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      2 * R.card * exp (-L * γ ^ 2 / 2) :=
  consistency_of_matching (Splits.IsSystem r) T m γ hγ
    (fun S hS hne => by
      obtain ⟨h1, h2, -⟩ := Splits.displacement_matching hT hS hne
      exact ⟨h1, h2⟩)
    hgap hL Y hmeas hb hind hmean R hR hmR

/-! ### The probability in the Bédier effect -/

/-- **Bédier effect, probability.**  Let `E u` be the event that unit `u` proposes a family that
would resolve a polytomy, with probability `m`, independently across the `L` units.  The true
(unresolved) stemma can be selected only if no unit proposes it, an event of probability
`(1 - m)^L`. -/
theorem bedier_probability {L : ℕ} (E : Fin L → Set Ω) (hmeasE : ∀ u, MeasurableSet (E u))
    (hind : iIndepSet (fun u => (E u)ᶜ) μ) (m : ℝ) (hm : ∀ u, μ.real (E u) = m) :
    μ.real (⋂ u, (E u)ᶜ) = (1 - m) ^ L := by
  have h := hind.meas_biInter (Finset.univ : Finset (Fin L))
  simp only [Finset.mem_univ, Set.iInter_true] at h
  rw [measureReal_def, h, ENNReal.toReal_prod]
  have hc : ∀ u, (μ (E u)ᶜ).toReal = 1 - m := fun u => by
    rw [← measureReal_def, measureReal_compl (hmeasE u), hm u, probReal_univ]
  simp [hc]

end Stemma.Consistency
