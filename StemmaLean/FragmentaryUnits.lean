/-
Fragmentary witnesses, many units: Theorem 7.12(a) and (c) of the technical report
(`thm:fragmentary`), with the model of many units built rather than assumed.

Each of the `L` units `u` has its own complete proposals `Z u σ ∈ {0,1}` and its own illegibility
indicators `I u x ∈ {0,1}`.  The units' data `V u = ((Z u σ)_σ, (I u x)_x)` are independent across
units and identically distributed, and unit `0` follows the one-unit model of `Fragmentary.lean`
(witnesses illegible independently with probability at most `δ`, independently of the readings).
The restriction indicator `Y τ u` says that unit `u` proposes `τ|_{O_u}`; `w̃(τ) = ∑_u Y τ u` is
the restriction-weighted support, and the completion estimator is a maximum-weight compatible set
for `w̃`.

Formalised:
* the `Y τ u` are measurable, `[0,1]`-valued, independent across units for each `τ`, with mean
  `m̃ τ` (`measurable_Y`, `iIndep_Y`, `integral_Y`): these were the assumptions of the one-unit
  formalisation, now consequences of the model;
* (a) Theorem 7.4 for the completion estimator with `m̃`: `fragmentary_consistency` (Hoeffding,
  `2 |R| e^{-L γ̃²/2}` for any `R` outside which nothing is proposed),
  `fragmentary_consistency_bernstein` (Bernstein), and `fragmentary_inconsistency` (6.4(b), an
  infinite i.i.d. sequence of units, from Etemadi's strong law);
* (c) `fragmentary_consistent`: if `m σ - m τ ≥ ρ` on conflicting true/false pairs and
  `δ (4 + 2μ) < ρ`, the margin of `m̃` is positive and the probability that the completion
  estimator misses `T` is at most `2 |sides| e^{-L γ̃²/2}`, `γ̃ > 0` independent of `L`.
-/
import Mathlib
import StemmaLean.CuttingIllegible

open MeasureTheory ProbabilityTheory Finset Real
open scoped Classical

namespace Stemma.FragmentaryUnits

open Stemma.Splits Stemma.Fragmentary Stemma.GammaConf Stemma.Margin Stemma.CuttingIllegible

variable {n : ℕ}

/-- The data of one unit: its complete proposals and its illegibility indicators. -/
abbrev UnitData (n : ℕ) := (Finset (Fin n) → ℝ) × (Fin n → ℝ)

/-- The restriction indicator of `τ`, as a function of a unit's data (`0` off the sides). -/
noncomputable def g (r : Fin n) (τ : Finset (Fin n)) (v : UnitData n) : ℝ :=
  if τ ∈ sides r ∧ ProposesRestr r (fun σ v => v.1 σ) (fun x v => v.2 x) τ v then 1 else 0

lemma proposes_iff {Ω : Type*} {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ}
    {τ : Finset (Fin n)} {ω : Ω} :
    ProposesRestr r Z I τ ω ↔
      NontrivOn (legible I ω) τ ∧ ∃ σ ∈ zs r Z ω, SameRestr (legible I ω) σ τ := by
  unfold ProposesRestr zs
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, σ, hσ, hz, hs⟩; exact ⟨h1, σ, ⟨hσ, hz⟩, hs⟩
  · rintro ⟨h1, σ, ⟨hσ, hz⟩, hs⟩; exact ⟨h1, σ, hσ, hz, hs⟩

lemma measurable_g (r : Fin n) (τ : Finset (Fin n)) : Measurable (g r τ) := by
  intro s _
  have hZ : ∀ σ, Measurable fun v : UnitData n => v.1 σ := fun σ =>
    (measurable_pi_apply σ).comp measurable_fst
  have hI : ∀ x, Measurable fun v : UnitData n => v.2 x := fun x =>
    (measurable_pi_apply x).comp measurable_snd
  have := measurableSet_data (r := r) hZ hI fun F O =>
    (if τ ∈ sides r ∧ (NontrivOn O τ ∧ ∃ σ ∈ F, SameRestr O σ τ) then (1 : ℝ) else 0) ∈ s
  convert this using 1
  ext v
  simp only [Set.mem_preimage, g, Set.mem_ofPred_eq, proposes_iff]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The data of unit `u`. -/
def V {L : ℕ} (Z : Fin L → Finset (Fin n) → Ω → ℝ) (I : Fin L → Fin n → Ω → ℝ) (u : Fin L)
    (ω : Ω) : UnitData n :=
  (fun σ => Z u σ ω, fun x => I u x ω)

/-- Unit `u` proposes the restriction of `τ` (for `τ` a side away from `r`). -/
noncomputable def Y {L : ℕ} (r : Fin n) (Z : Fin L → Finset (Fin n) → Ω → ℝ)
    (I : Fin L → Fin n → Ω → ℝ) (τ : Finset (Fin n)) (u : Fin L) (ω : Ω) : ℝ :=
  g r τ (V Z I u ω)

/-- The expected restriction support `m̃`, of unit `0`, on the sides. -/
noncomputable def mt {L : ℕ} (hL : 0 < L) (μ : Measure Ω) (r : Fin n)
    (Z : Fin L → Finset (Fin n) → Ω → ℝ) (I : Fin L → Fin n → Ω → ℝ) (τ : Finset (Fin n)) : ℝ :=
  if τ ∈ sides r then mR μ r (Z ⟨0, hL⟩) (I ⟨0, hL⟩) τ else 0

section units

variable {L : ℕ} (hL : 0 < L) {r : Fin n} {Z : Fin L → Finset (Fin n) → Ω → ℝ}
  {I : Fin L → Fin n → Ω → ℝ}
  (hZ : ∀ u σ, Measurable (Z u σ)) (hIm : ∀ u x, Measurable (I u x))
  (hV : iIndepFun (V Z I) μ) (hident : ∀ u, IdentDistrib (V Z I u) (V Z I ⟨0, hL⟩) μ μ)

include hZ hIm in
lemma measurable_V (u : Fin L) : Measurable (V Z I u) :=
  (measurable_pi_iff.mpr fun σ => hZ u σ).prodMk (measurable_pi_iff.mpr fun x => hIm u x)

include hZ hIm in
lemma measurable_Y (τ : Finset (Fin n)) (u : Fin L) : Measurable (Y r Z I τ u) :=
  (measurable_g r τ).comp (measurable_V hZ hIm u)

lemma Y_mem (τ : Finset (Fin n)) (u : Fin L) (ω : Ω) : Y r Z I τ u ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold Y g; split_ifs <;> norm_num

include hV in
/-- For each `τ`, the restriction indicators are independent across units. -/
lemma iIndep_Y (τ : Finset (Fin n)) : iIndepFun (Y r Z I τ) μ :=
  hV.comp (fun _ => g r τ) fun _ => measurable_g r τ

include hZ hIm hident in
/-- Each restriction indicator has mean `m̃ τ`. -/
lemma integral_Y (τ : Finset (Fin n)) (u : Fin L) : μ[Y r Z I τ u] = mt hL μ r Z I τ := by
  have h1 : μ[Y r Z I τ u] = μ[Y r Z I τ ⟨0, hL⟩] :=
    ((hident u).comp (measurable_g r τ)).integral_eq
  rw [h1]
  unfold mt
  by_cases hτ : τ ∈ sides r
  · rw [if_pos hτ]
    have hset : MeasurableSet {ω | ProposesRestr r (Z ⟨0, hL⟩) (I ⟨0, hL⟩) τ ω} := by
      have := measurableSet_data (r := r) (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) fun F O =>
        NontrivOn O τ ∧ ∃ σ ∈ F, SameRestr O σ τ
      convert this using 2 with ω
      simp only [Set.mem_ofPred_eq, proposes_iff]
    have : Y r Z I τ ⟨0, hL⟩ =
        Set.indicator {ω | ProposesRestr r (Z ⟨0, hL⟩) (I ⟨0, hL⟩) τ ω} 1 := by
      funext ω
      simp only [Y, g, V, Set.indicator_apply, Pi.one_apply, hτ, true_and]
      rfl
    rw [this, integral_indicator_one hset]; rfl
  · rw [if_neg hτ]
    have : Y r Z I τ ⟨0, hL⟩ = fun _ => 0 := by
      funext ω; simp [Y, g, hτ]
    rw [this, integral_zero]

lemma Y_off {τ : Finset (Fin n)} (hτ : τ ∉ sides r) (u : Fin L) (ω : Ω) : Y r Z I τ u ω = 0 := by
  simp [Y, g, hτ]

lemma mt_off {τ : Finset (Fin n)} (hτ : τ ∉ sides r) : mt hL μ r Z I τ = 0 := by
  simp [mt, hτ]

include hZ hIm hV hident in
/-- **Theorem 7.12(a) (`thm:fragmentary`), Hoeffding form.**  Theorem 7.4(a) holds for the
completion estimator with `m̃` in place of `m`: if `T` is binary and the margin `γ̃` of `m̃` is
positive, and no unit proposes the restriction of a split outside `R` (`m̃ = 0` there), the
probability that some other compatible set has at least the restriction-weighted support of `T` is
at most `2 |R| e^{-L γ̃²/2}`.  With `R = sides r`, the hypotheses on `R` hold
(`fragmentary_consistent`). -/
theorem fragmentary_consistency {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (hγ : 0 < margin r (mt hL μ r Z I) T hTne)
    (R : Finset (Finset (Fin n))) (hR : ∀ τ ∉ R, ∀ u ω, Y r Z I τ u ω = 0)
    (hmR : ∀ τ ∉ R, mt hL μ r Z I τ = 0) :
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y r Z I σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y r Z I σ u ω) / L} ≤
      2 * R.card * exp (-L * margin r (mt hL μ r Z I) T hTne ^ 2 / 2) :=
  Consistency.consistency r T hT (mt hL μ r Z I) _ hγ (margin_gap hT hTne _) hL (Y r Z I)
    (measurable_Y hZ hIm) Y_mem (iIndep_Y hV) (integral_Y hL hZ hIm hident) R hR hmR

include hZ hIm hV hident in
/-- **Theorem 7.12(a) (`thm:fragmentary`), Bernstein form.**  Under the hypotheses of
`fragmentary_consistency`, the failure probability is at most
`∑_{σ ∈ R} 2 exp(-L γ̃² / (8 m̃_σ + 4 γ̃ / 3))`, the first bound of Theorem 7.4(a) with `m̃`. -/
theorem fragmentary_consistency_bernstein {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (hγ : 0 < margin r (mt hL μ r Z I) T hTne)
    (R : Finset (Finset (Fin n))) (hR : ∀ τ ∉ R, ∀ u ω, Y r Z I τ u ω = 0)
    (hmR : ∀ τ ∉ R, mt hL μ r Z I τ = 0) :
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y r Z I σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y r Z I σ u ω) / L} ≤
      ∑ σ ∈ R, 2 * exp (-(L * margin r (mt hL μ r Z I) T hTne ^ 2 /
        (8 * mt hL μ r Z I σ + 4 * margin r (mt hL μ r Z I) T hTne / 3))) :=
  Bernstein.consistency_bernstein r T hT (mt hL μ r Z I) _ hγ (margin_gap hT hTne _) hL (Y r Z I)
    (measurable_Y hZ hIm) Y_mem (iIndep_Y hV) (integral_Y hL hZ hIm hident) R hR hmR

include hZ hIm hV hident in
/-- **Theorem 7.12(c) (`thm:fragmentary`).**  Let unit `0` follow the illegibility model with rate
at most `δ`, let `m` be the complete-data supports and `μ_tot = ∑ m` over the non-trivial splits.
If `m σ - m τ ≥ ρ` whenever a false `τ` and a true `σ` conflict and `δ (4 + 2 μ_tot) < ρ`, the
margin `γ̃` of `m̃` is positive (it does not depend on `L`), and the completion estimator misses `T`
with probability at most `2 |sides| e^{-L γ̃²/2}`: it is consistent. -/
theorem fragmentary_consistent {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) {δ ρ : ℝ}
    (hI01 : ∀ x ω, I ⟨0, hL⟩ x ω = 0 ∨ I ⟨0, hL⟩ x ω = 1)
    (hindZI : IndepFun (fun ω σ => Z ⟨0, hL⟩ σ ω) (fun ω x => I ⟨0, hL⟩ x ω) μ)
    (hindI : iIndepFun (I ⟨0, hL⟩) μ) (hδ : ∀ x, μ.real {ω | I ⟨0, hL⟩ x ω = 1} ≤ δ)
    (hgap : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ →
      ρ ≤ mC μ (Z ⟨0, hL⟩) σ - mC μ (Z ⟨0, hL⟩) τ)
    (hδρ : δ * (4 + 2 * ∑ σ ∈ sides r, mC μ (Z ⟨0, hL⟩) σ) < ρ) :
    0 < margin r (mt hL μ r Z I) T hTne ∧
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y r Z I σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y r Z I σ u ω) / L} ≤
      2 * (sides r).card * exp (-L * margin r (mt hL μ r Z I) T hTne ^ 2 / 2) := by
  set m := mC μ (Z ⟨0, hL⟩)
  set μtot := ∑ σ ∈ sides r, m σ
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  have hm0 : ∀ σ, 0 ≤ m σ := fun σ => measureReal_nonneg
  have hm1 : ∀ σ, m σ ≤ 1 := fun σ => measureReal_le_one
  have hμ0 : 0 ≤ μtot := sum_nonneg fun σ _ => hm0 σ
  -- `δ ≤ 1`: some false split conflicts with a true one, so `ρ ≤ 1`
  have hδ1 : δ ≤ 1 := by
    obtain ⟨σ, hσ⟩ := hTne
    obtain ⟨τ, hτ, hc⟩ := exists_conflict r (hT.1.1 σ hσ).2
    have hτT : τ ∉ T := fun h => hc (hT.1.2 τ h σ hσ (fun e => hc (e ▸ compat_self _)))
    have := hgap τ σ hτ hτT hσ hc
    have := hm1 σ; have := hm0 τ
    nlinarith
  have hside : ∀ {A}, IsSide r A → A ∈ sides r := fun h => mem_filter.mpr ⟨mem_univ _, h⟩
  have hpos := (fragmentary_margin_pos hT hTne m (mt hL μ r Z I) hm0 hm1
    (fun σ => by unfold mt; split_ifs <;> first | exact measureReal_nonneg | exact le_rfl)
    hδ0 (fun σ hσ => by
      rw [mt, if_pos (hside (hT.1.1 σ hσ))]
      exact restr_lower (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) hI01 hindZI hindI (hside (hT.1.1 σ hσ)) hδ)
    (fun τ hτ _ => by
      rw [mt, if_pos (hside hτ)]
      refine (restr_upper (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) hI01 hindZI hindI τ hδ).trans ?_
      rw [add_le_add_iff_left, mul_sum]
      refine (sum_le_sum fun σ hσ => ?_).trans
        (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun σ _ _ =>
          mul_nonneg (by linarith) (hm0 σ))
      obtain ⟨hne, hσs⟩ := mem_erase.mp hσ
      have hrσ : r ∉ σ := (mem_filter.mp hσs).2.1
      have h1 : (symmDiff σ τ).card ≠ 0 := by
        rw [Ne, card_eq_zero, ← bot_eq_empty, symmDiff_eq_bot]; exact hne
      have h2 : (symmDiff σ τᶜ).card ≠ 0 := by
        rw [Ne, card_eq_zero]
        intro h
        have : r ∈ symmDiff σ τᶜ := by simp [mem_symmDiff, hrσ, hτ.1]
        rw [h] at this; exact notMem_empty r this
      have := pow_le_of_le_one hδ0 hδ1 h1
      have := pow_le_of_le_one hδ0 hδ1 h2
      have := hm0 σ
      nlinarith) hgap hδρ).2
  exact ⟨hpos, fragmentary_consistency hL hZ hIm hV hident hT hTne hpos (sides r)
    (fun τ hτ u ω => Y_off hτ u ω) (fun τ hτ => mt_off hL hτ)⟩

end units

/-! ### Theorem 7.12(a), inconsistency: an infinite sequence of units -/

section infinite

open Filter Topology

variable {r : Fin n} {Z : ℕ → Finset (Fin n) → Ω → ℝ} {I : ℕ → Fin n → Ω → ℝ}

/-- The data of unit `u` of an infinite sequence. -/
def VN (Z : ℕ → Finset (Fin n) → Ω → ℝ) (I : ℕ → Fin n → Ω → ℝ) (u : ℕ) (ω : Ω) : UnitData n :=
  (fun σ => Z u σ ω, fun x => I u x ω)

/-- Unit `u` of an infinite sequence proposes the restriction of `τ`. -/
noncomputable def YN (r : Fin n) (Z : ℕ → Finset (Fin n) → Ω → ℝ) (I : ℕ → Fin n → Ω → ℝ)
    (τ : Finset (Fin n)) (u : ℕ) (ω : Ω) : ℝ :=
  g r τ (VN Z I u ω)

/-- The expected restriction support `m̃` of unit `0`, on the sides. -/
noncomputable def mtN (μ : Measure Ω) (r : Fin n) (Z : ℕ → Finset (Fin n) → Ω → ℝ)
    (I : ℕ → Fin n → Ω → ℝ) (τ : Finset (Fin n)) : ℝ :=
  if τ ∈ sides r then mR μ r (Z 0) (I 0) τ else 0

/-- All restriction indicators of a unit, as a function of its data. -/
noncomputable def G (r : Fin n) (v : UnitData n) : Finset (Fin n) → ℝ := fun σ => g r σ v

lemma measurable_G (r : Fin n) : Measurable (G (n := n) r) :=
  measurable_pi_iff.mpr fun σ => measurable_g r σ

variable (hZ : ∀ u σ, Measurable (Z u σ)) (hIm : ∀ u x, Measurable (I u x))
  (hV : iIndepFun (VN Z I) μ) (hident : ∀ u, IdentDistrib (VN Z I u) (VN Z I 0) μ μ)

include hZ hIm in
lemma measurable_VN (u : ℕ) : Measurable (VN Z I u) :=
  (measurable_pi_iff.mpr fun σ => hZ u σ).prodMk (measurable_pi_iff.mpr fun x => hIm u x)

include hZ hIm in
lemma measurable_YN (τ : Finset (Fin n)) (u : ℕ) : Measurable (YN r Z I τ u) :=
  (measurable_g r τ).comp (measurable_VN hZ hIm u)

lemma YN_mem (τ : Finset (Fin n)) (u : ℕ) (ω : Ω) : YN r Z I τ u ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold YN g; split_ifs <;> norm_num

include hV in
/-- The vectors `(Y τ u)_τ` are pairwise independent across units. -/
lemma pairwise_YN : Pairwise fun i j =>
    IndepFun (fun ω σ => YN r Z I σ i ω) (fun ω σ => YN r Z I σ j ω) μ :=
  fun _ _ hij => (hV.indepFun hij).comp (measurable_G r) (measurable_G r)

include hident in
/-- The vectors `(Y τ u)_τ` are identically distributed across units. -/
lemma ident_YN (u : ℕ) :
    IdentDistrib (fun ω σ => YN r Z I σ u ω) (fun ω σ => YN r Z I σ 0 ω) μ μ :=
  (hident u).comp (measurable_G r)

include hZ hIm in
/-- The indicators of unit `0` have mean `m̃`. -/
lemma integral_YN (τ : Finset (Fin n)) : μ[YN r Z I τ 0] = mtN μ r Z I τ := by
  unfold mtN
  by_cases hτ : τ ∈ sides r
  · rw [if_pos hτ]
    have hset : MeasurableSet {ω | ProposesRestr r (Z 0) (I 0) τ ω} := by
      have := measurableSet_data (r := r) (hZ 0) (hIm 0) fun F O =>
        NontrivOn O τ ∧ ∃ σ ∈ F, SameRestr O σ τ
      convert this using 2 with ω
      simp only [Set.mem_ofPred_eq, proposes_iff]
    have : YN r Z I τ 0 = Set.indicator {ω | ProposesRestr r (Z 0) (I 0) τ ω} 1 := by
      funext ω
      simp only [YN, g, VN, Set.indicator_apply, Pi.one_apply, hτ, true_and]
      rfl
    rw [this, integral_indicator_one hset]; rfl
  · rw [if_neg hτ]
    have : YN r Z I τ 0 = fun _ => 0 := by
      funext ω; simp [YN, g, hτ]
    rw [this, integral_zero]

include hZ hIm hV hident in
/-- **Theorem 7.12(a) (`thm:fragmentary`), inconsistency (Theorem 7.4(b) with `m̃`).**  Units form
an infinite sequence with i.i.d. data `V u`.  If some compatible `S` has `m̃(S) > m̃(T)`, then almost
surely the restriction-weighted support of `S` eventually exceeds that of `T`, and the probability
that `T` is a maximum-weight compatible set for the first `L` units tends to `0`. -/
theorem fragmentary_inconsistency (T S : Finset (Finset (Fin n))) (hS : IsSystem r S)
    (hlt : ∑ σ ∈ T, mtN μ r Z I σ < ∑ σ ∈ S, mtN μ r Z I σ) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop,
      ∑ σ ∈ T, ∑ u ∈ range L, YN r Z I σ u ω < ∑ σ ∈ S, ∑ u ∈ range L, YN r Z I σ u ω) ∧
    Tendsto (fun L => μ {ω | ∀ S', IsSystem r S' →
        ∑ σ ∈ S', ∑ u ∈ range L, YN r Z I σ u ω ≤ ∑ σ ∈ T, ∑ u ∈ range L, YN r Z I σ u ω})
      atTop (𝓝 0) :=
  Margin.inconsistency r T S hS (YN r Z I) (measurable_YN hZ hIm) YN_mem (pairwise_YN hV)
    (ident_YN hident) (mtN μ r Z I) (integral_YN hZ hIm) hlt

end infinite

end Stemma.FragmentaryUnits
