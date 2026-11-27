/-
Fragmentary witnesses (Theorem 7.12 of the technical report, `thm:fragmentary`).

Model of one unit.  `Z σ ω ∈ {0,1}` indicates that the complete unit proposes the non-trivial split
`σ` (a side away from `r`), so `m σ = P(Z σ = 1)`.  `I x ω ∈ {0,1}` indicates that witness `x` is
illegible; the legible set is `O = {x | I x = 0}`.  The illegibility indicators are independent
across witnesses (`iIndepFun I`), each of probability at most `δ`, and independent of the readings
(`IndepFun` of the vectors `(Z σ)_σ` and `(I x)_x`).  The unit proposes the restriction `τ|_O` when
some complete proposal `σ'` has the same restriction to `O` as `τ` and that restriction is
non-trivial; `m̃ τ` is the probability of this event.

Formalised: (b), both bounds; and the deterministic core of (c): if `m σ - m τ ≥ ρ` on conflicting
false/true pairs and `δ < ρ / (4 + 2μ)`, the expected restriction supports `m̃` have a positive
margin, so Theorem 7.4(a) (`Consistency.consistency`, whose statement is for any expected supports)
applies to the completion estimator with `m̃`.  Part (a) is that instantiation: it needs no new
proof beyond the fact that the restriction indicators are i.i.d. `[0,1]` variables with mean `m̃`,
which is the modelling assumption of the units, not proved here from a multi-unit model.
-/
import Mathlib
import StemmaLean.GammaConf

open MeasureTheory ProbabilityTheory Finset
open scoped Classical

namespace Stemma.Fragmentary

open Splits Margin GammaConf

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The legible witnesses. -/
noncomputable def legible (I : Fin n → Ω → ℝ) (ω : Ω) : Finset (Fin n) :=
  univ.filter fun x => I x ω = 0

/-- Two full splits (by one side) have the same restriction to `O`, as unordered partial splits. -/
def SameRestr (O A C : Finset (Fin n)) : Prop := A ∩ O = C ∩ O ∨ A ∩ O = Cᶜ ∩ O

/-- The restriction of the split with side `A` to `O` is non-trivial. -/
def NontrivOn (O A : Finset (Fin n)) : Prop := 2 ≤ (A ∩ O).card ∧ 2 ≤ (Aᶜ ∩ O).card

/-- The unit proposes the restriction of `τ` to its legible witnesses. -/
def ProposesRestr (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) (I : Fin n → Ω → ℝ)
    (τ : Finset (Fin n)) (ω : Ω) : Prop :=
  NontrivOn (legible I ω) τ ∧ ∃ σ ∈ sides r, Z σ ω = 1 ∧ SameRestr (legible I ω) σ τ

/-- Complete-data support. -/
noncomputable def mC (μ : Measure Ω) (Z : Finset (Fin n) → Ω → ℝ) (σ : Finset (Fin n)) : ℝ :=
  μ.real {ω | Z σ ω = 1}

/-- Restriction-weighted support `m̃`. -/
noncomputable def mR (μ : Measure Ω) (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ)
    (I : Fin n → Ω → ℝ) (τ : Finset (Fin n)) : ℝ :=
  μ.real {ω | ProposesRestr r Z I τ ω}

section bounds

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1)
  (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
  (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ)
include hZ hIm hI01 hindZI hindI

/-- `P(Z σ = 1, all witnesses of D in a given state) = m σ · ∏ P(state)`. -/
lemma meas_inter_illegible (σ : Finset (Fin n)) (D : Finset (Fin n)) (v : ℝ) :
    μ.real ({ω | Z σ ω = 1} ∩ {ω | ∀ x ∈ D, I x ω = v}) =
      mC μ Z σ * ∏ x ∈ D, μ.real {ω | I x ω = v} := by
  have hs : MeasurableSet {f : Finset (Fin n) → ℝ | f σ = 1} :=
    measurableSet_eq_fun (measurable_pi_apply σ) measurable_const
  have ht : MeasurableSet {f : Fin n → ℝ | ∀ x ∈ D, f x = v} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (measurable_pi_apply x) measurable_const
  have h1 := hindZI.measure_inter_preimage_eq_mul _ _ hs ht
  have h2 := hindI.measure_inter_preimage_eq_mul D (sets := fun _ => ({v} : Set ℝ))
    (fun _ _ => measurableSet_singleton v)
  have e1 : (fun ω σ => Z σ ω) ⁻¹' {f | f σ = 1} = {ω | Z σ ω = 1} := rfl
  have e2 : (fun ω x => I x ω) ⁻¹' {f | ∀ x ∈ D, f x = v} = {ω | ∀ x ∈ D, I x ω = v} := rfl
  have e3 : (⋂ x ∈ D, I x ⁻¹' ({v} : Set ℝ)) = {ω | ∀ x ∈ D, I x ω = v} := by
    ext ω; simp
  rw [e1, e2] at h1
  rw [e3] at h2
  rw [measureReal_def, h1, ENNReal.toReal_mul, h2, ENNReal.toReal_prod, mC, measureReal_def]
  rfl

/-- A complete proposal stays non-trivial on the legible witnesses with probability at least
`1 - 4δ`: `P(Z σ = 1, σ non-trivial on O) ≥ (1 - 4δ) m σ`. -/
theorem nontriv_lower {σ : Finset (Fin n)} (hσ : σ ∈ sides r)
    (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ) :
    (1 - 4 * δ) * mC μ Z σ ≤ μ.real {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
  have hside : IsSide r σ := (mem_filter.mp hσ).2
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := one_lt_card.mp (by have := hside.2.1; omega : 1 < σ.card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := one_lt_card.mp (by have := hside.2.2; omega : 1 < σᶜ.card)
  set F : Finset (Fin n) := {a₁, a₂, b₁, b₂}
  have hF4 : F.card ≤ 4 := card_le_four
  -- the four witnesses are legible with probability at least `1 - 4δ`
  have hleg : 1 - 4 * δ ≤ ∏ x ∈ F, μ.real {ω | I x ω = 0} := by
    have hone : ∀ x, μ.real {ω | I x ω = 0} = 1 - μ.real {ω | I x ω = 1} := by
      intro x
      have hc : {ω | I x ω = 0} = {ω | I x ω = 1}ᶜ := by
        ext ω; rcases hI01 x ω with h | h <;> simp [h]
      rw [hc, measureReal_compl (measurableSet_eq_fun (hIm x) measurable_const), probReal_univ]
    have hle : ∀ x, 0 ≤ μ.real {ω | I x ω = 1} := fun x => measureReal_nonneg
    -- ∏ (1 - p_x) ≥ 1 - ∑ p_x
    have key : ∀ G : Finset (Fin n), 1 - ∑ x ∈ G, μ.real {ω | I x ω = 1} ≤
        ∏ x ∈ G, (1 - μ.real {ω | I x ω = 1}) := by
      intro G
      induction G using Finset.induction_on with
      | empty => simp
      | insert y G hy ih =>
        rw [sum_insert hy, prod_insert hy]
        have hp1 : μ.real {ω | I y ω = 1} ≤ 1 := measureReal_le_one
        have hprod := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
        have hs0 : 0 ≤ ∑ x ∈ G, μ.real {ω | I x ω = 1} := sum_nonneg fun x _ => hle x
        nlinarith [hle y]
    have hsum : ∑ x ∈ F, μ.real {ω | I x ω = 1} ≤ 4 * δ :=
      (sum_le_sum fun x _ => hδ x).trans (by
        rw [sum_const, nsmul_eq_mul]
        have : (0 : ℝ) ≤ δ := (hle a₁).trans (hδ a₁)
        have : (F.card : ℝ) ≤ 4 := by exact_mod_cast hF4
        nlinarith)
    simp_rw [hone]
    linarith [key F]
  -- the event is contained in the restricted proposal
  have hsub : {ω | Z σ ω = 1} ∩ {ω | ∀ x ∈ F, I x ω = 0} ⊆
      {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
    rintro ω ⟨hz, hl⟩
    simp only [Set.mem_ofPred_eq] at hz hl ⊢
    have leg : ∀ x ∈ F, x ∈ legible I ω := fun x hx => by simp [legible, hl x hx]
    refine ⟨hz, ?_, ?_⟩
    · have : ({a₁, a₂} : Finset (Fin n)) ⊆ σ ∩ legible I ω := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_inter.mpr ⟨ha₁, leg _ (by simp [F])⟩
        · exact mem_inter.mpr ⟨ha₂, leg _ (by simp [F])⟩
      have := card_le_card this; rwa [card_pair ha] at this
    · have : ({b₁, b₂} : Finset (Fin n)) ⊆ σᶜ ∩ legible I ω := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_inter.mpr ⟨hb₁, leg _ (by simp [F])⟩
        · exact mem_inter.mpr ⟨hb₂, leg _ (by simp [F])⟩
      have := card_le_card this; rwa [card_pair hb] at this
  have hm0 : 0 ≤ mC μ Z σ := measureReal_nonneg
  calc (1 - 4 * δ) * mC μ Z σ ≤ mC μ Z σ * ∏ x ∈ F, μ.real {ω | I x ω = 0} := by nlinarith
    _ = μ.real ({ω | Z σ ω = 1} ∩ {ω | ∀ x ∈ F, I x ω = 0}) :=
        (meas_inter_illegible hZ hIm hI01 hindZI hindI σ F 0).symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-- **Theorem 7.12(b), lower bound:** `m̃ σ ≥ (1 - 4δ) m σ` for every non-trivial split `σ`. -/
theorem restr_lower {σ : Finset (Fin n)} (hσ : σ ∈ sides r) (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ) :
    (1 - 4 * δ) * mC μ Z σ ≤ mR μ r Z I σ :=
  (nontriv_lower hZ hIm hI01 hindZI hindI hσ hδ).trans
    (measureReal_mono (fun ω ⟨hz, hnt⟩ => ⟨hnt, σ, hσ, hz, Or.inl rfl⟩) (measure_ne_top _ _))

/-- **Theorem 7.12(b), upper bound:** `m̃ τ ≤ m τ + ∑_{σ' ≠ τ} m σ' (δ^{|A' △ C|} + δ^{|A' △ D|})`,
`τ = C | D`, `σ' = A' | B'`: the restrictions agree only if every witness on which the two splits
disagree, in one orientation, is illegible.  (`≤ m τ + 2 ∑ m σ' δ^{d(σ', τ)}` for `δ ≤ 1`.) -/
theorem restr_upper (τ : Finset (Fin n)) (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ) :
    mR μ r Z I τ ≤ mC μ Z τ + ∑ σ ∈ (sides r).erase τ,
      mC μ Z σ * (δ ^ (symmDiff σ τ).card + δ ^ (symmDiff σ τᶜ).card) := by
  set E : Finset (Fin n) → Finset (Fin n) → Set Ω :=
    fun σ D => {ω | Z σ ω = 1} ∩ {ω | ∀ x ∈ D, I x ω = 1}
  have hsub : {ω | ProposesRestr r Z I τ ω} ⊆ {ω | Z τ ω = 1} ∪
      ⋃ σ ∈ (sides r).erase τ, (E σ (symmDiff σ τ) ∪ E σ (symmDiff σ τᶜ)) := by
    intro ω hω
    obtain ⟨-, σ, hσ, hz, hsame⟩ := hω
    by_cases e : σ = τ
    · left; rw [← e]; exact hz
    right
    simp only [Set.mem_iUnion]
    refine ⟨σ, mem_erase.mpr ⟨e, hσ⟩, ?_⟩
    have ill : ∀ (C : Finset (Fin n)), σ ∩ legible I ω = C ∩ legible I ω →
        ∀ x ∈ symmDiff σ C, I x ω = 1 := by
      intro C hC x hx
      rcases hI01 x ω with h0 | h1
      · exfalso
        have hl : x ∈ legible I ω := by simp [legible, h0]
        rw [mem_symmDiff] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : x ∈ C ∩ legible I ω := hC ▸ mem_inter.mpr ⟨h1, hl⟩
          exact h2 (mem_inter.mp this).1
        · have : x ∈ σ ∩ legible I ω := hC.symm ▸ mem_inter.mpr ⟨h1, hl⟩
          exact h2 (mem_inter.mp this).1
      · exact h1
    rcases hsame with h | h
    · left; exact ⟨hz, ill τ h⟩
    · right; exact ⟨hz, ill τᶜ h⟩
  have hE : ∀ σ D, μ.real (E σ D) ≤ mC μ Z σ * δ ^ D.card := by
    intro σ D
    rw [meas_inter_illegible hZ hIm hI01 hindZI hindI σ D 1]
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    calc ∏ x ∈ D, μ.real {ω | I x ω = 1} ≤ ∏ _x ∈ D, δ := by
          gcongr with x _
          all_goals first | exact fun i _ => measureReal_nonneg | exact hδ _
      _ = δ ^ D.card := prod_const _
  calc mR μ r Z I τ ≤ μ.real ({ω | Z τ ω = 1} ∪
        ⋃ σ ∈ (sides r).erase τ, (E σ (symmDiff σ τ) ∪ E σ (symmDiff σ τᶜ))) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ mC μ Z τ + μ.real (⋃ σ ∈ (sides r).erase τ,
          (E σ (symmDiff σ τ) ∪ E σ (symmDiff σ τᶜ))) := measureReal_union_le _ _
    _ ≤ mC μ Z τ + ∑ σ ∈ (sides r).erase τ,
          μ.real (E σ (symmDiff σ τ) ∪ E σ (symmDiff σ τᶜ)) := by
        gcongr; exact measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
        gcongr with σ
        refine (measureReal_union_le _ _).trans ?_
        rw [mul_add]
        exact add_le_add (hE σ _) (hE σ _)

end bounds

/-! ### The deterministic core of (c) -/

/-- **Theorem 7.12(c), core.**  Let `T` be binary, `0 ≤ m ≤ 1`, `μ_tot = ∑ m` over the non-trivial
splits, and let `m̃ ≥ 0` satisfy the two bounds of (b) in the form
`m̃ σ ≥ (1 - 4δ) m σ` and `m̃ τ ≤ m τ + 2 δ μ_tot` (the latter follows from (b) since
`δ^{d} ≤ δ` for `d ≥ 1`).  If `m σ - m τ ≥ ρ` whenever a false `τ` and a true `σ` conflict, and
`0 ≤ δ < ρ / (4 + 2 μ_tot)`, then `T` is the unique maximum of `m̃` over compatible sets and its
margin for `m̃` is positive; Theorem 7.4(a) then gives consistency of the completion estimator. -/
theorem fragmentary_margin_pos {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) (m mt : Finset (Fin n) → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) (hm1 : ∀ σ, m σ ≤ 1)
    (hmt0 : ∀ σ, 0 ≤ mt σ) {δ ρ μtot : ℝ} (hδ0 : 0 ≤ δ)
    (hlow : ∀ σ ∈ T, (1 - 4 * δ) * m σ ≤ mt σ)
    (hupp : ∀ τ, IsSide r τ → τ ∉ T → mt τ ≤ m τ + 2 * δ * μtot)
    (hgap : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ → ρ ≤ m σ - m τ)
    (hδρ : δ * (4 + 2 * μtot) < ρ) :
    (∀ S, IsSystem r S → S ≠ T → wt mt S < wt mt T) ∧ 0 < margin r mt T hTne := by
  have hloc : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ → mt τ < mt σ := by
    intro τ σ hτ hτT hσ hc
    have h1 := hlow σ hσ
    have h2 := hupp τ hτ hτT
    have h3 := hgap τ σ hτ hτT hσ hc
    have := hm1 σ; have := hm0 σ
    nlinarith
  obtain ⟨-, hlt⟩ := local_separation_strong hT mt (fun A _ => hmt0 A) hloc
  refine ⟨fun S hS hne => hlt S hS hne, ?_⟩
  unfold margin
  rw [lt_inf'_iff]
  intro S hS
  simp only [competitors, mem_filter, mem_univ, true_and] at hS
  have hpos : (0 : ℝ) < (T \ S).card :=
    by exact_mod_cast card_pos.mpr (displacement_matching hT hS.1 hS.2).1
  have hd := hlt S hS.1 hS.2
  unfold wt at hd
  have := (Finset.sum_sdiff_sub_sum_sdiff (s₁ := S) (s₂ := T) (f := mt))
  unfold ratio
  apply div_pos _ hpos
  linarith

end Stemma.Fragmentary
