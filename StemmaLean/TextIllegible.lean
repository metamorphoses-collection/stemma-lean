/-
Illegibility that depends on the text (Proposition 7.13 of the technical report,
`prop:textillegible`).  Numbers are those of the current draft of the report, in which the
fragmentary-witness theorem (`thm:fragmentary`) is 6.12 and the cutting-plane theorem
(`thm:cuttingconsistency`) is 6.14; `Fragmentary.lean`, `FragmentaryUnits.lean` and
`CuttingIllegible.lean` call them 6.11 and 6.12.

The model of one unit is that of `Fragmentary.lean` and `CuttingIllegible.lean`: `Z σ ∈ {0,1}` says
that the complete unit proposes the non-trivial split `σ`, `I x ∈ {0,1}` that witness `x` is
illegible.  The independence hypotheses of those files (`IndepFun` of readings and illegibility,
`iIndepFun` across witnesses, `P(I x = 1) ≤ δ`) are replaced by one hypothesis,
`CondIllegible μ r Z I δ`: for every set `F` of complete proposals and every witness `x`,
`P(x illegible ∧ zs = F) ≤ δ · P(zs = F)`, i.e. given the unit's complete proposals each witness
is illegible with conditional probability at most `δ`.  The joint law of the illegibility
indicators, and their dependence on the readings, are otherwise arbitrary.  Conditioning on the
complete proposals, a function of the readings, is weaker than conditioning on the readings, so
the report's hypothesis implies this one; the independent model of Theorem 7.12 implies it too
(`condIllegible_of_indep`).

Formalised:
* (b) `restr_lower`: `m̃ σ ≥ (1 - 4δ) m σ`; `restr_upper`: `m̃ τ ≤ m τ + 2δμ`, `μ = ∑ m`;
* (c) `margin_pos`: if `m σ - m τ ≥ ρ` on conflicting true/false pairs and `δ (4 + 2μ) < ρ`, then
  `T` is the unique maximum of `m̃` and its margin for `m̃` is positive; `consistent`: with the units'
  data (readings, legibility) i.i.d. as in `FragmentaryUnits.lean` and unit `0` satisfying the
  hypothesis, the completion estimator misses `T` with probability at most
  `2 |sides| e^{-L γ̃²/2}`.  Part (a) of Theorem 7.12 (`FragmentaryUnits.fragmentary_consistency`,
  `_bernstein`, `fragmentary_inconsistency`) never used the illegibility model and holds as is;
* Theorem 7.14(c) under the same hypothesis: `M_lower`, `M_upper`, `cutting_illegible` (the
  inequality, unchanged), `cutting_illegible_margin`, `cutting_illegible_consistent`.
-/
import Mathlib
import StemmaLean.FragmentaryUnits

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped Classical

namespace Stemma.TextIllegible

open Stemma.Splits Stemma.Cutting Stemma.Fragmentary Stemma.GammaConf Stemma.Margin
  Stemma.CuttingIllegible

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Given the unit's complete proposals, each witness is illegible with conditional probability
at most `δ`: `P(zs = F ∧ I x = 1) ≤ δ P(zs = F)` for every `F` and `x`. -/
def CondIllegible (μ : Measure Ω) (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) (I : Fin n → Ω → ℝ)
    (δ : ℝ) : Prop :=
  ∀ (F : Finset (Finset (Fin n))) (x : Fin n),
    μ.real {ω | zs r Z ω = F ∧ I x ω = 1} ≤ δ * μ.real {ω | zs r Z ω = F}

section model

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}

/-- The independent model of Theorem 7.12 satisfies the hypothesis. -/
theorem condIllegible_of_indep (hZ : ∀ σ, Measurable (Z σ))
    (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
    (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ) : CondIllegible μ r Z I δ := by
  intro F x
  have hs : MeasurableSet {f : Finset (Fin n) → ℝ | (sides r).filter (fun σ => f σ = 1) = F} := by
    have := measurableSet_filter_eq (Ω := Finset (Fin n) → ℝ) (sides r) (fun σ f => f σ)
      (fun σ => measurable_pi_apply σ) 1 F
    exact this
  have h := meas_inter_ill_le hZ hindZI hindI hδ _ hs (D := {x}) (singleton_nonempty x)
  have e1 : {ω | (fun σ => Z σ ω) ∈ {f : Finset (Fin n) → ℝ |
      (sides r).filter (fun σ => f σ = 1) = F}} ∩ {ω | ∀ y ∈ ({x} : Finset (Fin n)), I y ω = 1} =
      {ω | zs r Z ω = F ∧ I x ω = 1} := by
    ext ω; simp [zs]
  have e2 : {ω | (fun σ => Z σ ω) ∈ {f : Finset (Fin n) → ℝ |
      (sides r).filter (fun σ => f σ = 1) = F}} = {ω | zs r Z ω = F} := by
    ext ω; simp [zs]
  rw [e1, e2] at h
  linarith

variable (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1) (hc : CondIllegible μ r Z I δ)

include hZ in
lemma measurableSet_zs (p : Finset (Finset (Fin n)) → Prop) :
    MeasurableSet {ω | p (zs r Z ω)} := by
  have : {ω | p (zs r Z ω)} = ⋃ F ∈ (univ.filter p : Finset (Finset (Finset (Fin n)))),
      {ω | zs r Z ω = F} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ fun F _ => measurableSet_filter_eq _ Z hZ 1 F

include hZ hIm hc in
/-- The hypothesis for any event about the complete proposals:
`P(p(zs) ∧ I x = 1) ≤ δ P(p(zs))`. -/
lemma ill_le (p : Finset (Finset (Fin n)) → Prop) (x : Fin n) :
    μ.real {ω | p (zs r Z ω) ∧ I x ω = 1} ≤ δ * μ.real {ω | p (zs r Z ω)} := by
  set G : Finset (Finset (Finset (Fin n))) := univ.filter p
  have e1 : {ω | p (zs r Z ω) ∧ I x ω = 1} = ⋃ F ∈ G, {ω | zs r Z ω = F ∧ I x ω = 1} := by
    ext ω; simp [G]
  have e2 : {ω | p (zs r Z ω)} = ⋃ F ∈ G, {ω | zs r Z ω = F} := by
    ext ω; simp [G]
  have hmF : ∀ F, MeasurableSet {ω | zs r Z ω = F} := fun F =>
    measurableSet_filter_eq _ Z hZ 1 F
  have hIx : MeasurableSet {ω | I x ω = 1} := measurableSet_eq_fun (hIm x) measurable_const
  rw [e1, e2, measureReal_biUnion_finset (f := fun F => {ω | zs r Z ω = F ∧ I x ω = 1})
      (fun F _ G _ hFG => ?_) (fun F _ => (hmF F).inter hIx),
    measureReal_biUnion_finset (f := fun F => {ω | zs r Z ω = F})
      (fun F _ G _ hFG => ?_) (fun F _ => hmF F), mul_sum]
  · exact sum_le_sum fun F _ => hc F x
  all_goals exact Set.disjoint_left.mpr fun ω h1 h2 => hFG (by
    simp only [Set.mem_ofPred_eq] at h1 h2
    first | exact h1.1.symm.trans h2.1 | exact h1.symm.trans h2)

include hZ hIm hc in
lemma delta_nonneg : 0 ≤ δ := by
  have h := ill_le hZ hIm hc (fun _ => True) r
  have e : {ω : Ω | True} = Set.univ := Set.ofPred_true
  simp only [true_and, e, probReal_univ, mul_one] at h
  exact measureReal_nonneg.trans h

include hZ hIm hc in
/-- With one witness of `D` at least, all of `D` illegible costs a factor `δ`. -/
lemma ill_set_le (p : Finset (Finset (Fin n)) → Prop) {D : Finset (Fin n)} (hD : D.Nonempty) :
    μ.real {ω | p (zs r Z ω) ∧ ∀ x ∈ D, I x ω = 1} ≤ δ * μ.real {ω | p (zs r Z ω)} := by
  obtain ⟨x, hx⟩ := hD
  have hsub : {ω | p (zs r Z ω) ∧ ∀ x ∈ D, I x ω = 1} ⊆ {ω | p (zs r Z ω) ∧ I x ω = 1} :=
    fun ω h => ⟨h.1, h.2 x hx⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (ill_le hZ hIm hc p x)

include hZ hIm hI01 hc in
/-- Every witness of `F` legible: `P(p(zs) ∧ F ⊆ O) ≥ (1 - |F| δ) P(p(zs))`, by a union bound. -/
lemma legible_lower (p : Finset (Finset (Fin n)) → Prop) (F : Finset (Fin n)) :
    μ.real {ω | p (zs r Z ω)} - F.card * δ * μ.real {ω | p (zs r Z ω)} ≤
      μ.real {ω | p (zs r Z ω) ∧ ∀ x ∈ F, I x ω = 0} := by
  have hsub : {ω | p (zs r Z ω)} ⊆ {ω | p (zs r Z ω) ∧ ∀ x ∈ F, I x ω = 0} ∪
      ⋃ x ∈ F, {ω | p (zs r Z ω) ∧ I x ω = 1} := by
    intro ω hp
    by_cases h : ∀ x ∈ F, I x ω = 0
    · exact Or.inl ⟨hp, h⟩
    · push Not at h
      obtain ⟨x, hx, hne⟩ := h
      refine Or.inr (Set.mem_biUnion hx ⟨hp, ?_⟩)
      rcases hI01 x ω with h0 | h1
      · exact absurd h0 hne
      · exact h1
  have h1 := (measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_union_le _ _)
  have h2 : μ.real (⋃ x ∈ F, {ω | p (zs r Z ω) ∧ I x ω = 1}) ≤
      F.card * δ * μ.real {ω | p (zs r Z ω)} := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (sum_le_sum fun x _ => ill_le hZ hIm hc p x).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]; ring
  linarith

include hZ hIm hI01 hc in
/-- A complete proposal stays non-trivial on the legible witnesses with probability at least
`1 - 4δ`. -/
theorem nontriv_lower {σ : Finset (Fin n)} (hσ : σ ∈ sides r) :
    (1 - 4 * δ) * mC μ Z σ ≤ μ.real {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
  have hδ0 := delta_nonneg hZ hIm hc
  have hside : IsSide r σ := (mem_filter.mp hσ).2
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := one_lt_card.mp (by have := hside.2.1; omega : 1 < σ.card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := one_lt_card.mp (by have := hside.2.2; omega : 1 < σᶜ.card)
  set F : Finset (Fin n) := {a₁, a₂, b₁, b₂}
  have hF4 : (F.card : ℝ) ≤ 4 := by exact_mod_cast card_le_four
  have hm : mC μ Z σ = μ.real {ω | σ ∈ zs r Z ω} := by
    unfold mC; congr 1; ext ω; simp [mem_zs hσ]
  have hL := legible_lower hZ hIm hI01 hc (fun G => σ ∈ G) F
  have hsub : {ω | σ ∈ zs r Z ω ∧ ∀ x ∈ F, I x ω = 0} ⊆
      {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
    rintro ω ⟨hz, hl⟩
    have hz' : Z σ ω = 1 := (mem_zs hσ ω).mp hz
    have leg : ∀ x ∈ F, x ∈ legible I ω := fun x hx => by simp [legible, hl x hx]
    refine ⟨hz', ?_, ?_⟩
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
  rw [← hm] at hL
  have h4 : (F.card : ℝ) * δ * mC μ Z σ ≤ 4 * δ * mC μ Z σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF4 hδ0) hm0
  calc (1 - 4 * δ) * mC μ Z σ ≤ mC μ Z σ - F.card * δ * mC μ Z σ := by linarith
    _ ≤ _ := hL
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), lower bound of Theorem 7.12(b):**
`m̃ σ ≥ (1 - 4δ) m σ` for every non-trivial split `σ`. -/
theorem restr_lower {σ : Finset (Fin n)} (hσ : σ ∈ sides r) :
    (1 - 4 * δ) * mC μ Z σ ≤ mR μ r Z I σ :=
  (nontriv_lower hZ hIm hI01 hc hσ).trans
    (measureReal_mono (fun _ω ⟨hz, hnt⟩ => ⟨hnt, σ, hσ, hz, Or.inl rfl⟩) (measure_ne_top _ _))

include hZ hIm hI01 hc in
/-- Two distinct sides away from `r` share their restriction with probability at most `2δ`, on
any event about the complete proposals. -/
lemma meas_same_le (p : Finset (Finset (Fin n)) → Prop) {A C : Finset (Fin n)}
    (hA : A ∈ sides r) (hC : C ∈ sides r) (hAC : A ≠ C) :
    μ.real {ω | p (zs r Z ω) ∧ SameRestr (legible I ω) A C} ≤
      2 * δ * μ.real {ω | p (zs r Z ω)} := by
  have hrA : r ∉ A := (mem_filter.mp hA).2.1
  have hrC : r ∉ C := (mem_filter.mp hC).2.1
  have hD1 : (symmDiff A C).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, ← bot_eq_empty, symmDiff_eq_bot]; exact hAC
  have hD2 : (symmDiff A Cᶜ).Nonempty := ⟨r, by simp [mem_symmDiff, hrA, hrC]⟩
  have hsub : {ω | p (zs r Z ω) ∧ SameRestr (legible I ω) A C} ⊆
      {ω | p (zs r Z ω) ∧ ∀ x ∈ symmDiff A C, I x ω = 1} ∪
        {ω | p (zs r Z ω) ∧ ∀ x ∈ symmDiff A Cᶜ, I x ω = 1} := by
    rintro ω ⟨hz, hsame⟩
    rcases ill_of_sameRestr hI01 hsame with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ δ * μ.real {ω | p (zs r Z ω)} + δ * μ.real {ω | p (zs r Z ω)} :=
        add_le_add (ill_set_le hZ hIm hc p hD1) (ill_set_le hZ hIm hc p hD2)
    _ = _ := by ring

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), upper bound of Theorem 7.12(b) with `δ^d` replaced
by `δ`:** `m̃ τ ≤ m τ + 2 δ μ`, `μ = ∑ m` over the non-trivial splits. -/
theorem restr_upper {τ : Finset (Fin n)} (hτ : τ ∈ sides r) :
    mR μ r Z I τ ≤ mC μ Z τ + 2 * δ * mu1 μ r Z := by
  have hδ0 := delta_nonneg hZ hIm hc
  set E : Finset (Fin n) → Set Ω :=
    fun σ => {ω | σ ∈ zs r Z ω ∧ SameRestr (legible I ω) σ τ}
  have hsub : {ω | ProposesRestr r Z I τ ω} ⊆ {ω | Z τ ω = 1} ∪ ⋃ σ ∈ (sides r).erase τ, E σ := by
    intro ω hω
    obtain ⟨-, σ, hσ, hz, hsame⟩ := hω
    by_cases e : σ = τ
    · left; rw [← e]; exact hz
    right
    exact Set.mem_biUnion (mem_erase.mpr ⟨e, hσ⟩) ⟨(mem_zs hσ ω).mpr hz, hsame⟩
  have hE : ∀ σ ∈ (sides r).erase τ, μ.real (E σ) ≤ 2 * δ * mC μ Z σ := by
    intro σ hσ
    obtain ⟨hne, hσs⟩ := mem_erase.mp hσ
    have hm : mC μ Z σ = μ.real {ω | σ ∈ zs r Z ω} := by
      unfold mC; congr 1; ext ω; simp [mem_zs hσs]
    rw [hm]
    exact meas_same_le hZ hIm hI01 hc (fun G => σ ∈ G) hσs hτ hne
  calc mR μ r Z I τ ≤ μ.real ({ω | Z τ ω = 1} ∪ ⋃ σ ∈ (sides r).erase τ, E σ) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ mC μ Z τ + μ.real (⋃ σ ∈ (sides r).erase τ, E σ) := measureReal_union_le _ _
    _ ≤ mC μ Z τ + ∑ σ ∈ (sides r).erase τ, μ.real (E σ) := by
        gcongr; exact measureReal_biUnion_finset_le _ _
    _ ≤ mC μ Z τ + ∑ σ ∈ (sides r).erase τ, 2 * δ * mC μ Z σ := by
        gcongr with σ hσ; exact hE σ hσ
    _ ≤ mC μ Z τ + 2 * δ * mu1 μ r Z := by
        rw [← mul_sum, mu1]
        gcongr
        · exact fun _ _ _ => measureReal_nonneg
        · exact erase_subset τ (sides r)

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), the sufficient condition of Theorem 7.12(c).**  Let
`T` be binary.  If `m σ - m τ ≥ ρ` whenever a false `τ` and a true `σ` conflict, and
`δ (4 + 2μ) < ρ`, `μ = ∑ m`, then `T` is the unique maximum of `m̃` over compatible sets and its
margin for `m̃` is positive. -/
theorem margin_pos {T : Finset (Finset (Fin n))} (hT : IsBinary r T) (hTne : T.Nonempty) {ρ : ℝ}
    (hgap : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ → ρ ≤ mC μ Z σ - mC μ Z τ)
    (hδρ : δ * (4 + 2 * mu1 μ r Z) < ρ) :
    (∀ S, IsSystem r S → S ≠ T → wt (mR μ r Z I) S < wt (mR μ r Z I) T) ∧
      0 < margin r (mR μ r Z I) T hTne := by
  have hside : ∀ {A}, IsSide r A → A ∈ sides r := fun h => mem_filter.mpr ⟨mem_univ _, h⟩
  exact fragmentary_margin_pos hT hTne (mC μ Z) (mR μ r Z I) (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) (fun _ => measureReal_nonneg) (delta_nonneg hZ hIm hc)
    (fun σ hσ => restr_lower hZ hIm hI01 hc (hside (hT.1.1 σ hσ)))
    (fun τ hτ _ => restr_upper hZ hIm hI01 hc (hside hτ)) hgap hδρ

end model

/-! ### Theorem 7.12(c) under the hypothesis: many units -/

section units

open Stemma.FragmentaryUnits

variable {L : ℕ} (hL : 0 < L) {r : Fin n} {Z : Fin L → Finset (Fin n) → Ω → ℝ}
  {I : Fin L → Fin n → Ω → ℝ}
  (hZ : ∀ u σ, Measurable (Z u σ)) (hIm : ∀ u x, Measurable (I u x))
  (hV : iIndepFun (V Z I) μ) (hident : ∀ u, IdentDistrib (V Z I u) (V Z I ⟨0, hL⟩) μ μ)

include hZ hIm hV hident in
/-- **Proposition 7.13 (`prop:textillegible`), Theorem 7.12(c) with illegibility that depends on
the text.**  The units' data `V u` (complete proposals, illegibility indicators) are independent
and identically distributed, as in `FragmentaryUnits.lean`; for unit `0` the only hypothesis on
legibility is `CondIllegible`: given its complete proposals, each witness is illegible with
probability at most `δ`.  If `m σ - m τ ≥ ρ` whenever a false `τ` and a true `σ` conflict and
`δ (4 + 2 μ) < ρ`, the margin `γ̃` of `m̃` is positive and the completion estimator misses `T`
with probability at most `2 |sides| e^{-L γ̃²/2}`: it is consistent. -/
theorem consistent {T : Finset (Finset (Fin n))} (hT : IsBinary r T) (hTne : T.Nonempty)
    {δ ρ : ℝ} (hI01 : ∀ x ω, I ⟨0, hL⟩ x ω = 0 ∨ I ⟨0, hL⟩ x ω = 1)
    (hc : CondIllegible μ r (Z ⟨0, hL⟩) (I ⟨0, hL⟩) δ)
    (hgap : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ →
      ρ ≤ mC μ (Z ⟨0, hL⟩) σ - mC μ (Z ⟨0, hL⟩) τ)
    (hδρ : δ * (4 + 2 * ∑ σ ∈ sides r, mC μ (Z ⟨0, hL⟩) σ) < ρ) :
    0 < margin r (FragmentaryUnits.mt hL μ r Z I) T hTne ∧
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y r Z I σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y r Z I σ u ω) / L} ≤
      2 * (sides r).card * exp (-L * margin r (FragmentaryUnits.mt hL μ r Z I) T hTne ^ 2 / 2) := by
  have hside : ∀ {A}, IsSide r A → A ∈ sides r := fun h => mem_filter.mpr ⟨mem_univ _, h⟩
  have hpos := (fragmentary_margin_pos hT hTne (mC μ (Z ⟨0, hL⟩)) (FragmentaryUnits.mt hL μ r Z I)
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (fun σ => by unfold FragmentaryUnits.mt; split_ifs <;> first | exact measureReal_nonneg | exact le_rfl)
    (delta_nonneg (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) hc)
    (fun σ hσ => by
      rw [FragmentaryUnits.mt, if_pos (hside (hT.1.1 σ hσ))]
      exact restr_lower (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) hI01 hc (hside (hT.1.1 σ hσ)))
    (fun τ hτ _ => by
      rw [FragmentaryUnits.mt, if_pos (hside hτ)]
      exact restr_upper (hZ ⟨0, hL⟩) (hIm ⟨0, hL⟩) hI01 hc (hside hτ)) hgap hδρ).2
  exact ⟨hpos, fragmentary_consistency hL hZ hIm hV hident hT hTne hpos (sides r)
    (fun τ hτ u ω => Y_off hτ u ω) (fun τ hτ => mt_off hL hτ)⟩

end units

/-! ### Theorem 7.14(c) under the hypothesis: the cutting-plane estimator -/

section cutting

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1) (hc : CondIllegible μ r Z I δ)

include hZ hIm hI01 hc in
/-- **Theorem 7.14(c) under Proposition 7.13, true stemma.**  `M(T) ≥ (1 - 4δ) m(T) - 2δ μ₂`. -/
theorem M_lower {T : Finset (Finset (Fin n))} (hT : T ⊆ sides r) :
    (1 - 4 * δ) * ∑ σ ∈ T, mC μ Z σ - 2 * δ * mu2 μ r Z ≤
      ∫ ω, (count T (zs r Z ω) (legible I ω) : ℝ) ∂μ := by
  have hδ0 := delta_nonneg hZ hIm hc
  set p1 : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun σ F O => σ ∈ F ∧ NontrivOn O σ
  set p2 : Finset (Fin n) × Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun q F O => q.1 ∈ F ∧ q.2 ∈ F ∧ SameRestr O q.1 q.2
  have hpt : (fun ω => ∑ σ ∈ T, ind r Z I (p1 σ) ω - (1 / 2) * ∑ q ∈ T.offDiag, ind r Z I (p2 q) ω)
      ≤ fun ω => (count T (zs r Z ω) (legible I ω) : ℝ) := by
    intro ω
    have h := count_lower T (zs r Z ω) (legible I ω)
    have e1 : ((T.filter fun σ => σ ∈ zs r Z ω ∧ NontrivOn (legible I ω) σ).card : ℝ) =
        ∑ σ ∈ T, ind r Z I (p1 σ) ω := by
      rw [card_filter]; push_cast; exact sum_congr rfl fun σ _ => by simp [ind, p1]
    have e2 : ((T.offDiag.filter fun q => q.1 ∈ zs r Z ω ∧ q.2 ∈ zs r Z ω ∧
        SameRestr (legible I ω) q.1 q.2).card : ℝ) = ∑ q ∈ T.offDiag, ind r Z I (p2 q) ω := by
      rw [card_filter]; push_cast; exact sum_congr rfl fun q _ => by simp [ind, p2]
    have h' : (2 : ℝ) * ((T.filter fun σ => σ ∈ zs r Z ω ∧ NontrivOn (legible I ω) σ).card) ≤
        2 * (count T (zs r Z ω) (legible I ω)) + ((T.offDiag.filter fun q => q.1 ∈ zs r Z ω ∧
          q.2 ∈ zs r Z ω ∧ SameRestr (legible I ω) q.1 q.2).card) := by exact_mod_cast h
    rw [e1, e2] at h'
    show _ ≤ _
    linarith
  have hint1 : Integrable (fun ω => ∑ σ ∈ T, ind r Z I (p1 σ) ω) μ :=
    integrable_finsetSum _ fun σ _ => integrable_ind hZ hIm _
  have hint2 : Integrable (fun ω => ∑ q ∈ T.offDiag, ind r Z I (p2 q) ω) μ :=
    integrable_finsetSum _ fun q _ => integrable_ind hZ hIm _
  have hmono : ∫ ω, (∑ σ ∈ T, ind r Z I (p1 σ) ω -
      (1 / 2) * ∑ q ∈ T.offDiag, ind r Z I (p2 q) ω) ∂μ ≤
      ∫ ω, (count T (zs r Z ω) (legible I ω) : ℝ) ∂μ :=
    integral_mono (hint1.sub (hint2.const_mul (1 / 2))) (integrable_count hZ hIm T) hpt
  rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul, integral_finsetSum _
    fun σ _ => integrable_ind hZ hIm _, integral_finsetSum _ fun q _ => integrable_ind hZ hIm _]
    at hmono
  simp only [integral_ind hZ hIm] at hmono
  have hA : (1 - 4 * δ) * ∑ σ ∈ T, mC μ Z σ ≤
      ∑ σ ∈ T, μ.real {ω | p1 σ (zs r Z ω) (legible I ω)} := by
    rw [mul_sum]
    refine sum_le_sum fun σ hσ => ?_
    have heq : {ω | p1 σ (zs r Z ω) (legible I ω)} =
        {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
      ext ω; simp [p1, mem_zs (hT hσ)]
    rw [heq]
    exact nontriv_lower hZ hIm hI01 hc (hT hσ)
  have hB : ∑ q ∈ T.offDiag, μ.real {ω | p2 q (zs r Z ω) (legible I ω)} ≤ 4 * δ * mu2 μ r Z := by
    calc ∑ q ∈ T.offDiag, μ.real {ω | p2 q (zs r Z ω) (legible I ω)}
        ≤ ∑ q ∈ T.offDiag, 2 * δ * μ.real {ω | Z q.1 ω = 1 ∧ Z q.2 ω = 1} := by
          refine sum_le_sum fun q hq => ?_
          obtain ⟨h1, h2, h3⟩ := mem_offDiag.mp hq
          have heq : {ω | p2 q (zs r Z ω) (legible I ω)} = {ω | (q.1 ∈ zs r Z ω ∧ q.2 ∈ zs r Z ω)
              ∧ SameRestr (legible I ω) q.1 q.2} := by
            ext ω; simp [p2, and_assoc]
          have heq2 : {ω | Z q.1 ω = 1 ∧ Z q.2 ω = 1} =
              {ω | q.1 ∈ zs r Z ω ∧ q.2 ∈ zs r Z ω} := by
            ext ω; simp [mem_zs (hT h1), mem_zs (hT h2)]
          rw [heq, heq2]
          exact meas_same_le hZ hIm hI01 hc (fun G => q.1 ∈ G ∧ q.2 ∈ G) (hT h1) (hT h2) h3
      _ ≤ ∑ q ∈ (sides r).offDiag, 2 * δ * μ.real {ω | Z q.1 ω = 1 ∧ Z q.2 ω = 1} :=
          sum_le_sum_of_subset_of_nonneg (offDiag_mono hT) fun _ _ _ =>
            mul_nonneg (by linarith) measureReal_nonneg
      _ = 4 * δ * mu2 μ r Z := by rw [← mul_sum, mu2]; ring
  linarith

include hZ hIm hI01 hc in
/-- **Theorem 7.14(c) under Proposition 7.13, rival stemma.**  `M(T') ≤ m(T') + 2 |T'| δ μ`. -/
theorem M_upper {T' : Finset (Finset (Fin n))} (hT' : T' ⊆ sides r) :
    ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∑ σ ∈ T', mC μ Z σ + 2 * δ * T'.card * mu1 μ r Z := by
  have hδ0 := delta_nonneg hZ hIm hc
  set p1 : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop := fun σ F _ => σ ∈ F
  set p2 : Finset (Fin n) → Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun σ τ F O => σ ∈ F ∧ SameRestr O τ σ
  have hpt : (fun ω => (count T' (zs r Z ω) (legible I ω) : ℝ)) ≤ fun ω =>
      ∑ σ ∈ T', ind r Z I (p1 σ) ω + ∑ σ ∈ sides r \ T', ∑ τ ∈ T', ind r Z I (p2 σ τ) ω := by
    intro ω
    refine (count_upper T' (zs r Z ω) (filter_subset _ _) (legible I ω)).trans (le_of_eq ?_)
    simp only [ind, p1, p2]; congr! 4
  have hint1 : Integrable (fun ω => ∑ σ ∈ T', ind r Z I (p1 σ) ω) μ :=
    integrable_finsetSum _ fun σ _ => integrable_ind hZ hIm _
  have hint2 : ∀ σ, Integrable (fun ω => ∑ τ ∈ T', ind r Z I (p2 σ τ) ω) μ := fun σ =>
    integrable_finsetSum _ fun τ _ => integrable_ind hZ hIm _
  have hint3 : Integrable (fun ω => ∑ σ ∈ sides r \ T', ∑ τ ∈ T', ind r Z I (p2 σ τ) ω) μ :=
    integrable_finsetSum _ fun σ _ => hint2 σ
  have hmono : ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∫ ω, (∑ σ ∈ T', ind r Z I (p1 σ) ω +
        ∑ σ ∈ sides r \ T', ∑ τ ∈ T', ind r Z I (p2 σ τ) ω) ∂μ :=
    integral_mono (integrable_count hZ hIm T') (hint1.add hint3) hpt
  rw [integral_add hint1 hint3, integral_finsetSum _ fun σ _ => integrable_ind hZ hIm _,
    integral_finsetSum _ fun σ _ => hint2 σ] at hmono
  simp only [integral_finsetSum _ fun τ _ => integrable_ind hZ hIm _, integral_ind hZ hIm]
    at hmono
  have hA : ∑ σ ∈ T', μ.real {ω | p1 σ (zs r Z ω) (legible I ω)} = ∑ σ ∈ T', mC μ Z σ := by
    refine sum_congr rfl fun σ hσ => ?_
    unfold mC; congr 1; ext ω; simp [p1, mem_zs (hT' hσ)]
  have hB : ∑ σ ∈ sides r \ T', ∑ τ ∈ T', μ.real {ω | p2 σ τ (zs r Z ω) (legible I ω)} ≤
      2 * δ * T'.card * mu1 μ r Z := by
    calc ∑ σ ∈ sides r \ T', ∑ τ ∈ T', μ.real {ω | p2 σ τ (zs r Z ω) (legible I ω)}
        ≤ ∑ σ ∈ sides r \ T', ∑ τ ∈ T', 2 * δ * mC μ Z σ := by
          refine sum_le_sum fun σ hσ => sum_le_sum fun τ hτ => ?_
          obtain ⟨hσs, hσT⟩ := mem_sdiff.mp hσ
          have hm : mC μ Z σ = μ.real {ω | σ ∈ zs r Z ω} := by
            unfold mC; congr 1; ext ω; simp [mem_zs hσs]
          rw [hm]
          exact meas_same_le hZ hIm hI01 hc (fun G => σ ∈ G) (hT' hτ) hσs
            (fun h => hσT (h ▸ hτ))
      _ = 2 * δ * T'.card * ∑ σ ∈ sides r \ T', mC μ Z σ := by
          rw [mul_sum]; refine sum_congr rfl fun σ _ => ?_
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * δ * T'.card * mu1 μ r Z := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => measureReal_nonneg
  linarith

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), Theorem 7.14(c), the inequality.**  Under
illegibility that depends on the text, for binary stemmata `T` and `T'`,
`M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (2 (n - 1) μ + 2 μ₂)`, as in Theorem 7.14(c). -/
theorem cutting_illegible (hn : 3 ≤ n) {T T' : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hT' : IsBinary r T') {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I) :
    ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ -
        δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) ≤
      M μ P T - M μ P T' := by
  have hδ0 := delta_nonneg hZ hIm hc
  have h1 := M_lower hZ hIm hI01 hc (subset_sides hT.1)
  have h2 := M_upper hZ hIm hI01 hc (subset_sides hT'.1)
  rw [hT'.2, Nat.cast_sub hn] at h2
  have hmT : ∑ σ ∈ T, mC μ Z σ ≤ mu1 μ r Z :=
    sum_le_sum_of_subset_of_nonneg (subset_sides hT.1) fun _ _ _ => measureReal_nonneg
  rw [M_eq hP0, M_eq hP0]
  push_cast at h2
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hmT)]

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), Theorem 7.14(c), the margin.**  If
`δ (2 (n - 1) μ + 2 μ₂) < γ`, `γ` the complete-data margin of `T`, then `T` is the unique maximum
of `M` over binary stemmata. -/
theorem cutting_illegible_margin (hn : 3 ≤ n) {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T := by
  intro T' hT' hne
  have hδ0 := delta_nonneg hZ hIm hc
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : 0 ≤ δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) :=
    mul_nonneg hδ0 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn1) mu1_nonneg)
      (mul_nonneg (by norm_num) mu2_nonneg))
  have hγpos : 0 < margin r (mC μ Z) T hTne := lt_of_le_of_lt hpos hγ
  have hgap := margin_gap hT hTne (mC μ Z) T' hT'.1 hne
  rw [sum_sdiff_sub_sum_sdiff] at hgap
  have hcard : (1 : ℝ) ≤ (T \ T').card := by
    exact_mod_cast card_pos.mpr (displacement_matching hT hT'.1 hne).1
  have hge : margin r (mC μ Z) T hTne ≤ ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ := by
    nlinarith
  have := cutting_illegible hZ hIm hI01 hc hn hT hT' hP0
  linarith

variable [MeasurableSpace (Finset (PSplit n))] [MeasurableSingletonClass (Finset (PSplit n))]

include hZ hIm hI01 hc in
/-- **Proposition 7.13 (`prop:textillegible`), Theorem 7.14(c), consistency.**  Let the units
`P u` (their partial proposals) be pairwise independent and identically distributed, with unit `0`
following the model with illegibility that depends on the text (`CondIllegible`).  If
`δ (2 (n - 1) μ + 2 μ₂) < γ`, the cutting-plane estimator is consistent: the conclusion of
Theorem 7.14(b) (`Cutting.cutting_consistent`) holds for the true stemma `T`. -/
theorem cutting_illegible_consistent (hn : 3 ≤ n) {T : Finset (Finset (Fin n))}
    (hT : IsBinary r T) (hTne : T.Nonempty)
    (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B)
    (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ T', IsBinary r T' → T' ≠ T →
      W P L T' ω < W P L T ω ∧
        ∃ u ∈ range L, ∃ s ∈ P u ω, Displays T s ∧ ¬ Displays T' s) ∧
    Tendsto (fun L => μ {ω | ∀ T', IsBinary r T' → T' ≠ T → W P L T' ω < W P L T ω}ᶜ) atTop
      (𝓝 0) :=
  cutting_consistent r P hP hindep hident hB
    (cutting_illegible_margin hZ hIm hI01 hc hn hT hTne hP0 hγ)

end cutting

end Stemma.TextIllegible
