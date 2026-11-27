/-
A tolerance independent of the number of witnesses: Proposition 7.15 of the technical report
(`prop:dimfree`), which sharpens Theorem 7.14(c) (`thm:cuttingconsistency`,
`CuttingIllegible.lean`) and its version under Proposition 7.13 (`TextIllegible.lean`).

The model of one unit is that of `CuttingIllegible.lean`.  In the proof of Theorem 7.14(c) a
proposal `σ ∉ Σ(T')` is displayed by `T'` only if its restriction agrees with that of one of the
`n - 3` splits of `T'`, and the union over them gives the factor `n - 3`.  Here the union is
replaced by one combinatorial fact, stated in the language of split systems rather than of
subtrees: as `T'` is binary, `σ` crosses some split `C` of `T'` (maximality, Lemma 3.3(ii)), and
the four quadrants `σ ∩ C`, `σ ∩ Cᶜ`, `σᶜ ∩ C`, `σᶜ ∩ Cᶜ` are non-empty; if all four met the legible
set `O`, every split of `T'` with the restriction of `σ` on `O` would cross `C` on `O`, hence in
full, which `T'` forbids.  So display requires one quadrant to be wholly illegible
(`four_parts`).  These are the report's `A₁, A₂, B₁, B₂` (there `X₁, X₃ ∩ A, X₂, X₃ ∩ B` at a leaf
of `conv(A) ∩ conv(B)`; any crossing split of `T'` serves).

Formalised:
* `four_parts`: the combinatorial lemma;
* `display_prob_le`: under independent illegibility, the probability that `σ` is proposed, `σ|_O`
  is non-trivial and displayed by `T'` is at most `2 max(δ, 2δ²) m_σ`; `display_prob_le_half`:
  at most `2δ m_σ` for `δ ≤ 1/2`;
* `M_upper_dimfree`: `M(T') ≤ m(Σ(T')) + 2 max(δ, 2δ²) μ`;
* `cutting_dimfree`: for `δ ≤ 1/2`, `M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (6 μ + 2 μ₂)`;
* `cutting_dimfree_margin`: if `δ (6 μ + 2 μ₂) < γ` then `T` is the unique maximum of `M` over
  binary stemmata (no hypothesis on `δ` beyond this: `γ ≤ μ`, `margin_le_mu1`, forces `δ < 1/6`);
  `cutting_dimfree_consistent`: consistency of the cutting-plane estimator;
* under the hypothesis `CondIllegible` of Proposition 7.13: `display_prob_le_text` (`4δ m_σ`),
  `M_upper_text`, `cutting_text` (`- δ (8 μ + 2 μ₂)`), `cutting_text_margin`,
  `cutting_text_consistent`.

The conditions are stated as `δ (6 μ + 2 μ₂) < γ`, the report's `δ < γ / (6 μ + 2 μ₂)` without
dividing by a possibly zero denominator.  None of them involves `n`.
-/
import Mathlib
import StemmaLean.CuttingIllegible
import StemmaLean.TextIllegible

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped Classical

namespace Stemma.CuttingDimFree

open Stemma.Splits Stemma.Cutting Stemma.Fragmentary Stemma.GammaConf Stemma.Margin
  Stemma.CuttingIllegible

variable {n : ℕ}

/-! ### The combinatorial lemma -/

/-- If `τ` and `C` are compatible and `τ` has the restriction of `A` on `O`, one of the four
quadrants of `A` and `C` misses `O`. -/
lemma quadrant_disjoint {A C τ O : Finset (Fin n)} (hc : Compat τ C) (hs : SameRestr O τ A) :
    Disjoint (A ∩ C) O ∨ Disjoint (A ∩ Cᶜ) O ∨ Disjoint (Aᶜ ∩ C) O ∨ Disjoint (Aᶜ ∩ Cᶜ) O := by
  rw [sameRestr_iff] at hs
  unfold Compat at hc
  simp only [Finset.eq_empty_iff_forall_notMem, mem_inter, mem_compl] at hc
  simp only [Finset.disjoint_left, mem_inter, mem_compl]
  rcases hs with hs | hs <;> rcases hc with h | h | h | h
  all_goals first
    | exact Or.inl fun x hx hO => by have := hs x hO; have := h x; tauto
    | exact Or.inr (Or.inl fun x hx hO => by have := hs x hO; have := h x; tauto)
    | exact Or.inr (Or.inr (Or.inl fun x hx hO => by have := hs x hO; have := h x; tauto))
    | exact Or.inr (Or.inr (Or.inr fun x hx hO => by have := hs x hO; have := h x; tauto))

/-- **Proposition 7.15 (`prop:dimfree`), the combinatorial lemma.**  Let `T'` be (the split system
of) a binary stemma and `A` a non-trivial split not in it.  Then `A = A₁ ⊔ A₂` and `Aᶜ = B₁ ⊔ B₂`
with all four parts non-empty, such that, for every set `O` of witnesses, if the restriction of `A`
to `O` is that of a split of `T'` then one of the four parts misses `O`. -/
theorem four_parts {r : Fin n} {T' : Finset (Finset (Fin n))} (hT' : IsBinary r T')
    {A : Finset (Fin n)} (hA : A ∈ sides r) (hAT : A ∉ T') :
    ∃ A₁ A₂ B₁ B₂ : Finset (Fin n),
      A₁.Nonempty ∧ A₂.Nonempty ∧ B₁.Nonempty ∧ B₂.Nonempty ∧
      Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧ Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Aᶜ ∧
      ∀ O : Finset (Fin n), (∃ τ ∈ T', SameRestr O τ A) →
        Disjoint A₁ O ∨ Disjoint A₂ O ∨ Disjoint B₁ O ∨ Disjoint B₂ O := by
  have hside : IsSide r A := (mem_filter.mp hA).2
  obtain ⟨C, hC, hAC⟩ : ∃ C ∈ T', ¬ Compat A C := by
    by_contra h
    push Not at h
    exact hAT (maximal hT' hside h)
  unfold Compat at hAC
  push Not at hAC
  obtain ⟨h1, h2, h3, h4⟩ := hAC
  refine ⟨A ∩ C, A ∩ Cᶜ, Aᶜ ∩ C, Aᶜ ∩ Cᶜ, h1,
    h2, h3, h4,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun x hx hx' => by simp_all
  · ext x; simp only [mem_union, mem_inter, mem_compl]; tauto
  · exact Finset.disjoint_left.mpr fun x hx hx' => by simp_all
  · ext x; simp only [mem_union, mem_inter, mem_compl]; tauto
  · rintro O ⟨τ, hτ, hs⟩
    have hc : Compat τ C := by
      by_cases e : τ = C
      · rw [e]; exact compat_self C
      · exact hT'.1.2 τ hτ C hC e
    exact quadrant_disjoint hc hs

/-! ### The count of displayed proposals -/

/-- **Upper count.**  A displayed proposal is a split of `T'`, or a split outside `T'` whose
restriction is non-trivial and that of a split of `T'`. -/
lemma count_upper_dimfree {r : Fin n} (T' F : Finset (Finset (Fin n))) (hF : F ⊆ sides r)
    (O : Finset (Fin n)) :
    (count T' F O : ℝ) ≤ ∑ σ ∈ T', (if σ ∈ F then 1 else 0) +
      ∑ σ ∈ sides r \ T',
        (if σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ then 1 else 0) := by
  set H := F.filter fun σ => NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ
  have h1 : count T' F O ≤ H.card := by
    rw [count_eq]; exact card_image_le
  have h2 : (H.card : ℝ) = ∑ σ ∈ sides r,
      (if σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ then 1 else 0) := by
    have : H = (sides r).filter fun σ => σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ := by
      ext σ; simp only [H, mem_filter]
      exact ⟨fun h => ⟨hF h.1, h⟩, fun h => h.2⟩
    rw [this, card_filter]; push_cast; rfl
  have h3 := sum_filter_add_sum_filter_not (sides r) (· ∈ T')
    (fun σ => if σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ then (1 : ℝ) else 0)
  refine (Nat.cast_le.mpr h1).trans ?_
  rw [h2, ← h3, sdiff_eq_filter]
  gcongr
  calc ∑ σ ∈ (sides r).filter (· ∈ T'),
        (if σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ then (1 : ℝ) else 0)
      ≤ ∑ σ ∈ (sides r).filter (· ∈ T'), (if σ ∈ F then (1 : ℝ) else 0) :=
        sum_le_sum fun σ _ => by split_ifs <;> simp_all
    _ ≤ ∑ σ ∈ T', (if σ ∈ F then (1 : ℝ) else 0) :=
        sum_le_sum_of_subset_of_nonneg (fun σ hσ => (mem_filter.mp hσ).2)
          fun _ _ _ => by split_ifs <;> norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The event that the unit proposes `σ` and that `T'` displays its non-trivial restriction. -/
def DisplayEvent (Z : Finset (Fin n) → Ω → ℝ) (I : Fin n → Ω → ℝ)
    (T' : Finset (Finset (Fin n))) (σ : Finset (Fin n)) : Set Ω :=
  {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ ∧ ∃ τ ∈ T', SameRestr (legible I ω) τ σ}

section generic

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))

include hZ hIm in
/-- If every proposal outside `T'` is displayed with probability at most `c m_σ`, then
`M(T') ≤ m(Σ(T')) + c μ`. -/
theorem M_upper_of_display {T' : Finset (Finset (Fin n))} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ σ ∈ sides r \ T', μ.real (DisplayEvent Z I T' σ) ≤ c * mC μ Z σ) :
    ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∑ σ ∈ T', mC μ Z σ + c * mu1 μ r Z := by
  set p1 : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop := fun σ F _ => σ ∈ F
  set p2 : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun σ F O => σ ∈ F ∧ NontrivOn O σ ∧ ∃ τ ∈ T', SameRestr O τ σ
  have hpt : (fun ω => (count T' (zs r Z ω) (legible I ω) : ℝ)) ≤ fun ω =>
      ∑ σ ∈ T', ind r Z I (p1 σ) ω + ∑ σ ∈ sides r \ T', ind r Z I (p2 σ) ω := by
    intro ω
    refine (count_upper_dimfree T' (zs r Z ω) (filter_subset _ _) (legible I ω)).trans
      (le_of_eq ?_)
    simp only [ind, p1, p2]; congr! 4
  have hint1 : Integrable (fun ω => ∑ σ ∈ T', ind r Z I (p1 σ) ω) μ :=
    integrable_finsetSum _ fun σ _ => integrable_ind hZ hIm _
  have hint2 : Integrable (fun ω => ∑ σ ∈ sides r \ T', ind r Z I (p2 σ) ω) μ :=
    integrable_finsetSum _ fun σ _ => integrable_ind hZ hIm _
  have hmono : ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∫ ω, (∑ σ ∈ T', ind r Z I (p1 σ) ω + ∑ σ ∈ sides r \ T', ind r Z I (p2 σ) ω) ∂μ :=
    integral_mono (integrable_count hZ hIm T') (hint1.add hint2) hpt
  rw [integral_add hint1 hint2, integral_finsetSum _ fun σ _ => integrable_ind hZ hIm _,
    integral_finsetSum _ fun σ _ => integrable_ind hZ hIm _] at hmono
  simp only [integral_ind hZ hIm] at hmono
  have hA : ∑ σ ∈ T', μ.real {ω | p1 σ (zs r Z ω) (legible I ω)} ≤ ∑ σ ∈ T', mC μ Z σ := by
    refine sum_le_sum fun σ _ => ?_
    unfold mC
    exact measureReal_mono (fun ω h => (mem_filter.mp (show σ ∈ zs r Z ω from h)).2)
      (measure_ne_top _ _)
  have hB : ∑ σ ∈ sides r \ T', μ.real {ω | p2 σ (zs r Z ω) (legible I ω)} ≤ c * mu1 μ r Z := by
    calc ∑ σ ∈ sides r \ T', μ.real {ω | p2 σ (zs r Z ω) (legible I ω)}
        ≤ ∑ σ ∈ sides r \ T', c * mC μ Z σ := by
          refine sum_le_sum fun σ hσ => ?_
          have heq : {ω | p2 σ (zs r Z ω) (legible I ω)} = DisplayEvent Z I T' σ := by
            ext ω; simp [p2, DisplayEvent, mem_zs (mem_sdiff.mp hσ).1]
          rw [heq]; exact hb σ hσ
      _ = c * ∑ σ ∈ sides r \ T', mC μ Z σ := by rw [mul_sum]
      _ ≤ c * mu1 μ r Z := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          exact sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => measureReal_nonneg
  linarith

/-- `γ ≤ μ`: the margin of `T` is at most the expected number of splits proposed. -/
lemma margin_le_mu1 {T : Finset (Finset (Fin n))} (hT : IsBinary r T) (hTne : T.Nonempty) :
    margin r (mC μ Z) T hTne ≤ mu1 μ r Z := by
  have h := margin_gap hT hTne (mC μ Z) ∅ ⟨by simp, fun a ha => by simp at ha⟩
    (nonempty_iff_ne_empty.mp hTne).symm
  simp only [sdiff_empty, empty_sdiff, sum_empty, sub_zero] at h
  have hc : (1 : ℝ) ≤ T.card := by exact_mod_cast card_pos.mpr hTne
  have hm : ∑ σ ∈ T, mC μ Z σ ≤ mu1 μ r Z :=
    sum_le_sum_of_subset_of_nonneg (subset_sides hT.1) fun _ _ _ => measureReal_nonneg
  have h0 : 0 ≤ mu1 μ r Z := mu1_nonneg
  by_cases hg : margin r (mC μ Z) T hTne ≤ 0
  · linarith
  · push Not at hg; nlinarith

omit [IsProbabilityMeasure μ] in
/-- From the two bounds on `M` to the margin: if `M(T) - M(T') ≥ m(T) - m(Σ(T')) - ε` for every
binary `T'` and `ε < γ`, then `T` is the unique maximum of `M`. -/
lemma unique_max_of_gap {T : Finset (Finset (Fin n))} (hT : IsBinary r T) (hTne : T.Nonempty)
    {P : ℕ → Ω → Finset (PSplit n)} {ε : ℝ}
    (hgap : ∀ T', IsBinary r T' → ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ - ε ≤ M μ P T - M μ P T')
    (hε : 0 ≤ ε) (hγ : ε < margin r (mC μ Z) T hTne) :
    ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T := by
  intro T' hT' hne
  have hγpos : 0 < margin r (mC μ Z) T hTne := lt_of_le_of_lt hε hγ
  have hg := margin_gap hT hTne (mC μ Z) T' hT'.1 hne
  rw [sum_sdiff_sub_sum_sdiff] at hg
  have hcard : (1 : ℝ) ≤ (T \ T').card := by
    exact_mod_cast card_pos.mpr (displacement_matching hT hT'.1 hne).1
  have hge : margin r (mC μ Z) T hTne ≤ ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ := by
    nlinarith
  have := hgap T' hT'
  linarith

end generic

/-! ### Independent illegibility -/

section indep

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1)
  (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
  (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- A set of witnesses missing the legible ones is wholly illegible. -/
lemma ill_of_disjoint (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1) {ω : Ω} {X : Finset (Fin n)}
    (h : Disjoint X (legible I ω)) : ∀ x ∈ X, I x ω = 1 := by
  intro x hx
  rcases hI01 x ω with h0 | h1
  · exact absurd (by simp [legible, h0] : x ∈ legible I ω) (Finset.disjoint_left.mp h hx)
  · exact h1

include hZ hindZI hindI hδ in
/-- The unit proposes `σ` and every witness of `X` is illegible: probability `≤ m_σ δ^{|X|}`. -/
lemma meas_ill_pow (σ X : Finset (Fin n)) :
    μ.real {ω | Z σ ω = 1 ∧ ∀ x ∈ X, I x ω = 1} ≤ mC μ Z σ * δ ^ X.card := by
  have hs : MeasurableSet {f : Finset (Fin n) → ℝ | f σ = 1} :=
    measurableSet_eq_fun (measurable_pi_apply σ) measurable_const
  have h : μ.real {ω | Z σ ω = 1 ∧ ∀ x ∈ X, I x ω = 1} =
      μ.real {ω | Z σ ω = 1} * ∏ x ∈ X, μ.real {ω | I x ω = 1} :=
    meas_inter_ill hZ hindZI hindI _ hs X
  rw [h, mC]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  calc ∏ x ∈ X, μ.real {ω | I x ω = 1} ≤ ∏ _x ∈ X, δ :=
        prod_le_prod₀ (fun _ _ => measureReal_nonneg) fun x _ => hδ x
    _ = δ ^ X.card := prod_const δ

include hZ hI01 hindZI hindI hδ in
/-- One side `S = X ⊔ Y`: the part `X` wholly illegible while `S` keeps two legible witnesses
needs `|Y| ≥ 2`, and has probability at most `m_σ δ^{|X|}`. -/
lemma side_le (σ S X Y : Finset (Fin n)) (hXY : X ∪ Y = S) :
    μ.real {ω | Z σ ω = 1 ∧ 2 ≤ (S ∩ legible I ω).card ∧ Disjoint X (legible I ω)} ≤
      mC μ Z σ * (if 2 ≤ Y.card then δ ^ X.card else 0) := by
  split_ifs with hY
  · calc _ ≤ μ.real {ω | Z σ ω = 1 ∧ ∀ x ∈ X, I x ω = 1} :=
          measureReal_mono (by
            rintro ω ⟨h1, -, h3⟩; exact ⟨h1, ill_of_disjoint hI01 h3⟩) (measure_ne_top _ _)
      _ ≤ _ := meas_ill_pow hZ hindZI hindI hδ σ X
  · have he : {ω | Z σ ω = 1 ∧ 2 ≤ (S ∩ legible I ω).card ∧ Disjoint X (legible I ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, h2, h3⟩
      have hsub : S ∩ legible I ω ⊆ Y := by
        intro x hx
        obtain ⟨hxS, hxO⟩ := mem_inter.mp hx
        rw [← hXY] at hxS
        rcases mem_union.mp hxS with h | h
        · exact absurd hxO (Finset.disjoint_left.mp h3 h)
        · exact h
      have := card_le_card hsub
      omega
    rw [he]; simp

/-- The two parts of one side contribute at most `max(δ, 2δ²)`. -/
lemma pair_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (if 2 ≤ l then δ ^ k else 0) + (if 2 ≤ k then δ ^ l else 0) ≤ max δ (2 * δ ^ 2) := by
  have hp : ∀ m, 2 ≤ m → δ ^ m ≤ δ ^ 2 := fun m hm => pow_le_pow_of_le_one h0 h1 hm
  rcases Nat.lt_or_ge k 2 with hk2 | hk2 <;> rcases Nat.lt_or_ge l 2 with hl2 | hl2
  · simp only [show ¬ 2 ≤ l by omega, show ¬ 2 ≤ k by omega, ↓reduceIte, add_zero]
    exact h0.trans (le_max_left _ _)
  · obtain rfl : k = 1 := by omega
    simp only [hl2, show ¬ 2 ≤ 1 by omega, ↓reduceIte, add_zero, pow_one]
    exact le_max_left _ _
  · obtain rfl : l = 1 := by omega
    simp only [hk2, show ¬ 2 ≤ 1 by omega, ↓reduceIte, zero_add, pow_one]
    exact le_max_left _ _
  · simp only [hl2, hk2, ↓reduceIte]
    linarith [hp k hk2, hp l hl2, le_max_right δ (2 * δ ^ 2)]

include hZ hI01 hindZI hindI hδ in
/-- **Proposition 7.15 (`prop:dimfree`), the display probability.**  Under independent
illegibility, for a binary stemma `T'` and a non-trivial split `σ ∉ Σ(T')`, the probability that
the unit proposes `σ`, that `σ|_O` is non-trivial and that `T'` displays it is at most
`2 max(δ, 2δ²) m_σ`: whatever the number of witnesses. -/
theorem display_prob_le {T' : Finset (Finset (Fin n))} (hT' : IsBinary r T')
    {σ : Finset (Fin n)} (hσ : σ ∈ sides r) (hσT : σ ∉ T') :
    μ.real (DisplayEvent Z I T' σ) ≤ 2 * max δ (2 * δ ^ 2) * mC μ Z σ := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  have hm0 : 0 ≤ mC μ Z σ := measureReal_nonneg
  by_cases hδ1 : 1 ≤ δ
  · have h1 : μ.real (DisplayEvent Z I T' σ) ≤ mC μ Z σ :=
      measureReal_mono (fun ω h => h.1) (measure_ne_top _ _)
    have h2 : 1 ≤ max δ (2 * δ ^ 2) := hδ1.trans (le_max_left _ _)
    nlinarith
  push Not at hδ1
  obtain ⟨A₁, A₂, B₁, B₂, hA₁, hA₂, hB₁, hB₂, -, hA, -, hB, hd⟩ := four_parts hT' hσ hσT
  set E : Finset (Fin n) → Finset (Fin n) → Set Ω := fun S X =>
    {ω | Z σ ω = 1 ∧ 2 ≤ (S ∩ legible I ω).card ∧ Disjoint X (legible I ω)}
  have hsub : DisplayEvent Z I T' σ ⊆ ((E σ A₁ ∪ E σ A₂) ∪ E σᶜ B₁) ∪ E σᶜ B₂ := by
    rintro ω ⟨hz, ⟨hn1, hn2⟩, hs⟩
    rcases hd _ hs with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hz, hn1, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hz, hn1, h⟩))
    · exact Or.inl (Or.inr ⟨hz, hn2, h⟩)
    · exact Or.inr ⟨hz, hn2, h⟩
  have e1 := side_le hZ hI01 hindZI hindI hδ σ σ A₁ A₂ hA
  have e2 := side_le hZ hI01 hindZI hindI hδ σ σ A₂ A₁ ((union_comm _ _).trans hA)
  have e3 := side_le hZ hI01 hindZI hindI hδ σ σᶜ B₁ B₂ hB
  have e4 := side_le hZ hI01 hindZI hindI hδ σ σᶜ B₂ B₁ ((union_comm _ _).trans hB)
  have pA := pair_le hδ0 hδ1.le (card_pos.mpr hA₁) (card_pos.mpr hA₂)
  have pB := pair_le hδ0 hδ1.le (card_pos.mpr hB₁) (card_pos.mpr hB₂)
  calc μ.real (DisplayEvent Z I T' σ)
      ≤ μ.real (((E σ A₁ ∪ E σ A₂) ∪ E σᶜ B₁) ∪ E σᶜ B₂) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (E σ A₁) + μ.real (E σ A₂) + μ.real (E σᶜ B₁) + μ.real (E σᶜ B₂) := by
        have u1 := measureReal_union_le (μ := μ) ((E σ A₁ ∪ E σ A₂) ∪ E σᶜ B₁) (E σᶜ B₂)
        have u2 := measureReal_union_le (μ := μ) (E σ A₁ ∪ E σ A₂) (E σᶜ B₁)
        have u3 := measureReal_union_le (μ := μ) (E σ A₁) (E σ A₂)
        linarith
    _ ≤ mC μ Z σ * ((if 2 ≤ A₂.card then δ ^ A₁.card else 0) +
          (if 2 ≤ A₁.card then δ ^ A₂.card else 0)) +
        mC μ Z σ * ((if 2 ≤ B₂.card then δ ^ B₁.card else 0) +
          (if 2 ≤ B₁.card then δ ^ B₂.card else 0)) := by
        simp only [E] at e1 e2 e3 e4 ⊢
        linarith
    _ ≤ mC μ Z σ * max δ (2 * δ ^ 2) + mC μ Z σ * max δ (2 * δ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left pA hm0) (mul_le_mul_of_nonneg_left pB hm0)
    _ = 2 * max δ (2 * δ ^ 2) * mC μ Z σ := by ring

lemma max_eq_of_le_half {δ : ℝ} (h0 : 0 ≤ δ) (h : δ ≤ 1 / 2) : max δ (2 * δ ^ 2) = δ :=
  max_eq_left (by nlinarith)

include hZ hI01 hindZI hindI hδ in
/-- **Proposition 7.15, the display probability for `δ ≤ 1/2`:** at most `2 δ m_σ`. -/
theorem display_prob_le_half (hδ2 : δ ≤ 1 / 2) {T' : Finset (Finset (Fin n))}
    (hT' : IsBinary r T') {σ : Finset (Fin n)} (hσ : σ ∈ sides r) (hσT : σ ∉ T') :
    μ.real (DisplayEvent Z I T' σ) ≤ 2 * δ * mC μ Z σ := by
  have h := display_prob_le hZ hI01 hindZI hindI hδ hT' hσ hσT
  rwa [max_eq_of_le_half (measureReal_nonneg.trans (hδ r)) hδ2] at h

include hZ hIm hI01 hindZI hindI hδ in
/-- **Proposition 7.15, rival stemma.**  `M(T') ≤ m(Σ(T')) + 2 max(δ, 2δ²) μ`, for every binary
`T'`. -/
theorem M_upper_dimfree {T' : Finset (Finset (Fin n))} (hT' : IsBinary r T') :
    ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∑ σ ∈ T', mC μ Z σ + 2 * max δ (2 * δ ^ 2) * mu1 μ r Z := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  exact M_upper_of_display hZ hIm (by positivity) fun σ hσ =>
    display_prob_le hZ hI01 hindZI hindI hδ hT' (mem_sdiff.mp hσ).1 (mem_sdiff.mp hσ).2

include hZ hIm hI01 hindZI hindI hδ in
/-- **Proposition 7.15 (`prop:dimfree`), the inequality.**  Under independent illegibility with
`δ ≤ 1/2`, for binary stemmata `T` and `T'`,
`M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (6 μ + 2 μ₂)`, whatever the number of witnesses. -/
theorem cutting_dimfree (hδ2 : δ ≤ 1 / 2) {T T' : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hT' : IsBinary r T') {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I) :
    ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ - δ * (6 * mu1 μ r Z + 2 * mu2 μ r Z) ≤
      M μ P T - M μ P T' := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  have h1 := M_lower hZ hIm hI01 hindZI hindI hδ (subset_sides hT.1)
  have h2 := M_upper_dimfree hZ hIm hI01 hindZI hindI hδ hT'
  rw [max_eq_of_le_half hδ0 hδ2] at h2
  have hmT : ∑ σ ∈ T, mC μ Z σ ≤ mu1 μ r Z :=
    sum_le_sum_of_subset_of_nonneg (subset_sides hT.1) fun _ _ _ => measureReal_nonneg
  rw [M_eq hP0, M_eq hP0]
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hmT)]

include hZ hIm hI01 hindZI hindI hδ in
/-- **Proposition 7.15 (`prop:dimfree`), the margin.**  Under independent illegibility, if
`δ (6 μ + 2 μ₂) < γ`, `γ` the complete-data margin of `T`, then `T` is the unique maximum of `M`
over binary stemmata, whatever the number of witnesses.  (The condition forces `δ < 1/6`, since
`γ ≤ μ`.) -/
theorem cutting_dimfree_margin {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (6 * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  have h1 : 0 ≤ mu1 μ r Z := mu1_nonneg
  have h2 : 0 ≤ mu2 μ r Z := mu2_nonneg
  have hle := margin_le_mu1 (μ := μ) (Z := Z) hT hTne
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hδ0 h2]
  exact unique_max_of_gap hT hTne
    (fun T' hT' => cutting_dimfree hZ hIm hI01 hindZI hindI hδ hδ2 hT hT' hP0)
    (by positivity) hγ

variable [MeasurableSpace (Finset (PSplit n))] [MeasurableSingletonClass (Finset (PSplit n))]

include hZ hIm hI01 hindZI hindI hδ in
/-- **Proposition 7.15 (`prop:dimfree`), consistency.**  Let the units `P u` (their partial
proposals) be pairwise independent and identically distributed, with unit `0` following the
independent illegibility model.  If `δ (6 μ + 2 μ₂) < γ`, the cutting-plane estimator is
consistent: the conclusion of Theorem 7.14(b) (`Cutting.cutting_consistent`) holds for the true
stemma `T`. -/
theorem cutting_dimfree_consistent {T : Finset (Finset (Fin n))}
    (hT : IsBinary r T) (hTne : T.Nonempty)
    (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B)
    (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (6 * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ T', IsBinary r T' → T' ≠ T →
      W P L T' ω < W P L T ω ∧
        ∃ u ∈ range L, ∃ s ∈ P u ω, Displays T s ∧ ¬ Displays T' s) ∧
    Tendsto (fun L => μ {ω | ∀ T', IsBinary r T' → T' ≠ T → W P L T' ω < W P L T ω}ᶜ) atTop
      (𝓝 0) :=
  cutting_consistent r P hP hindep hident hB
    (cutting_dimfree_margin hZ hIm hI01 hindZI hindI hδ hT hTne hP0 hγ)

end indep

/-! ### Illegibility that depends on the text (Proposition 7.13) -/

section text

open Stemma.TextIllegible

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1) (hc : CondIllegible μ r Z I δ)

include hZ hIm hI01 hc in
/-- **Proposition 7.15 under Proposition 7.13, the display probability.**  If each witness is
illegible with conditional probability at most `δ` given the unit's complete proposals, the
probability that the unit proposes `σ ∉ Σ(T')` and that `T'` displays its non-trivial restriction
is at most `4 δ m_σ`. -/
theorem display_prob_le_text {T' : Finset (Finset (Fin n))} (hT' : IsBinary r T')
    {σ : Finset (Fin n)} (hσ : σ ∈ sides r) (hσT : σ ∉ T') :
    μ.real (DisplayEvent Z I T' σ) ≤ 4 * δ * mC μ Z σ := by
  obtain ⟨A₁, A₂, B₁, B₂, hA₁, hA₂, hB₁, hB₂, -, -, -, -, hd⟩ := four_parts hT' hσ hσT
  set E : Finset (Fin n) → Set Ω := fun X =>
    {ω | (fun G => σ ∈ G) (zs r Z ω) ∧ ∀ x ∈ X, I x ω = 1}
  have hm : μ.real {ω | (fun G => σ ∈ G) (zs r Z ω)} = mC μ Z σ := by
    unfold mC; congr 1; ext ω; simp [mem_zs hσ]
  have hE : ∀ X : Finset (Fin n), X.Nonempty → μ.real (E X) ≤ δ * mC μ Z σ := fun X hX => by
    rw [← hm]; exact ill_set_le hZ hIm hc (fun G => σ ∈ G) hX
  have hsub : DisplayEvent Z I T' σ ⊆ ((E A₁ ∪ E A₂) ∪ E B₁) ∪ E B₂ := by
    rintro ω ⟨hz, -, hs⟩
    have hz' : σ ∈ zs r Z ω := (mem_zs hσ ω).mpr hz
    rcases hd _ hs with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hz', ill_of_disjoint hI01 h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hz', ill_of_disjoint hI01 h⟩))
    · exact Or.inl (Or.inr ⟨hz', ill_of_disjoint hI01 h⟩)
    · exact Or.inr ⟨hz', ill_of_disjoint hI01 h⟩
  calc μ.real (DisplayEvent Z I T' σ)
      ≤ μ.real (((E A₁ ∪ E A₂) ∪ E B₁) ∪ E B₂) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (E A₁) + μ.real (E A₂) + μ.real (E B₁) + μ.real (E B₂) := by
        have u1 := measureReal_union_le (μ := μ) ((E A₁ ∪ E A₂) ∪ E B₁) (E B₂)
        have u2 := measureReal_union_le (μ := μ) (E A₁ ∪ E A₂) (E B₁)
        have u3 := measureReal_union_le (μ := μ) (E A₁) (E A₂)
        linarith
    _ ≤ 4 * δ * mC μ Z σ := by linarith [hE _ hA₁, hE _ hA₂, hE _ hB₁, hE _ hB₂]

include hZ hIm hI01 hc in
/-- **Proposition 7.15 under Proposition 7.13, rival stemma.**  `M(T') ≤ m(Σ(T')) + 4 δ μ`. -/
theorem M_upper_text {T' : Finset (Finset (Fin n))} (hT' : IsBinary r T') :
    ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∑ σ ∈ T', mC μ Z σ + 4 * δ * mu1 μ r Z := by
  have hδ0 := delta_nonneg hZ hIm hc
  exact M_upper_of_display hZ hIm (by positivity) fun σ hσ =>
    display_prob_le_text hZ hIm hI01 hc hT' (mem_sdiff.mp hσ).1 (mem_sdiff.mp hσ).2

include hZ hIm hI01 hc in
/-- **Proposition 7.15 under Proposition 7.13, the inequality.**  For binary stemmata `T` and
`T'`, `M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (8 μ + 2 μ₂)`. -/
theorem cutting_text {T T' : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hT' : IsBinary r T') {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I) :
    ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ - δ * (8 * mu1 μ r Z + 2 * mu2 μ r Z) ≤
      M μ P T - M μ P T' := by
  have hδ0 := delta_nonneg hZ hIm hc
  have h1 := TextIllegible.M_lower hZ hIm hI01 hc (subset_sides hT.1)
  have h2 := M_upper_text hZ hIm hI01 hc hT'
  have hmT : ∑ σ ∈ T, mC μ Z σ ≤ mu1 μ r Z :=
    sum_le_sum_of_subset_of_nonneg (subset_sides hT.1) fun _ _ _ => measureReal_nonneg
  rw [M_eq hP0, M_eq hP0]
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hmT)]

include hZ hIm hI01 hc in
/-- **Proposition 7.15 under Proposition 7.13, the margin.**  If `δ (8 μ + 2 μ₂) < γ`, then `T`
is the unique maximum of `M` over binary stemmata, whatever the number of witnesses. -/
theorem cutting_text_margin {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (8 * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T := by
  have hδ0 := delta_nonneg hZ hIm hc
  have h1 : 0 ≤ mu1 μ r Z := mu1_nonneg
  have h2 : 0 ≤ mu2 μ r Z := mu2_nonneg
  exact unique_max_of_gap hT hTne (fun T' hT' => cutting_text hZ hIm hI01 hc hT hT' hP0)
    (by positivity) hγ

variable [MeasurableSpace (Finset (PSplit n))] [MeasurableSingletonClass (Finset (PSplit n))]

include hZ hIm hI01 hc in
/-- **Proposition 7.15 under Proposition 7.13, consistency.**  With i.i.d. units as in
`cutting_dimfree_consistent` and unit `0` satisfying `CondIllegible`, if `δ (8 μ + 2 μ₂) < γ` the
cutting-plane estimator is consistent. -/
theorem cutting_text_consistent {T : Finset (Finset (Fin n))}
    (hT : IsBinary r T) (hTne : T.Nonempty)
    (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B)
    (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (8 * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ T', IsBinary r T' → T' ≠ T →
      W P L T' ω < W P L T ω ∧
        ∃ u ∈ range L, ∃ s ∈ P u ω, Displays T s ∧ ¬ Displays T' s) ∧
    Tendsto (fun L => μ {ω | ∀ T', IsBinary r T' → T' ≠ T → W P L T' ω < W P L T ω}ᶜ) atTop
      (𝓝 0) :=
  cutting_consistent r P hP hindep hident hB
    (cutting_text_margin hZ hIm hI01 hc hT hTne hP0 hγ)

end text

end Stemma.CuttingDimFree
