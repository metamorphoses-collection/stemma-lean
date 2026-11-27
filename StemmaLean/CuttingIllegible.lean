/-
Illegible witnesses and the cutting-plane estimator: Theorem 7.14(c) of the technical report
(`thm:cuttingconsistency`).

The model of one unit is that of `Fragmentary.lean`: `Z σ ∈ {0,1}` says that the complete unit
proposes the non-trivial split `σ` (a side away from `r`), `I x ∈ {0,1}` that witness `x` is
illegible, independently across witnesses with probability at most `δ` and independently of the
readings.  On its legible witnesses `O` the unit proposes the partial splits `σ|_O` of its
complete proposals that are non-trivial on `O`.  They are recorded as partial splits
(`Stemma.PSplit`, oriented canonically by `canon`, so that each unordered partial split is
recorded once), and `M(T')` is the expected number of them that the binary stemma `T'` displays:
`Cutting.M`, the quantity of Theorem 7.14(b), for the units of this model.

Formalised:
* `M_lower`: `M(T) ≥ (1 - 4δ) m(T) - 2δ μ₂`, `μ₂` the expected number of pairs of splits proposed
  by a complete unit;
* `M_upper`: `M(T') ≤ m(Σ(T')) + 2 (n - 3) δ μ`, `μ` the expected number of splits proposed;
* `cutting_illegible`: the inequality of (c),
  `M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (2 (n - 1) μ + 2 μ₂)`;
* `cutting_illegible_margin`: if `δ (2 (n - 1) μ + 2 μ₂) < γ`, the complete-data margin, then `T`
  is the unique maximum of `M` over binary stemmata;
* `cutting_illegible_consistent`: with i.i.d. units following the model, Theorem 7.14(b) then
  gives consistency of the cutting-plane estimator.

The sufficient condition is stated as `δ (2 (n - 1) μ + 2 μ₂) < γ`, which is the report's
`δ < γ / (2 (n - 1) μ + 2 μ₂)` without dividing by a possibly zero denominator.
-/
import Mathlib
import StemmaLean.Fragmentary
import StemmaLean.Cutting

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped Classical

namespace Stemma.CuttingIllegible

open Stemma.Splits Stemma.Cutting Stemma.Fragmentary Stemma.GammaConf Stemma.Margin

variable {n : ℕ}

/-! ### Partial splits, recorded once -/

/-- The partial split `A ∩ O | O \ A`, oriented so that its recorded side avoids the least witness
of `O`; both orientations of one unordered partial split give the same record. -/
noncomputable def canon (O A : Finset (Fin n)) : PSplit n :=
  if h : O.Nonempty then
    (if O.min' h ∈ A then ⟨O, O \ A, sdiff_subset⟩ else ⟨O, A ∩ O, inter_subset_right⟩)
  else ⟨O, ∅, empty_subset _⟩

lemma canon_dom (O A : Finset (Fin n)) : (canon O A).dom = O := by
  unfold canon; split_ifs <;> rfl

lemma mem_canon_side {O : Finset (Fin n)} (hO : O.Nonempty) (A : Finset (Fin n)) (x : Fin n) :
    x ∈ (canon O A).side ↔ x ∈ O ∧ (x ∈ A ↔ O.min' hO ∉ A) := by
  unfold canon
  simp only [hO, ↓reduceDIte]
  by_cases ha : O.min' hO ∈ A
  · simp [ha]
  · simp [ha, and_comm]

lemma psplit_eq_of_side {s t : PSplit n} (hd : s.dom = t.dom) (hs : s.side = t.side) : s = t := by
  cases s; cases t; simp_all

lemma sameRestr_iff (O A B : Finset (Fin n)) :
    SameRestr O A B ↔ (∀ x ∈ O, x ∈ A ↔ x ∈ B) ∨ (∀ x ∈ O, x ∈ A ↔ x ∉ B) := by
  unfold SameRestr
  simp only [Finset.ext_iff, mem_inter, mem_compl]
  constructor
  · rintro (h | h)
    · exact Or.inl fun x hx => by have := h x; tauto
    · exact Or.inr fun x hx => by have := h x; tauto
  · rintro (h | h)
    · exact Or.inl fun x => by by_cases hx : x ∈ O <;> simp [hx, h x]
    · exact Or.inr fun x => by by_cases hx : x ∈ O <;> simp [hx, h x]

lemma sameRestr_symm {O A B : Finset (Fin n)} (h : SameRestr O A B) : SameRestr O B A := by
  rw [sameRestr_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl fun x hx => (h x hx).symm
  · exact Or.inr fun x hx => by have := h x hx; tauto

/-- The canonical records agree iff the restrictions agree. -/
lemma canon_eq_iff {O : Finset (Fin n)} (hO : O.Nonempty) (A B : Finset (Fin n)) :
    canon O A = canon O B ↔ SameRestr O A B := by
  set a := O.min' hO
  have haO : a ∈ O := O.min'_mem hO
  have hside : canon O A = canon O B ↔
      ∀ x ∈ O, ((x ∈ A ↔ a ∉ A) ↔ (x ∈ B ↔ a ∉ B)) := by
    constructor
    · intro h x hx
      have := congrArg (fun s => x ∈ s.side) h
      simp only [mem_canon_side hO] at this
      tauto
    · intro h
      refine psplit_eq_of_side (by rw [canon_dom, canon_dom]) ?_
      ext x
      rw [mem_canon_side hO, mem_canon_side hO]
      by_cases hx : x ∈ O
      · have := h x hx; tauto
      · simp [hx]
  rw [hside, sameRestr_iff]
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B
  · constructor
    · intro h; exact Or.inl fun x hx => by have := h x hx; tauto
    · rintro (h | h)
      · intro x hx; have := h x hx; tauto
      · exact absurd ((h a haO).mp hA) (not_not.mpr hB)
  · constructor
    · intro h; exact Or.inr fun x hx => by have := h x hx; tauto
    · rintro (h | h)
      · exact absurd ((h a haO).mp hA) hB
      · intro x hx; have := h x hx; tauto
  · constructor
    · intro h; exact Or.inr fun x hx => by have := h x hx; tauto
    · rintro (h | h)
      · exact absurd ((h a haO).mpr hB) hA
      · intro x hx; have := h x hx; tauto
  · constructor
    · intro h; exact Or.inl fun x hx => by have := h x hx; tauto
    · rintro (h | h)
      · intro x hx; have := h x hx; tauto
      · exact absurd ((h a haO).mpr hB) hA

/-- A split system displays the record of `A|_O` iff one of its splits has the same restriction. -/
lemma displays_canon {O : Finset (Fin n)} (hO : O.Nonempty) (T : Finset (Finset (Fin n)))
    (A : Finset (Fin n)) :
    Displays T (canon O A) ↔ ∃ τ ∈ T, SameRestr O τ A := by
  unfold Displays Restricts Extends
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  rw [canon_dom, sameRestr_iff]
  simp only [Finset.ext_iff, mem_inter, mem_compl, mem_canon_side hO]
  set a := O.min' hO
  have haO : a ∈ O := O.min'_mem hO
  constructor
  · rintro (h | h)
    · by_cases hA : a ∈ A
      · exact Or.inr fun x hx => by have := h x; tauto
      · exact Or.inl fun x hx => by have := h x; tauto
    · by_cases hA : a ∈ A
      · exact Or.inl fun x hx => by have := h x; tauto
      · exact Or.inr fun x hx => by have := h x; tauto
  · rintro (h | h)
    · by_cases hA : a ∈ A
      · right; intro x; by_cases hx : x ∈ O
        · have := h x hx; tauto
        · tauto
      · left; intro x; by_cases hx : x ∈ O
        · have := h x hx; tauto
        · tauto
    · by_cases hA : a ∈ A
      · left; intro x; by_cases hx : x ∈ O
        · have := h x hx; tauto
        · tauto
      · right; intro x; by_cases hx : x ∈ O
        · have := h x hx; tauto
        · tauto

/-! ### The count of displayed proposals, deterministically -/

/-- The partial splits proposed by a unit with complete proposals `F` and legible witnesses `O`. -/
noncomputable def props (F : Finset (Finset (Fin n))) (O : Finset (Fin n)) : Finset (PSplit n) :=
  (F.filter (NontrivOn O)).image (canon O)

/-- The number of them displayed by `T`. -/
noncomputable def count (T F : Finset (Finset (Fin n))) (O : Finset (Fin n)) : ℕ :=
  ((props F O).filter (Displays T)).card

lemma nonempty_of_nontrivOn {O A : Finset (Fin n)} (h : NontrivOn O A) : O.Nonempty := by
  obtain ⟨x, hx⟩ := card_pos.mp (by have := h.1; omega : 0 < (A ∩ O).card)
  exact ⟨x, (mem_inter.mp hx).2⟩

lemma count_eq (T F : Finset (Finset (Fin n))) (O : Finset (Fin n)) :
    count T F O =
      ((F.filter fun σ => NontrivOn O σ ∧ ∃ τ ∈ T, SameRestr O τ σ).image (canon O)).card := by
  unfold count props
  rw [filter_image, filter_filter]
  congr 2
  refine filter_congr fun σ _ => and_congr_right fun h => ?_
  exact displays_canon (nonempty_of_nontrivOn h) T σ

/-- Collapsing by a map loses at most the number of unordered pairs it identifies:
`2 |G| ≤ 2 |f G| + #{ordered pairs of distinct elements with the same image}`. -/
lemma two_card_le {α β : Type*} [DecidableEq α] [DecidableEq β] (G : Finset α) (f : α → β) :
    2 * G.card ≤ 2 * (G.image f).card + (G.offDiag.filter fun p => f p.1 = f p.2).card := by
  have h1 : G.card = ∑ b ∈ G.image f, (G.filter fun a => f a = b).card :=
    card_eq_sum_card_fiberwise fun a ha => mem_image_of_mem f ha
  have h2 : (G.offDiag.filter fun p => f p.1 = f p.2).card =
      ∑ b ∈ G.image f, ((G.filter fun a => f a = b).offDiag).card := by
    rw [card_eq_sum_card_fiberwise (f := fun p => f p.1) (t := G.image f) fun p hp =>
      mem_image_of_mem f (mem_offDiag.mp (mem_filter.mp hp).1).1]
    refine sum_congr rfl fun b _ => congrArg card ?_
    ext p
    simp only [mem_filter, mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩; exact ⟨⟨h1, h5⟩, ⟨h2, h4 ▸ h5⟩, h3⟩
    · rintro ⟨⟨h1, h5⟩, ⟨h2, h6⟩, h3⟩; exact ⟨⟨⟨h1, h2, h3⟩, h5.trans h6.symm⟩, h5⟩
  rw [h1, h2, card_eq_sum_ones (G.image f), mul_sum, mul_sum, mul_one, ← sum_add_distrib]
  refine sum_le_sum fun b hb => ?_
  rw [offDiag_card]
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  have hk : 1 ≤ (G.filter fun x => f x = f a).card := card_pos.mpr ⟨a, by simp [ha]⟩
  set k := (G.filter fun x => f x = f a).card
  have hkk : k ≤ k * k := Nat.le_mul_self k
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k; simp
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k; simp
    · have : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk3
      omega

/-- **Lower count.**  The true proposals still non-trivial on `O` are displayed by `T`; two of them
give one partial split only when their restrictions agree. -/
lemma count_lower (T F : Finset (Finset (Fin n))) (O : Finset (Fin n)) :
    2 * (T.filter fun σ => σ ∈ F ∧ NontrivOn O σ).card ≤
      2 * count T F O + (T.offDiag.filter fun p => p.1 ∈ F ∧ p.2 ∈ F ∧ SameRestr O p.1 p.2).card := by
  set G := T.filter fun σ => σ ∈ F ∧ NontrivOn O σ
  have h := two_card_le G (canon O)
  have himg : (G.image (canon O)).card ≤ count T F O := by
    rw [count_eq]
    refine card_le_card (image_subset_image fun σ hσ => ?_)
    obtain ⟨hσT, hσF, hnt⟩ := (by simpa [G] using hσ : σ ∈ T ∧ σ ∈ F ∧ NontrivOn O σ)
    exact mem_filter.mpr ⟨hσF, hnt, σ, hσT, Or.inl rfl⟩
  have hpairs : (G.offDiag.filter fun p => canon O p.1 = canon O p.2).card ≤
      (T.offDiag.filter fun p => p.1 ∈ F ∧ p.2 ∈ F ∧ SameRestr O p.1 p.2).card := by
    refine card_le_card fun p hp => ?_
    obtain ⟨hpG, heq⟩ := mem_filter.mp hp
    obtain ⟨h1, h2, h3⟩ := mem_offDiag.mp hpG
    obtain ⟨h1T, h1F, h1n⟩ := (by simpa [G] using h1 : p.1 ∈ T ∧ p.1 ∈ F ∧ NontrivOn O p.1)
    obtain ⟨h2T, h2F, -⟩ := (by simpa [G] using h2 : p.2 ∈ T ∧ p.2 ∈ F ∧ NontrivOn O p.2)
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨h1T, h2T, h3⟩, h1F, h2F,
      (canon_eq_iff (nonempty_of_nontrivOn h1n) _ _).mp heq⟩
  omega

/-- **Upper count.**  A displayed proposal is a split of `T'`, or has the restriction of one. -/
lemma count_upper {r : Fin n} (T' F : Finset (Finset (Fin n))) (hF : F ⊆ sides r)
    (O : Finset (Fin n)) :
    (count T' F O : ℝ) ≤ ∑ σ ∈ T', (if σ ∈ F then 1 else 0) +
      ∑ σ ∈ sides r \ T', ∑ τ ∈ T', (if σ ∈ F ∧ SameRestr O τ σ then 1 else 0) := by
  set H := F.filter fun σ => ∃ τ ∈ T', SameRestr O τ σ
  have h1 : count T' F O ≤ H.card := by
    rw [count_eq]
    exact (card_image_le).trans (card_le_card fun σ hσ =>
      mem_filter.mpr ⟨(mem_filter.mp hσ).1, (mem_filter.mp hσ).2.2⟩)
  have h2 : (H.card : ℝ) = ∑ σ ∈ sides r,
      (if σ ∈ F ∧ ∃ τ ∈ T', SameRestr O τ σ then 1 else 0) := by
    have : H = (sides r).filter fun σ => σ ∈ F ∧ ∃ τ ∈ T', SameRestr O τ σ := by
      ext σ; simp only [H, mem_filter]
      exact ⟨fun h => ⟨hF h.1, h⟩, fun h => h.2⟩
    rw [this, card_filter]; push_cast; rfl
  have h3 := sum_filter_add_sum_filter_not (sides r) (· ∈ T')
    (fun σ => if σ ∈ F ∧ ∃ τ ∈ T', SameRestr O τ σ then (1 : ℝ) else 0)
  refine (Nat.cast_le.mpr h1).trans ?_
  rw [h2, ← h3]
  gcongr with σ hσ σ hσ
  · calc ∑ σ ∈ (sides r).filter (· ∈ T'),
          (if σ ∈ F ∧ ∃ τ ∈ T', SameRestr O τ σ then (1 : ℝ) else 0)
        ≤ ∑ σ ∈ (sides r).filter (· ∈ T'), (if σ ∈ F then (1 : ℝ) else 0) :=
          sum_le_sum fun σ _ => by split_ifs <;> simp_all
      _ ≤ ∑ σ ∈ T', (if σ ∈ F then (1 : ℝ) else 0) :=
          sum_le_sum_of_subset_of_nonneg (fun σ hσ => (mem_filter.mp hσ).2)
            fun _ _ _ => by split_ifs <;> norm_num
  · rw [sdiff_eq_filter]
    refine sum_le_sum fun σ _ => ?_
    split_ifs with h
    · obtain ⟨hσF, τ, hτ, hs⟩ := h
      calc (1 : ℝ) = if σ ∈ F ∧ SameRestr O τ σ then 1 else 0 := by simp [hσF, hs]
        _ ≤ _ := single_le_sum (f := fun τ => if σ ∈ F ∧ SameRestr O τ σ then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) hτ
    · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-! ### The model of one unit -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The complete proposals of the unit. -/
noncomputable def zs (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) (ω : Ω) : Finset (Finset (Fin n)) :=
  (sides r).filter fun σ => Z σ ω = 1

/-- The partial splits proposed by the unit, each recorded once. -/
noncomputable def unitProps (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) (I : Fin n → Ω → ℝ)
    (ω : Ω) : Finset (PSplit n) :=
  props (zs r Z ω) (legible I ω)

/-- The expected number of pairs of splits proposed by a complete unit. -/
noncomputable def mu2 (μ : Measure Ω) (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ (sides r).offDiag, μ.real {ω | Z p.1 ω = 1 ∧ Z p.2 ω = 1}

/-- The expected number of splits proposed by a complete unit. -/
noncomputable def mu1 (μ : Measure Ω) (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) : ℝ :=
  ∑ σ ∈ sides r, mC μ Z σ

lemma measurableSet_filter_eq {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (c : ℝ) (F : Finset ι) :
    MeasurableSet {ω | s.filter (fun i => f i ω = c) = F} := by
  have : {ω | s.filter (fun i => f i ω = c) = F} =
      ⋂ i, {ω | (i ∈ s ∧ f i ω = c) ↔ i ∈ F} := by
    ext ω; simp [Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : MeasurableSet {ω | f i ω = c} := measurableSet_eq_fun (hf i) measurable_const
  by_cases h1 : i ∈ s <;> by_cases h2 : i ∈ F <;> simp [h1, h2]
  · exact measurableSet_setOfPred.mp hm
  · exact (measurableSet_setOfPred.mp hm).not

section model

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1)
  (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
  (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ)

include hZ hIm in
/-- Every event about the unit's proposals and legible witnesses is measurable. -/
lemma measurableSet_data (p : Finset (Finset (Fin n)) → Finset (Fin n) → Prop) :
    MeasurableSet {ω | p (zs r Z ω) (legible I ω)} := by
  have : {ω | p (zs r Z ω) (legible I ω)} =
      ⋃ F : Finset (Finset (Fin n)), ⋃ O : Finset (Fin n),
        ({ω | zs r Z ω = F} ∩ {ω | legible I ω = O}) ∩ {_ω | p F O} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun O =>
    ((measurableSet_filter_eq _ Z hZ 1 F).inter (measurableSet_filter_eq _ I hIm 0 O)).inter
      (MeasurableSet.const _)

include hZ hIm in
lemma measurable_unitProps [MeasurableSpace (Finset (PSplit n))] :
    Measurable (unitProps r Z I) := fun s _ =>
  measurableSet_data hZ hIm (fun F O => props F O ∈ s)

include hZ hIm in
lemma measurable_count (T : Finset (Finset (Fin n))) :
    Measurable fun ω => (count T (zs r Z ω) (legible I ω) : ℝ) := fun s _ =>
  measurableSet_data hZ hIm (fun F O => (count T F O : ℝ) ∈ s)

include hZ hIm in
lemma integrable_count (T : Finset (Finset (Fin n))) :
    Integrable (fun ω => (count T (zs r Z ω) (legible I ω) : ℝ)) μ := by
  refine Integrable.of_bound (C := (sides r).card) (measurable_count hZ hIm T).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  unfold count props
  exact_mod_cast ((card_filter_le _ _).trans card_image_le).trans
    ((card_filter_le _ _).trans (card_filter_le _ _))

include hZ hindZI hindI in
/-- The probability that the proposals are in a given set of states and every witness of `D` is
illegible factors. -/
lemma meas_inter_ill (s : Set (Finset (Fin n) → ℝ)) (hs : MeasurableSet s) (D : Finset (Fin n)) :
    μ.real ({ω | (fun σ => Z σ ω) ∈ s} ∩ {ω | ∀ x ∈ D, I x ω = 1}) =
      μ.real {ω | (fun σ => Z σ ω) ∈ s} * ∏ x ∈ D, μ.real {ω | I x ω = 1} := by
  have ht : MeasurableSet {f : Fin n → ℝ | ∀ x ∈ D, f x = 1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (measurable_pi_apply x) measurable_const
  have h1 := hindZI.measure_inter_preimage_eq_mul _ _ hs ht
  have h2 := hindI.measure_inter_preimage_eq_mul D (sets := fun _ => ({1} : Set ℝ))
    (fun _ _ => measurableSet_singleton 1)
  have e3 : (⋂ x ∈ D, I x ⁻¹' ({1} : Set ℝ)) = {ω | ∀ x ∈ D, I x ω = 1} := by
    ext ω; simp
  rw [e3] at h2
  rw [measureReal_def, show {ω | (fun σ => Z σ ω) ∈ s} ∩ {ω | ∀ x ∈ D, I x ω = 1} =
    (fun ω σ => Z σ ω) ⁻¹' s ∩ (fun ω x => I x ω) ⁻¹' {f | ∀ x ∈ D, f x = 1} from rfl, h1,
    ENNReal.toReal_mul, show (fun ω x => I x ω) ⁻¹' {f : Fin n → ℝ | ∀ x ∈ D, f x = 1} =
    {ω | ∀ x ∈ D, I x ω = 1} from rfl, h2, ENNReal.toReal_prod, measureReal_def]
  rfl

include hZ hindZI hindI hδ in
/-- With one witness of `D` at least, all of `D` illegible costs a factor `δ`. -/
lemma meas_inter_ill_le (s : Set (Finset (Fin n) → ℝ)) (hs : MeasurableSet s)
    {D : Finset (Fin n)} (hD : D.Nonempty) :
    μ.real ({ω | (fun σ => Z σ ω) ∈ s} ∩ {ω | ∀ x ∈ D, I x ω = 1}) ≤
      μ.real {ω | (fun σ => Z σ ω) ∈ s} * δ := by
  rw [meas_inter_ill hZ hindZI hindI s hs D]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  obtain ⟨x, hx⟩ := hD
  rw [← mul_prod_erase D _ hx]
  calc μ.real {ω | I x ω = 1} * ∏ y ∈ D.erase x, μ.real {ω | I y ω = 1}
      ≤ μ.real {ω | I x ω = 1} * 1 :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ => measureReal_nonneg)
          fun _ _ => measureReal_le_one) measureReal_nonneg
    _ ≤ δ := by rw [mul_one]; exact hδ x

/-- Equal restrictions force every witness of one of the two mismatch sets to be illegible. -/
lemma ill_of_sameRestr (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1) {ω : Ω} {A C : Finset (Fin n)}
    (h : SameRestr (legible I ω) A C) :
    (∀ x ∈ symmDiff A C, I x ω = 1) ∨ (∀ x ∈ symmDiff A Cᶜ, I x ω = 1) := by
  have ill : ∀ C : Finset (Fin n), A ∩ legible I ω = C ∩ legible I ω →
      ∀ x ∈ symmDiff A C, I x ω = 1 := by
    intro C hC x hx
    rcases hI01 x ω with h0 | h1
    · exfalso
      have hl : x ∈ legible I ω := by simp [legible, h0]
      rw [mem_symmDiff] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (mem_inter.mp (hC ▸ mem_inter.mpr ⟨h1, hl⟩)).1
      · exact h2 (mem_inter.mp (hC.symm ▸ mem_inter.mpr ⟨h1, hl⟩)).1
    · exact h1
  rcases h with h | h
  · exact Or.inl (ill C h)
  · exact Or.inr (ill Cᶜ h)

include hZ hIm hI01 hindZI hindI hδ in
/-- Two distinct sides away from `r` share their restriction with probability at most `2δ`, on
any event `s` about the proposals. -/
lemma meas_same_le (s : Set (Finset (Fin n) → ℝ)) (hs : MeasurableSet s)
    {A C : Finset (Fin n)} (hA : A ∈ sides r) (hC : C ∈ sides r) (hAC : A ≠ C) :
    μ.real {ω | (fun σ => Z σ ω) ∈ s ∧ SameRestr (legible I ω) A C} ≤
      2 * δ * μ.real {ω | (fun σ => Z σ ω) ∈ s} := by
  have hrA : r ∉ A := (mem_filter.mp hA).2.1
  have hrC : r ∉ C := (mem_filter.mp hC).2.1
  have hD1 : (symmDiff A C).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, ← bot_eq_empty, symmDiff_eq_bot]; exact hAC
  have hD2 : (symmDiff A Cᶜ).Nonempty := ⟨r, by simp [mem_symmDiff, hrA, hrC]⟩
  set E := {ω | (fun σ => Z σ ω) ∈ s}
  have hsub : {ω | (fun σ => Z σ ω) ∈ s ∧ SameRestr (legible I ω) A C} ⊆
      (E ∩ {ω | ∀ x ∈ symmDiff A C, I x ω = 1}) ∪ (E ∩ {ω | ∀ x ∈ symmDiff A Cᶜ, I x ω = 1}) := by
    rintro ω ⟨hz, hsame⟩
    rcases ill_of_sameRestr hI01 hsame with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  calc _ ≤ μ.real ((E ∩ {ω | ∀ x ∈ symmDiff A C, I x ω = 1}) ∪
          (E ∩ {ω | ∀ x ∈ symmDiff A Cᶜ, I x ω = 1})) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ μ.real E * δ + μ.real E * δ := add_le_add
        (meas_inter_ill_le hZ hindZI hindI hδ s hs hD1) (meas_inter_ill_le hZ hindZI hindI hδ s hs hD2)
    _ = _ := by ring

end model

section bounds

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1)
  (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
  (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ)

/-- The indicator of an event about the unit. -/
noncomputable def ind (r : Fin n) (Z : Finset (Fin n) → Ω → ℝ) (I : Fin n → Ω → ℝ)
    (p : Finset (Finset (Fin n)) → Finset (Fin n) → Prop) (ω : Ω) : ℝ :=
  if p (zs r Z ω) (legible I ω) then 1 else 0

include hZ hIm in
lemma ind_eq (p : Finset (Finset (Fin n)) → Finset (Fin n) → Prop) :
    ind r Z I p = Set.indicator {ω | p (zs r Z ω) (legible I ω)} 1 := by
  funext ω; simp [ind, Set.indicator_apply]

include hZ hIm in
lemma integrable_ind (p : Finset (Finset (Fin n)) → Finset (Fin n) → Prop) :
    Integrable (ind r Z I p) μ := by
  rw [ind_eq hZ hIm]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_data hZ hIm p)

include hZ hIm in
lemma integral_ind (p : Finset (Finset (Fin n)) → Finset (Fin n) → Prop) :
    ∫ ω, ind r Z I p ω ∂μ = μ.real {ω | p (zs r Z ω) (legible I ω)} := by
  rw [ind_eq hZ hIm, integral_indicator_one (measurableSet_data hZ hIm p)]

lemma mem_zs {σ : Finset (Fin n)} (hσ : σ ∈ sides r) (ω : Ω) : σ ∈ zs r Z ω ↔ Z σ ω = 1 := by
  simp [zs, hσ]

include hZ hIm hI01 hindZI hindI hδ in
/-- **Theorem 7.14(c), true stemma.**  `M(T) ≥ (1 - 4δ) m(T) - 2δ μ₂`, `M` the expected number
of distinct partial proposals of the unit displayed by `T`. -/
theorem M_lower {T : Finset (Finset (Fin n))} (hT : T ⊆ sides r) :
    (1 - 4 * δ) * ∑ σ ∈ T, mC μ Z σ - 2 * δ * mu2 μ r Z ≤
      ∫ ω, (count T (zs r Z ω) (legible I ω) : ℝ) ∂μ := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  set p1 : Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun σ F O => σ ∈ F ∧ NontrivOn O σ
  set p2 : Finset (Fin n) × Finset (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) → Prop :=
    fun q F O => q.1 ∈ F ∧ q.2 ∈ F ∧ SameRestr O q.1 q.2
  -- pointwise
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
  -- the true term
  have hA : (1 - 4 * δ) * ∑ σ ∈ T, mC μ Z σ ≤
      ∑ σ ∈ T, μ.real {ω | p1 σ (zs r Z ω) (legible I ω)} := by
    rw [mul_sum]
    refine sum_le_sum fun σ hσ => ?_
    have heq : {ω | p1 σ (zs r Z ω) (legible I ω)} =
        {ω | Z σ ω = 1 ∧ NontrivOn (legible I ω) σ} := by
      ext ω; simp [p1, mem_zs (hT hσ)]
    rw [heq]
    exact nontriv_lower hZ hIm hI01 hindZI hindI (hT hσ) hδ
  -- the merged pairs
  have hB : ∑ q ∈ T.offDiag, μ.real {ω | p2 q (zs r Z ω) (legible I ω)} ≤ 4 * δ * mu2 μ r Z := by
    calc ∑ q ∈ T.offDiag, μ.real {ω | p2 q (zs r Z ω) (legible I ω)}
        ≤ ∑ q ∈ T.offDiag, 2 * δ * μ.real {ω | Z q.1 ω = 1 ∧ Z q.2 ω = 1} := by
          refine sum_le_sum fun q hq => ?_
          obtain ⟨h1, h2, h3⟩ := mem_offDiag.mp hq
          have heq : {ω | p2 q (zs r Z ω) (legible I ω)} = {ω | (fun σ => Z σ ω) ∈
              {f : Finset (Fin n) → ℝ | f q.1 = 1 ∧ f q.2 = 1} ∧
                SameRestr (legible I ω) q.1 q.2} := by
            ext ω; simp [p2, mem_zs (hT h1), mem_zs (hT h2), and_assoc]
          rw [heq]
          exact meas_same_le hZ hIm hI01 hindZI hindI hδ _
            ((measurableSet_eq_fun (measurable_pi_apply _) measurable_const).inter
              (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)) (hT h1) (hT h2) h3
      _ ≤ ∑ q ∈ (sides r).offDiag, 2 * δ * μ.real {ω | Z q.1 ω = 1 ∧ Z q.2 ω = 1} :=
          sum_le_sum_of_subset_of_nonneg (offDiag_mono hT) fun _ _ _ =>
            mul_nonneg (by linarith) measureReal_nonneg
      _ = 4 * δ * mu2 μ r Z := by rw [← mul_sum, mu2]; ring
  linarith

include hZ hIm hI01 hindZI hindI hδ in
/-- **Theorem 7.14(c), rival stemma.**  `M(T') ≤ m(T') + 2 |T'| δ μ`; for a binary `T'`,
`|T'| = n - 3`. -/
theorem M_upper {T' : Finset (Finset (Fin n))} (hT' : T' ⊆ sides r) :
    ∫ ω, (count T' (zs r Z ω) (legible I ω) : ℝ) ∂μ ≤
      ∑ σ ∈ T', mC μ Z σ + 2 * δ * T'.card * mu1 μ r Z := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
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
          have heq : {ω | p2 σ τ (zs r Z ω) (legible I ω)} = {ω | (fun σ => Z σ ω) ∈
              {f : Finset (Fin n) → ℝ | f σ = 1} ∧ SameRestr (legible I ω) τ σ} := by
            ext ω; simp [p2, mem_zs hσs]
          rw [heq]
          exact meas_same_le hZ hIm hI01 hindZI hindI hδ _
            (measurableSet_eq_fun (measurable_pi_apply _) measurable_const) (hT' hτ) hσs
            (fun h => hσT (h ▸ hτ))
      _ = 2 * δ * T'.card * ∑ σ ∈ sides r \ T', mC μ Z σ := by
          rw [mul_sum]; refine sum_congr rfl fun σ _ => ?_
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * δ * T'.card * mu1 μ r Z := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => measureReal_nonneg
  linarith

end bounds

/-! ### The inequality of (c) and consistency -/

section main

variable {r : Fin n} {Z : Finset (Fin n) → Ω → ℝ} {I : Fin n → Ω → ℝ} {δ : ℝ}
  (hZ : ∀ σ, Measurable (Z σ)) (hIm : ∀ x, Measurable (I x))
  (hI01 : ∀ x ω, I x ω = 0 ∨ I x ω = 1)
  (hindZI : IndepFun (fun ω σ => Z σ ω) (fun ω x => I x ω) μ) (hindI : iIndepFun I μ)
  (hδ : ∀ x, μ.real {ω | I x ω = 1} ≤ δ)

lemma subset_sides {S : Finset (Finset (Fin n))} (hS : IsSystem r S) : S ⊆ sides r :=
  fun A hA => mem_filter.mpr ⟨mem_univ _, hS.1 A hA⟩

/-- When the unit `0` of a sequence `P` of units follows the model, `Cutting.M` is the expectation
of its count. -/
lemma M_eq {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I)
    (T : Finset (Finset (Fin n))) :
    M μ P T = ∫ ω, (count T (zs r Z ω) (legible I ω) : ℝ) ∂μ := by
  unfold M X; rw [hP0]; rfl

include hZ hIm hI01 hindZI hindI hδ in
/-- **Theorem 7.14(c) (`thm:cuttingconsistency`), the inequality.**  Under the illegibility model,
for binary stemmata `T` and `T'`,
`M(T) - M(T') ≥ m(T) - m(Σ(T')) - δ (2 (n - 1) μ + 2 μ₂)`. -/
theorem cutting_illegible (hn : 3 ≤ n) {T T' : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hT' : IsBinary r T') {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I) :
    ∑ σ ∈ T, mC μ Z σ - ∑ σ ∈ T', mC μ Z σ -
        δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) ≤
      M μ P T - M μ P T' := by
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
  have h1 := M_lower hZ hIm hI01 hindZI hindI hδ (subset_sides hT.1)
  have h2 := M_upper hZ hIm hI01 hindZI hindI hδ (subset_sides hT'.1)
  rw [hT'.2, Nat.cast_sub hn] at h2
  have hmT : ∑ σ ∈ T, mC μ Z σ ≤ mu1 μ r Z :=
    sum_le_sum_of_subset_of_nonneg (subset_sides hT.1) fun _ _ _ => measureReal_nonneg
  rw [M_eq hP0, M_eq hP0]
  push_cast at h2
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hmT)]

lemma mu1_nonneg : 0 ≤ mu1 μ r Z := sum_nonneg fun _ _ => measureReal_nonneg

lemma mu2_nonneg : 0 ≤ mu2 μ r Z :=
  mul_nonneg (by norm_num) (sum_nonneg fun _ _ => measureReal_nonneg)

include hZ hIm hI01 hindZI hindI hδ in
/-- **Theorem 7.14(c), the margin.**  If `δ (2 (n - 1) μ + 2 μ₂) < γ`, `γ` the complete-data
margin of `T` (Definition 7.2), then `T` is the unique maximum of `M` over binary stemmata. -/
theorem cutting_illegible_margin (hn : 3 ≤ n) {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (hTne : T.Nonempty) {P : ℕ → Ω → Finset (PSplit n)} (hP0 : P 0 = unitProps r Z I)
    (hγ : δ * (2 * ((n : ℝ) - 1) * mu1 μ r Z + 2 * mu2 μ r Z) < margin r (mC μ Z) T hTne) :
    ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T := by
  intro T' hT' hne
  have hδ0 : 0 ≤ δ := measureReal_nonneg.trans (hδ r)
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
  have := cutting_illegible hZ hIm hI01 hindZI hindI hδ hn hT hT' hP0
  linarith

variable [MeasurableSpace (Finset (PSplit n))] [MeasurableSingletonClass (Finset (PSplit n))]

include hZ hIm hI01 hindZI hindI hδ in
/-- **Theorem 7.14(c), consistency.**  Let the units `P u` (their partial proposals) be pairwise
independent and identically distributed, with unit `0` following the illegibility model.  If
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
    (cutting_illegible_margin hZ hIm hI01 hindZI hindI hδ hn hT hTne hP0 hγ)

end main

end Stemma.CuttingIllegible
