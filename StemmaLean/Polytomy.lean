/-
The Bédier effect at a polytomy: Proposition 8.1 of the technical report (`prop:bediereffect`)
as one statement, and the remark that follows it.

* `bedier_effect`: if a false split `τ`, compatible with every split of the stemma `T`, is
  proposed by each of `L` independent units with probability `m`, then the probability that `T`
  is a maximum-weight compatible set for the supports is at most `(1 - m)^L`.  (The report's
  `Pr(Ŝ_L = T) ≤ (1 - m_τ)^L`: selecting `T` requires `T` to be a maximum.)  This composes
  `bedier_core` (`Basic.lean`) and `bedier_probability` (`Consistency.lean`).
* `polytomy_split`: a polytomy produces such a `τ`.  Rooting the stemma at the witness `r`, the
  clusters are the sides away from `r`.  If a cluster `C` (a split of `T`, or `X \ {r}` for the
  vertex next to `r`) has three or more children (its maximal sub-clusters, single witnesses
  included), the union `τ` of two of them is a non-trivial split, not in `T`, and compatible with
  every split of `T`.

The positivity of `m_τ` is a property of the model of variation, not of the combinatorics: a
coincident error or a shared retention on the two branches proposes `τ` (`Mechanisms.lean`,
Theorem 8.5(ii)), with positive probability (`Attraction.polytomy_support_pos`).
-/
import Mathlib
import StemmaLean.Consistency

open MeasureTheory ProbabilityTheory Finset
open scoped Classical

namespace Stemma.Polytomy

open Stemma.Splits

variable {n : ℕ}

/-! ### The probability -/

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Proposition 8.1 (`prop:bediereffect`).**  Let `T` be pairwise compatible, `τ ∉ T`
compatible with every member of `T`, and let unit `u` propose `τ` on the event `E u`, of
probability `m`, the complements independent.  If the support `w ω τ` of `τ` counts the units
proposing it, then `T` is a maximum-weight compatible set with probability at most `(1 - m)^L`. -/
theorem bedier_effect {L : ℕ} (T : Finset (Finset (Fin n))) (hT : PairwiseCompat T)
    (τ : Finset (Fin n)) (hτ : τ ∉ T) (hcomp : ∀ s ∈ T, Compat τ s)
    (E : Fin L → Set Ω) (hmeasE : ∀ u, MeasurableSet (E u))
    (hind : iIndepSet (fun u => (E u)ᶜ) μ) (m : ℝ) (hm : ∀ u, μ.real (E u) = m)
    (w : Ω → Finset (Fin n) → ℕ) (hw : ∀ ω, w ω τ = (univ.filter fun u => ω ∈ E u).card) :
    μ.real {ω | IsOptimal (w ω) T} ≤ (1 - m) ^ L := by
  rw [← Consistency.bedier_probability E hmeasE hind m hm]
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro u hu
  apply bedier_core (w ω) T τ hT hτ hcomp _ hω
  rw [hw ω]
  exact card_pos.mpr ⟨u, mem_filter.mpr ⟨mem_univ u, hu⟩⟩

end prob

/-! ### A polytomy produces a compatible false split -/

/-- `D` is a child of the cluster `C` in the system `T`: a maximal proper sub-cluster of `C`,
where the sub-clusters are the members of `T` and the single witnesses. -/
def IsChild (T : Finset (Finset (Fin n))) (C D : Finset (Fin n)) : Prop :=
  D ⊂ C ∧ (D ∈ T ∨ D.card = 1) ∧
    ∀ E : Finset (Fin n), E ⊂ C → (E ∈ T ∨ E.card = 1) → D ⊆ E → E = D

/-- Every proper sub-cluster of `C` lies in a child of `C`. -/
lemma exists_child {T : Finset (Finset (Fin n))} {C A : Finset (Fin n)} (hA : A ⊂ C)
    (hAT : A ∈ T ∨ A.card = 1) : ∃ D, IsChild T C D ∧ A ⊆ D := by
  set cand := univ.filter fun E : Finset (Fin n) => E ⊂ C ∧ (E ∈ T ∨ E.card = 1) ∧ A ⊆ E
  have hne : cand.Nonempty := ⟨A, by simp [cand, hA, hAT]⟩
  obtain ⟨D, hD, hmax⟩ := exists_max_image cand card hne
  simp only [cand, mem_filter, mem_univ, true_and] at hD
  refine ⟨D, ⟨hD.1, hD.2.1, fun E hE hET hDE => ?_⟩, hD.2.2⟩
  have := hmax E (by simp [cand, hE, hET, hD.2.2.trans hDE])
  exact (eq_of_subset_of_card_le hDE this).symm

/-- **Remark after Proposition 8.1, combinatorial part.**  Let `T` be the split system of a stemma
(sides away from `r`) and `C` a cluster: a split of `T`, or `X \ {r}`.  If `D₁`, `D₂`, `D₃` are
three distinct children of `C`, then `τ = D₁ ∪ D₂` is a non-trivial side away from `r`, is not a
split of `T`, and is compatible with every split of `T`.  Such a `τ` resolves the polytomy at the
vertex of `C`; by Proposition 8.1 the true stemma is then selected with probability at most
`(1 - m_τ)^L`. -/
theorem polytomy_split {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsSystem r T)
    {C : Finset (Fin n)} (hC : C ∈ T ∨ C = univ.erase r) {D₁ D₂ D₃ : Finset (Fin n)}
    (h₁ : IsChild T C D₁) (h₂ : IsChild T C D₂) (h₃ : IsChild T C D₃)
    (h12 : D₁ ≠ D₂) (h13 : D₁ ≠ D₃) (h23 : D₂ ≠ D₃) :
    IsSide r (D₁ ∪ D₂) ∧ D₁ ∪ D₂ ∉ T ∧ ∀ A ∈ T, Compat (D₁ ∪ D₂) A := by
  have hrC : r ∉ C := by
    rcases hC with hC | rfl
    · exact (hT.1 C hC).1
    · simp
  -- clusters are laminar: members of `T`, singletons, and `C`
  have lam : ∀ A B : Finset (Fin n), (A ∈ T ∨ A.card = 1) → (B ∈ T ∨ B.card = 1) →
      r ∉ A → r ∉ B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A := by
    intro A B hA hB hrA hrB
    rcases hA with hA | hA
    · rcases hB with hB | hB
      · by_cases hAB : A = B
        · exact Or.inr (Or.inl hAB.le)
        · exact (compat_iff_laminar hrA hrB).mp (hT.2 A hA B hB hAB)
      · obtain ⟨b, rfl⟩ := card_eq_one.mp hB
        by_cases hb : b ∈ A
        · exact Or.inr (Or.inr (singleton_subset_iff.mpr hb))
        · exact Or.inl (disjoint_singleton_right.mpr hb)
    · obtain ⟨a, rfl⟩ := card_eq_one.mp hA
      by_cases ha : a ∈ B
      · exact Or.inr (Or.inl (singleton_subset_iff.mpr ha))
      · exact Or.inl (disjoint_singleton_left.mpr ha)
  have hr : ∀ {D}, IsChild T C D → r ∉ D := fun h hr => hrC (h.1.1 hr)
  -- distinct children are disjoint
  have disj : ∀ {D D'}, IsChild T C D → IsChild T C D' → D ≠ D' → Disjoint D D' := by
    intro D D' hD hD' hne
    rcases lam D D' hD.2.1 hD'.2.1 (hr hD) (hr hD') with h | h | h
    · exact h
    · exact absurd (hD.2.2 D' hD'.1 hD'.2.1 h) (Ne.symm hne)
    · exact absurd (hD'.2.2 D hD.1 hD.2.1 h) hne
  have hne : ∀ {D}, IsChild T C D → D.Nonempty := by
    intro D hD
    rcases hD.2.1 with hDT | h1
    · exact card_pos.mp (by have := (hT.1 D hDT).2.1; omega)
    · exact card_pos.mp (by omega)
  have d12 := disj h₁ h₂ h12
  have d13 := disj h₁ h₃ h13
  have d23 := disj h₂ h₃ h23
  have hτC : D₁ ∪ D₂ ⊆ C := union_subset h₁.1.1 h₂.1.1
  obtain ⟨x₃, hx₃⟩ := hne h₃
  have hx₃τ : x₃ ∉ D₁ ∪ D₂ := by
    rw [mem_union, not_or]
    exact ⟨fun h => disjoint_left.mp d13 h hx₃, fun h => disjoint_left.mp d23 h hx₃⟩
  refine ⟨⟨fun h => hrC (hτC h), ?_, ?_⟩, ?_, ?_⟩
  · -- two witnesses on the side
    obtain ⟨x₁, hx₁⟩ := hne h₁
    obtain ⟨x₂, hx₂⟩ := hne h₂
    have hx : x₁ ≠ x₂ := fun h => disjoint_left.mp d12 hx₁ (h ▸ hx₂)
    calc 2 = ({x₁, x₂} : Finset (Fin n)).card := (card_pair hx).symm
      _ ≤ _ := card_le_card (by
          intro y hy; simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          exacts [mem_union_left _ hx₁, mem_union_right _ hx₂])
  · -- two witnesses off it: one of the third child, and `r`
    have hx : x₃ ≠ r := fun h => hrC (h ▸ h₃.1.1 hx₃)
    calc 2 = ({x₃, r} : Finset (Fin n)).card := (card_pair hx).symm
      _ ≤ _ := card_le_card (by
          intro y hy; simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact mem_compl.mpr hx₃τ
          · exact mem_compl.mpr fun h => hrC (hτC h))
  · -- not a split of `T`: it would be a sub-cluster of `C` above `D₁`
    intro hτT
    have hτC' : D₁ ∪ D₂ ⊂ C := ssubset_of_subset_of_ne hτC fun h => hx₃τ (h ▸ h₃.1.1 hx₃)
    have := h₁.2.2 (D₁ ∪ D₂) hτC' (Or.inl hτT) subset_union_left
    obtain ⟨x₂, hx₂⟩ := hne h₂
    have : x₂ ∈ D₁ := this ▸ mem_union_right _ hx₂
    exact disjoint_left.mp d12 this hx₂
  · -- compatible with every split of `T`
    intro A hA
    have hrA : r ∉ A := (hT.1 A hA).1
    have hrτ : r ∉ D₁ ∪ D₂ := fun h => hrC (hτC h)
    rw [compat_iff_laminar hrτ hrA]
    -- `A` against `C`
    have hAC : Disjoint A C ∨ A ⊆ C ∨ C ⊆ A := by
      rcases hC with hC | rfl
      · by_cases h : A = C
        · exact Or.inr (Or.inl h.le)
        · exact (compat_iff_laminar hrA hrC).mp (hT.2 A hA C hC h)
      · exact Or.inr (Or.inl fun y hy => mem_erase.mpr ⟨fun h => hrA (h ▸ hy), mem_univ y⟩)
    rcases hAC with h | h | h
    · exact Or.inl (disjoint_of_subset_right hτC h).symm
    · rcases h.eq_or_ssubset with rfl | hss
      · exact Or.inr (Or.inl hτC)
      · obtain ⟨D, hD, hAD⟩ := exists_child hss (Or.inl hA)
        by_cases e1 : D = D₁
        · exact Or.inr (Or.inr (hAD.trans (e1 ▸ subset_union_left)))
        by_cases e2 : D = D₂
        · exact Or.inr (Or.inr (hAD.trans (e2 ▸ subset_union_right)))
        · left
          rw [disjoint_union_left]
          exact ⟨disjoint_of_subset_right hAD (disj h₁ hD (Ne.symm e1)),
            disjoint_of_subset_right hAD (disj h₂ hD (Ne.symm e2))⟩
    · exact Or.inr (Or.inl (hτC.trans h))

end Stemma.Polytomy
