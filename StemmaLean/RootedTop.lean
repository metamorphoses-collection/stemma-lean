/-
Two-branched tops in the rooted coding: a maximum-weight laminar set of clusters never leaves a
vertex with three or more children when the union of two of them has positive weight.

Clusters, laminarity and laminar sets of proper clusters are those of `Rooted.lean`; children are
those of `Polytomy.IsChild` (the maximal members of `S` and the single witnesses strictly inside a
cluster).

* `top_union`: if `V` is a cluster of a laminar set `S` (or all the witnesses) and `D₁`, `D₂`,
  `D₃` are three distinct children of `V`, then `D₁ ∪ D₂` is a proper cluster, is not in `S`, and
  is laminar with every member of `S`;
* `two_branched_top`: so for a maximum-weight laminar set `S` (weight `w ≥ 0`), the union of two
  children of a vertex with three or more children has weight `0`;
* `rooted_bedier_effect`: if the units propose `τ = C_i ∪ C_j` independently with probability `m`,
  the probability that some maximum-weight laminar set has the root children `C₁`, `C₂`, `C₃` is
  at most `(1 - m)^L`; `rooted_bedier_true`: in particular, if `C₁`, `C₂`, `C₃` are the children
  of the root in the true rooted stemma `T`, the probability that `T` is a maximum-weight laminar
  set is at most `(1 - m)^L`.
-/
import Mathlib
import StemmaLean.Rooted
import StemmaLean.Polytomy

open MeasureTheory ProbabilityTheory Finset
open scoped Classical

namespace Stemma.RootedTop

open Rooted Polytomy

variable {n : ℕ}

/-- `S` is a maximum-weight laminar set of proper clusters for the weight `w`. -/
def IsOptimalR (w : Finset (Fin n) → ℝ) (S : Finset (Finset (Fin n))) : Prop :=
  IsHier S ∧ ∀ S', IsHier S' → wtR w S' ≤ wtR w S

/-- Members of a laminar set and single witnesses are pairwise laminar. -/
lemma lam_of_hier {S : Finset (Finset (Fin n))} (hS : IsHier S) {A B : Finset (Fin n)}
    (hA : A ∈ S ∨ A.card = 1) (hB : B ∈ S ∨ B.card = 1) : Lam A B := by
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · by_cases hAB : A = B
      · exact hAB ▸ lam_self A
      · exact hS.2 A hA B hB hAB
    · obtain ⟨b, rfl⟩ := card_eq_one.mp hB
      by_cases hb : b ∈ A
      · exact Or.inr (Or.inr (singleton_subset_iff.mpr hb))
      · exact Or.inl (disjoint_singleton_right.mpr hb)
  · obtain ⟨a, rfl⟩ := card_eq_one.mp hA
    by_cases ha : a ∈ B
    · exact Or.inr (Or.inl (singleton_subset_iff.mpr ha))
    · exact Or.inl (disjoint_singleton_left.mpr ha)

/-- **The union of two children at a vertex with three or more children.**  Let `S` be a laminar
set of proper clusters and `V` a member of `S` or the set of all witnesses.  If `D₁`, `D₂`, `D₃`
are three distinct children of `V`, then `D₁ ∪ D₂` is a proper cluster, is not in `S`, and is
laminar with every member of `S`. -/
theorem top_union {S : Finset (Finset (Fin n))} (hS : IsHier S) {V : Finset (Fin n)}
    (hV : V ∈ S ∨ V = univ) {D₁ D₂ D₃ : Finset (Fin n)}
    (h₁ : IsChild S V D₁) (h₂ : IsChild S V D₂) (h₃ : IsChild S V D₃)
    (h12 : D₁ ≠ D₂) (h13 : D₁ ≠ D₃) (h23 : D₂ ≠ D₃) :
    IsCluster (D₁ ∪ D₂) ∧ D₁ ∪ D₂ ∉ S ∧ ∀ A ∈ S, Lam (D₁ ∪ D₂) A := by
  -- distinct children are disjoint
  have disj : ∀ {D D'}, IsChild S V D → IsChild S V D' → D ≠ D' → Disjoint D D' := by
    intro D D' hD hD' hne
    rcases lam_of_hier hS hD.2.1 hD'.2.1 with h | h | h
    · exact h
    · exact absurd (hD.2.2 D' hD'.1 hD'.2.1 h) (Ne.symm hne)
    · exact absurd (hD'.2.2 D hD.1 hD.2.1 h) hne
  have hne : ∀ {D}, IsChild S V D → D.Nonempty := by
    intro D hD
    rcases hD.2.1 with hDS | h1
    · exact card_pos.mp (by have := (hS.1 D hDS).1; omega)
    · exact card_pos.mp (by omega)
  have d12 := disj h₁ h₂ h12
  have d13 := disj h₁ h₃ h13
  have d23 := disj h₂ h₃ h23
  have hτV : D₁ ∪ D₂ ⊆ V := union_subset h₁.1.1 h₂.1.1
  obtain ⟨x₁, hx₁⟩ := hne h₁
  obtain ⟨x₂, hx₂⟩ := hne h₂
  obtain ⟨x₃, hx₃⟩ := hne h₃
  have hx₃τ : x₃ ∉ D₁ ∪ D₂ := by
    rw [mem_union, not_or]
    exact ⟨fun h => disjoint_left.mp d13 h hx₃, fun h => disjoint_left.mp d23 h hx₃⟩
  have hτV' : D₁ ∪ D₂ ⊂ V := ssubset_of_subset_of_ne hτV fun h => hx₃τ (h ▸ h₃.1.1 hx₃)
  refine ⟨⟨?_, fun h => hx₃τ (h ▸ mem_univ x₃)⟩, ?_, ?_⟩
  · have hx : x₁ ≠ x₂ := fun h => disjoint_left.mp d12 hx₁ (h ▸ hx₂)
    calc 2 = ({x₁, x₂} : Finset (Fin n)).card := (card_pair hx).symm
      _ ≤ _ := card_le_card (by
          intro y hy; simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          exacts [mem_union_left _ hx₁, mem_union_right _ hx₂])
  · -- a member of `S` strictly inside `V` above `D₁` would be `D₁`
    intro hτS
    have := h₁.2.2 (D₁ ∪ D₂) hτV' (Or.inl hτS) subset_union_left
    have : x₂ ∈ D₁ := this ▸ mem_union_right _ hx₂
    exact disjoint_left.mp d12 this hx₂
  · intro A hA
    have hAV : Lam A V := by
      rcases hV with hV | rfl
      · by_cases h : A = V
        · exact h ▸ lam_self A
        · exact hS.2 A hA V hV h
      · exact Or.inr (Or.inl (subset_univ A))
    rcases hAV with h | h | h
    · exact Or.inl (disjoint_of_subset_left hτV h.symm)
    · rcases h.eq_or_ssubset with rfl | hss
      · exact Or.inr (Or.inl hτV)
      · obtain ⟨D, hD, hAD⟩ := exists_child hss (Or.inl hA)
        by_cases e1 : D = D₁
        · exact Or.inr (Or.inr (hAD.trans (e1 ▸ subset_union_left)))
        by_cases e2 : D = D₂
        · exact Or.inr (Or.inr (hAD.trans (e2 ▸ subset_union_right)))
        · left
          rw [disjoint_union_left]
          exact ⟨disjoint_of_subset_right hAD (disj h₁ hD (Ne.symm e1)),
            disjoint_of_subset_right hAD (disj h₂ hD (Ne.symm e2))⟩
    · exact Or.inr (Or.inl (hτV.trans h))

/-- **Two-branched tops, deterministic core.**  Let `S` be a maximum-weight laminar set of proper
clusters and `V` a cluster of `S` or the set of all witnesses.  If `V` has three distinct children
`D₁`, `D₂`, `D₃`, then `w (D₁ ∪ D₂) ≤ 0`: otherwise adding `D₁ ∪ D₂` to `S` would give a strictly
heavier laminar set. -/
theorem union_weight_nonpos {w : Finset (Fin n) → ℝ} {S : Finset (Finset (Fin n))}
    (hS : IsOptimalR w S) {V : Finset (Fin n)} (hV : V ∈ S ∨ V = univ)
    {D₁ D₂ D₃ : Finset (Fin n)} (h₁ : IsChild S V D₁) (h₂ : IsChild S V D₂)
    (h₃ : IsChild S V D₃) (h12 : D₁ ≠ D₂) (h13 : D₁ ≠ D₃) (h23 : D₂ ≠ D₃) :
    w (D₁ ∪ D₂) ≤ 0 := by
  obtain ⟨hcl, hnot, hlam⟩ := top_union hS.1 hV h₁ h₂ h₃ h12 h13 h23
  have hins : IsHier (insert (D₁ ∪ D₂) S) := by
    refine ⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩
    · rcases mem_insert.mp hA with rfl | hA
      · exact hcl
      · exact hS.1.1 A hA
    · rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
      · exact absurd rfl hab
      · exact hlam b hb
      · exact lam_symm (hlam a ha)
      · exact hS.1.2 a ha b hb hab
  have := hS.2 _ hins
  rw [wtR, sum_insert hnot] at this
  unfold wtR at this
  linarith

/-- **Two-branched tops.**  Let `w ≥ 0` and `S` be a maximum-weight laminar set of proper clusters.
At a cluster `V` of `S`, or at the root (`V` the set of all witnesses), with three or more children,
the union of any two children has weight `0`. -/
theorem two_branched_top {w : Finset (Fin n) → ℝ} (hw0 : ∀ A, 0 ≤ w A)
    {S : Finset (Finset (Fin n))} (hS : IsOptimalR w S) {V : Finset (Fin n)}
    (hV : V ∈ S ∨ V = univ) {D₁ D₂ D₃ : Finset (Fin n)} (h₁ : IsChild S V D₁)
    (h₂ : IsChild S V D₂) (h₃ : IsChild S V D₃) (h12 : D₁ ≠ D₂) (h13 : D₁ ≠ D₃)
    (h23 : D₂ ≠ D₃) :
    w (D₁ ∪ D₂) = 0 :=
  le_antisymm (union_weight_nonpos hS hV h₁ h₂ h₃ h12 h13 h23) (hw0 _)

/-! ### The probability -/

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The Bédier effect at the top, for clusters.**  Let `C₁`, `C₂`, `C₃` be distinct, and let
unit `u` propose the cluster `τ = C₁ ∪ C₂` on the event `E u`, of probability `m`, the complements
independent.  If the support `w ω τ` of `τ` counts the units proposing it, then the probability
that some maximum-weight laminar set of proper clusters has `C₁`, `C₂`, `C₃` among the children of
its root is at most `(1 - m)^L`. -/
theorem rooted_bedier_effect {L : ℕ} {C₁ C₂ C₃ : Finset (Fin n)} (h12 : C₁ ≠ C₂)
    (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃)
    (E : Fin L → Set Ω) (hmeasE : ∀ u, MeasurableSet (E u))
    (hind : iIndepSet (fun u => (E u)ᶜ) μ) (m : ℝ) (hm : ∀ u, μ.real (E u) = m)
    (w : Ω → Finset (Fin n) → ℝ)
    (hw : ∀ ω, w ω (C₁ ∪ C₂) = ((univ.filter fun u => ω ∈ E u).card : ℝ)) :
    μ.real {ω | ∃ S, IsOptimalR (w ω) S ∧ IsChild S univ C₁ ∧ IsChild S univ C₂ ∧
      IsChild S univ C₃} ≤ (1 - m) ^ L := by
  rw [← Consistency.bedier_probability E hmeasE hind m hm]
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  obtain ⟨S, hS, h₁, h₂, h₃⟩ := hω
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro u hu
  have hle := union_weight_nonpos hS (Or.inr rfl) h₁ h₂ h₃ h12 h13 h23
  rw [hw ω] at hle
  have : 0 < (univ.filter fun u => ω ∈ E u).card :=
    card_pos.mpr ⟨u, mem_filter.mpr ⟨mem_univ u, hu⟩⟩
  have : (0 : ℝ) < (univ.filter fun u => ω ∈ E u).card := by exact_mod_cast this
  linarith

/-- **The Bédier effect at the top of the true rooted stemma.**  If the root of the true rooted
stemma `T` (its set of proper clusters) has three distinct children `C₁`, `C₂`, `C₃`, and each of
`L` independent units proposes `τ = C₁ ∪ C₂` with probability `m`, then `T` is a maximum-weight
laminar set of proper clusters with probability at most `(1 - m)^L`. -/
theorem rooted_bedier_true {L : ℕ} {T : Finset (Finset (Fin n))} {C₁ C₂ C₃ : Finset (Fin n)}
    (h₁ : IsChild T univ C₁) (h₂ : IsChild T univ C₂) (h₃ : IsChild T univ C₃)
    (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃)
    (E : Fin L → Set Ω) (hmeasE : ∀ u, MeasurableSet (E u))
    (hind : iIndepSet (fun u => (E u)ᶜ) μ) (m : ℝ) (hm : ∀ u, μ.real (E u) = m)
    (w : Ω → Finset (Fin n) → ℝ)
    (hw : ∀ ω, w ω (C₁ ∪ C₂) = ((univ.filter fun u => ω ∈ E u).card : ℝ)) :
    μ.real {ω | IsOptimalR (w ω) T} ≤ (1 - m) ^ L :=
  le_trans (measureReal_mono (s₂ := {ω | ∃ S, IsOptimalR (w ω) S ∧ IsChild S univ C₁ ∧
      IsChild S univ C₂ ∧ IsChild S univ C₃})
      (fun _ hω => ⟨T, hω, h₁, h₂, h₃⟩) (measure_ne_top _ _))
    (rooted_bedier_effect h12 h13 h23 E hmeasE hind m hm w hw)

end prob

end Stemma.RootedTop
