/-
Size of the conflict graph (Proposition 9.1 of the technical report, `prop:size`).

Splits are counted as unordered bipartitions `{A, Aᶜ}` of the witnesses `Fin n`, independently of
any reference witness.
-/
import Mathlib
import StemmaLean.Splits
import StemmaLean.PartialSplits

namespace Stemma.Size

open Finset Stemma.Splits

variable {n : ℕ}

instance (A : Finset (Fin n)) : Decidable (Nontriv A) := by unfold Nontriv; infer_instance

/-- The unordered bipartition with side `A`. -/
def unord (A : Finset (Fin n)) : Finset (Finset (Fin n)) := {A, Aᶜ}

lemma unord_away (r : Fin n) (A : Finset (Fin n)) : unord (away r A) = unord A := by
  unfold unord away; split_ifs
  · rw [compl_compl, pair_comm]
  · rfl

lemma unord_injOn (r : Fin n) {A C : Finset (Fin n)} (hA : r ∉ A) (hC : r ∉ C)
    (h : unord A = unord C) : A = C := by
  have : A ∈ unord C := h ▸ (by simp [unord])
  simp only [unord, mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact h
  · exact absurd (h ▸ (by simpa using hC : r ∈ Cᶜ)) hA

lemma away_not_mem (r : Fin n) (A : Finset (Fin n)) : r ∉ away r A := by
  unfold away; split_ifs with h <;> simp [h]

/-- Counting unordered splits through their sides away from `r`. -/
lemma card_unord_eq (r : Fin n) (F : Finset (Finset (Fin n))) :
    (F.image unord).card = (F.image (away r)).card := by
  have : F.image unord = (F.image (away r)).image unord := by
    rw [image_image]; congr 1; funext A; exact (unord_away r A).symm
  rw [this, card_image_of_injOn]
  intro A hA C hC h
  simp only [coe_image, Set.mem_image, mem_coe] at hA hC
  obtain ⟨A', -, rfl⟩ := hA; obtain ⟨C', -, rfl⟩ := hC
  exact unord_injOn r (away_not_mem r A') (away_not_mem r C') h

/-- Subsets of a finite set with at most one element. -/
lemma card_small (U : Finset (Fin n)) :
    (U.powerset.filter (fun A => A.card ≤ 1)).card = U.card + 1 := by
  have : U.powerset.filter (fun A => A.card ≤ 1) = U.powersetCard 0 ∪ U.powersetCard 1 := by
    ext A
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    by_cases hA : A ⊆ U <;> simp only [hA, true_and, false_and, or_self] <;> omega
  rw [this, card_union_of_disjoint, card_powersetCard, card_powersetCard]
  · simp; ring
  · rw [disjoint_left]; intro A h1 h2
    rw [mem_powersetCard] at h1 h2; omega

/-- **Proposition 9.1 (`prop:size`), first part.**  On `n ≥ 3` witnesses there are
`2^(n-1) - n - 1` non-trivial full splits (unordered bipartitions with both sides of size at
least two).  The report assumes `n ≥ 4`. -/
theorem card_nontrivial (hn : 3 ≤ n) :
    ((univ.filter (fun A : Finset (Fin n) => Nontriv A)).image unord).card = 2 ^ (n - 1) - n - 1 := by
  classical
  set r : Fin n := ⟨0, by omega⟩
  rw [card_unord_eq r]
  set U := univ.erase r
  have hU : U.card = n - 1 := by simp [U, card_erase_of_mem]
  -- the sides away from `r` are the subsets of `U` other than `U` with at least two elements
  have himg : (univ.filter (fun A : Finset (Fin n) => Nontriv A)).image (away r) =
      U.powerset.filter (fun A => ¬ (A.card ≤ 1 ∨ A = U)) := by
    ext A
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_powerset]
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hs := isSide_away (r := r) hB
      have hsu := side_sub hs
      have hc2 := hs.2.1
      refine ⟨hsu.1, ?_⟩
      push Not; exact ⟨by omega, hsu.2⟩
    · rintro ⟨hsub, hA⟩
      push Not at hA
      refine ⟨A, ⟨by omega, ?_⟩, ?_⟩
      · have hlt := card_lt_card (ssubset_of_subset_of_ne hsub hA.2)
        rw [card_compl, Fintype.card_fin]; have := card_le_card hsub; omega
      · have : r ∉ A := fun h => by have := hsub h; simp [U] at this
        simp [away, this]
  rw [himg]
  have hsplit := card_filter_add_card_filter_not (s := U.powerset)
    (fun A => A.card ≤ 1 ∨ A = U)
  have hbad : (U.powerset.filter (fun A => A.card ≤ 1 ∨ A = U)).card = U.card + 2 := by
    rw [filter_or, card_union_of_disjoint, card_small]
    · have : U.powerset.filter (fun A => A = U) = {U} := by
        ext A; simp only [mem_filter, mem_powerset, mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ subset_rfl, h⟩⟩
      rw [this, card_singleton]
    · rw [disjoint_left]; intro A h1 h2
      simp only [mem_filter] at h1 h2; rw [h2.2] at h1; omega
  rw [card_powerset, hU] at hsplit
  rw [hU] at hbad
  have key : ∀ k : ℕ, k + 4 ≤ 2 ^ (k + 2) := by
    intro k; induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have : n + 1 ≤ 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have := key k
    simpa [show k + 3 - 1 = k + 2 by omega] using (by omega : k + 3 + 1 ≤ 2 ^ (k + 2))
  omega

/-- **Proposition 9.1 (`prop:size`), second part.**  Every independent set of the full conflict
graph, i.e. every pairwise compatible set of non-trivial full splits counted as unordered
bipartitions, has at most `n - 3` members.  Hence so has a best-supported stemma, and, with
fragmentary witnesses, so have the distinct completions of a jointly completable family
(`completions_le`). -/
theorem independent_le (F : Finset (Finset (Fin n))) (hF : ∀ A ∈ F, Nontriv A)
    (hc : ∀ A ∈ F, ∀ C ∈ F, Compat A C) : (F.image unord).card ≤ n - 3 := by
  rcases F.eq_empty_or_nonempty with h | ⟨A₀, hA₀⟩
  · simp [h]
  have hn : 0 < n := by
    have := (hF A₀ hA₀).1; have := card_le_univ A₀; simp at this; omega
  set r : Fin n := ⟨0, hn⟩
  rw [card_unord_eq r]
  apply card_le (r := r)
  refine ⟨fun B hB => ?_, fun a ha b hb _ => ?_⟩
  · simp only [mem_image] at hB; obtain ⟨A, hA, rfl⟩ := hB; exact isSide_away (hF A hA)
  · simp only [mem_image] at ha hb
    obtain ⟨A, hA, rfl⟩ := ha; obtain ⟨C, hC, rfl⟩ := hb
    rw [compat_away]; exact compat_symm (compat_away.mpr (compat_symm (hc A hA C hC)))

/-- An extension of a non-trivial partial split is a non-trivial full split. -/
lemma nontriv_of_extends {s : PSplit n} {A : Finset (Fin n)} (h : Extends s A)
    (h1 : 2 ≤ s.side.card) (h2 : 2 ≤ s.other.card) : Nontriv A := by
  have hside : s.side ⊆ A := fun x hx => by
    have : x ∈ A ∩ s.dom := h ▸ hx; exact (mem_inter.mp this).1
  have hother : s.other ⊆ Aᶜ := fun x hx => by
    rw [mem_compl]; intro hxA
    unfold PSplit.other at hx
    have : x ∈ A ∩ s.dom := mem_inter.mpr ⟨hxA, (mem_sdiff.mp hx).1⟩
    rw [h] at this; exact (mem_sdiff.mp hx).2 this
  exact ⟨h1.trans (card_le_card hside), h2.trans (card_le_card hother)⟩

/-- **Proposition 9.1 (`prop:size`), fragmentary witnesses.**  If a family `P` of non-trivial
partial splits is jointly completable, by extensions `ext s` that are pairwise compatible, the
extensions are at most `n - 3` distinct full splits. -/
theorem completions_le (P : Finset (PSplit n)) (hP : ∀ s ∈ P, 2 ≤ s.side.card ∧ 2 ≤ s.other.card)
    (ext : PSplit n → Finset (Fin n)) (hext : ∀ s ∈ P, Extends s (ext s))
    (hc : ∀ s ∈ P, ∀ t ∈ P, Compat (ext s) (ext t)) : ((P.image ext).image unord).card ≤ n - 3 := by
  apply independent_le
  · intro A hA; simp only [mem_image] at hA; obtain ⟨s, hs, rfl⟩ := hA
    exact nontriv_of_extends (hext s hs) (hP s hs).1 (hP s hs).2
  · intro A hA C hC; simp only [mem_image] at hA hC
    obtain ⟨s, hs, rfl⟩ := hA; obtain ⟨t, ht, rfl⟩ := hC; exact hc s hs t ht

end Stemma.Size
