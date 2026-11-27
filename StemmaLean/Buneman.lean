/-
Buneman's theorem for the split systems of `Splits.lean` (Proposition 3.2 of the technical report,
`prop:buneman`).

The tree side is the Splits Equivalence Theorem of `vltanh/lean4-phylogenetics` (Apache-2.0),
vendored unchanged in `StemmaLean/Vendor/`: `exists_xTree_iff` and `xTree_unique`, for `X`-trees as
Mathlib `SimpleGraph` trees with every vertex of degree at most two labelled (Semple and Steel 2003,
Theorem 3.1.4).  Its split systems are families of sides closed under complement, trivial splits
included.  This file is the bridge: a set `S` of non-trivial splits (sides away from `r`) is
pairwise compatible exactly when `S`, with both sides of each split and all trivial splits, is the
split system of an `X`-tree on the witnesses; the tree is then unique up to a label-preserving
isomorphism, and its non-trivial splits are exactly `S`.
-/
import Mathlib
import StemmaLean.Splits
import StemmaLean.Vendor.SplitsEquivalence

open Finset
open Phylogenetics.SplitsEquivalence

namespace Stemma.Buneman

open Splits

variable {n : ℕ}

/-- The split system, as a family of sides, of a set `S` of non-trivial splits together with all
trivial splits: `B` and `Bᶜ` for `B ∈ S`, and `{x}`, `{x}ᶜ` for every witness `x`. -/
def fam (S : Finset (Finset (Fin n))) : Set (Set (Fin n)) :=
  {A | (∃ B ∈ S, A = ↑B ∨ A = (↑B)ᶜ) ∨ ∃ x, A = {x} ∨ A = {x}ᶜ}

/-- Compatibility of two sides given as sets. -/
def SetCompat (A B : Set (Fin n)) : Prop := A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ Aᶜ ∩ B = ∅ ∨ Aᶜ ∩ Bᶜ = ∅

lemma setCompat_coe {a b : Finset (Fin n)} : SetCompat (a : Set (Fin n)) b ↔ Compat a b := by
  unfold SetCompat Compat
  simp only [← coe_compl, ← coe_inter, coe_eq_empty]

lemma setCompat_compl_left {A B : Set (Fin n)} : SetCompat Aᶜ B ↔ SetCompat A B := by
  unfold SetCompat; rw [compl_compl]; tauto

lemma setCompat_compl_right {A B : Set (Fin n)} : SetCompat A Bᶜ ↔ SetCompat A B := by
  unfold SetCompat; rw [compl_compl]; tauto

lemma setCompat_singleton (x : Fin n) (B : Set (Fin n)) : SetCompat {x} B := by
  by_cases h : x ∈ B
  · right; left; ext y; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff,
      Set.mem_empty_iff_false, iff_false, not_and, not_not]; rintro rfl; exact h
  · left; ext y; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]; rintro rfl; exact h

lemma setCompat_symm {A B : Set (Fin n)} (h : SetCompat A B) : SetCompat B A := by
  unfold SetCompat at *
  rcases h with h | h | h | h
  · exact Or.inl (by rw [Set.inter_comm]; exact h)
  · exact Or.inr (Or.inr (Or.inl (by rw [Set.inter_comm]; exact h)))
  · exact Or.inr (Or.inl (by rw [Set.inter_comm]; exact h))
  · exact Or.inr (Or.inr (Or.inr (by rw [Set.inter_comm]; exact h)))

lemma fam_isSplitSystem (hn : 2 ≤ n) {r : Fin n} {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) : IsSplitSystem (fam S) := by
  intro A hA
  have ne2 : ∀ B : Finset (Fin n), 2 ≤ B.card → (B : Set (Fin n)).Nonempty := fun B h =>
    coe_nonempty.mpr (card_pos.mp (by omega))
  rcases hA with ⟨B, hB, rfl | rfl⟩ | ⟨x, rfl | rfl⟩
  · refine ⟨ne2 B (hS B hB).2.1, ?_, Or.inl ⟨B, hB, Or.inr rfl⟩⟩
    rw [← coe_compl]; exact ne2 _ (hS B hB).2.2
  · refine ⟨?_, by rw [compl_compl]; exact ne2 B (hS B hB).2.1, ?_⟩
    · rw [← coe_compl]; exact ne2 _ (hS B hB).2.2
    · rw [compl_compl]; exact Or.inl ⟨B, hB, Or.inl rfl⟩
  · refine ⟨Set.singleton_nonempty x, ?_, Or.inr ⟨x, Or.inr rfl⟩⟩
    obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ x := by
      by_cases hx : x.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at hx; simp at hx⟩
      · exact ⟨⟨0, by omega⟩, fun e => hx (by rw [← e])⟩
    exact ⟨y, by simpa using hy⟩
  · refine ⟨?_, by rw [compl_compl]; exact Set.singleton_nonempty x, ?_⟩
    · obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ x := by
        by_cases hx : x.val = 0
        · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at hx; simp at hx⟩
        · exact ⟨⟨0, by omega⟩, fun e => hx (by rw [← e])⟩
      exact ⟨y, by simpa using hy⟩
    · rw [compl_compl]; exact Or.inr ⟨x, Or.inl rfl⟩

lemma fam_compatible_iff {S : Finset (Finset (Fin n))} :
    PairwiseCompatible (fam S) ↔ PairwiseCompat S := by
  constructor
  · intro h a ha b hb _
    exact setCompat_coe.mp (h _ (Or.inl ⟨a, ha, Or.inl rfl⟩) _ (Or.inl ⟨b, hb, Or.inl rfl⟩))
  · intro h A hA B hB
    change SetCompat A B
    -- reduce each side to a member of `S` or a singleton, up to complement
    have red : ∀ C ∈ fam S, (∃ c ∈ S, C = ↑c ∨ C = (↑c)ᶜ) ∨ ∃ x, C = {x} ∨ C = {x}ᶜ :=
      fun C hC => hC
    rcases red A hA with ⟨a, ha, hAa⟩ | ⟨x, hAx⟩
    · rcases red B hB with ⟨b, hb, hBb⟩ | ⟨y, hBy⟩
      · have hab : SetCompat (a : Set (Fin n)) b := by
          by_cases e : a = b
          · rw [e, setCompat_coe]; exact compat_self b
          · exact setCompat_coe.mpr (h a ha b hb e)
        rcases hAa with rfl | rfl <;> rcases hBb with rfl | rfl
        · exact hab
        · exact setCompat_compl_right.mpr hab
        · exact setCompat_compl_left.mpr hab
        · exact setCompat_compl_left.mpr (setCompat_compl_right.mpr hab)
      · rcases hBy with rfl | rfl
        · exact setCompat_symm (setCompat_singleton y A)
        · exact setCompat_compl_right.mpr (setCompat_symm (setCompat_singleton y A))
    · rcases hAx with rfl | rfl
      · exact setCompat_singleton x B
      · exact setCompat_compl_left.mpr (setCompat_singleton x B)

/-- **Proposition 3.2 (`prop:buneman`), existence and characterisation.**  Let `n ≥ 2` and let `S`
be a set of non-trivial splits on `Fin n`, each recorded by its side away from `r`.  Then `S` is
pairwise compatible (a split system, `IsSystem`) if and only if there is an `X`-tree on the
witnesses whose split system is exactly `S` with all the trivial splits (`fam S`). -/
theorem buneman (hn : 2 ≤ n) (r : Fin n) {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) :
    IsSystem r S ↔ ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (φ : Fin n → Fin m),
      IsXTree T φ ∧ splitSides T φ = fam S := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [← exists_xTree_iff (fam_isSplitSystem hn hS), fam_compatible_iff]
  exact ⟨fun h => h.2, fun h => ⟨hS, h⟩⟩

/-- The non-trivial splits of such a tree, read off by their sides away from `r`, are exactly `S`. -/
theorem nontrivial_splits_of_tree {r : Fin n} {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) {m : ℕ} {T : SimpleGraph (Fin m)} {φ : Fin n → Fin m}
    (h : splitSides T φ = fam S) (B : Finset (Fin n)) (hB : IsSide r B) :
    (B : Set (Fin n)) ∈ splitSides T φ ↔ B ∈ S := by
  rw [h]
  constructor
  · rintro (⟨c, hc, e | e⟩ | ⟨x, e | e⟩)
    · rwa [coe_inj.mp e]
    · exfalso
      have : r ∈ (B : Set (Fin n)) := by rw [e]; simpa using (hS c hc).1
      exact hB.1 (mem_coe.mp this)
    · have : B = {x} := by rw [← coe_inj, coe_singleton]; exact e
      have := hB.2.1; rw [‹B = {x}›] at this; simp at this
    · have hc : Bᶜ = {x} := by rw [← coe_inj, coe_compl, coe_singleton, e, compl_compl]
      have h2 := hB.2.2; rw [hc] at h2; simp at h2
  · intro hBS; exact Or.inl ⟨B, hBS, Or.inl rfl⟩

/-- **Proposition 3.2 (`prop:buneman`), uniqueness.**  Two `X`-trees with the same split system are
isomorphic by a graph isomorphism that respects the labels. -/
theorem buneman_unique {m m' : ℕ} {T : SimpleGraph (Fin m)} {T' : SimpleGraph (Fin m')}
    {φ : Fin n → Fin m} {φ' : Fin n → Fin m'} (hT : IsXTree T φ) (hT' : IsXTree T' φ')
    (h : splitSides T φ = splitSides T' φ') (hn : 0 < n) :
    ∃ f : T ≃g T', ∀ x, f (φ x) = φ' x := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact xTree_unique hT hT' h

end Stemma.Buneman
