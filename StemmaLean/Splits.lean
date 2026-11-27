/-
Split systems: the counting facts, the displacement matching, and the separation certificates.

A stemma is represented by its split system, not by a graph tree.  An unordered full split
`A | Aᶜ` of the witnesses `Fin n` is recorded by its side away from a fixed reference witness `r`
(each unordered bipartition has exactly one such side, `side_away`), so a set of splits is a
`Finset (Finset (Fin n))` of sides not containing `r`.  Compatibility is `Stemma.Compat` of
`Basic.lean` (one of the four intersections is empty); on sides away from `r` it is laminarity
(`compat_iff_laminar`).

Formalised, from the technical report:
* Lemma 3.3 (`lem:facts`) (i): a pairwise compatible set of non-trivial full splits has at most
  `n - 3` elements (`card_le`, proved by induction on laminar families, without trees);
  (ii), second half: a set of `n - 3` such splits is maximal (`maximal`).
* Lemma 6.1 (`lem:hall`), displacement matching (`displacement_matching`), from Mathlib's Hall
  marriage theorem.
* Theorem 6.2 (`thm:local`), local separation; Theorem 6.3 (`thm:global`), global separation;
  Proposition 6.9 (`prop:threshold`), the threshold for non-binary stemmata.
* Auxiliary: every non-trivial split is crossed by a non-trivial split (`exists_conflict`),
  which gives positivity of true supports in Theorem 5.2.

"Binary" (`IsBinary`) is defined as: a pairwise compatible set of exactly `n - 3` non-trivial
splits.  The report's Lemma 3.3(ii), first half, shows that the split system of a binary tree has
`n - 3` splits (a degree count on the tree), and Buneman's theorem (Prop. 2.2) gives the converse;
both are formalised on trees in `BinaryTree.lean` (`isBinary_iff_binary_tree`: the systems of
`n - 3` sides are exactly the split systems of binary trees).  Every theorem below therefore
applies to every binary stemma, through its split system.
-/
import Mathlib
import StemmaLean.Basic

namespace Stemma.Splits

open Finset

variable {n : ℕ}

/-! ### Splits recorded by one side -/

/-- `A` is one side of a non-trivial full split: both sides have at least two witnesses. -/
def Nontriv (A : Finset (Fin n)) : Prop := 2 ≤ A.card ∧ 2 ≤ Aᶜ.card

/-- `A` is the side away from the reference witness `r` of a non-trivial full split. -/
def IsSide (r : Fin n) (A : Finset (Fin n)) : Prop := r ∉ A ∧ Nontriv A

/-- A set of non-trivial full splits (each by its side away from `r`), pairwise compatible: the
split system of a stemma (Buneman's theorem, Prop. 2.2 of the report). -/
def IsSystem (r : Fin n) (S : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ S, IsSide r A) ∧ PairwiseCompat S

/-- The split system of a binary stemma: a pairwise compatible set of exactly `n - 3` non-trivial
splits (Lemma 3.3(ii) and Prop. 2.2 of the report; see the file header). -/
def IsBinary (r : Fin n) (T : Finset (Finset (Fin n))) : Prop :=
  IsSystem r T ∧ T.card = n - 3

/-- Every unordered bipartition `{A, Aᶜ}` has exactly one side away from `r`. -/
theorem side_away (r : Fin n) (A : Finset (Fin n)) :
    (r ∉ A ∧ r ∈ Aᶜ) ∨ (r ∈ A ∧ r ∉ Aᶜ) := by
  by_cases h : r ∈ A <;> simp [h]

lemma nontriv_compl {A : Finset (Fin n)} : Nontriv Aᶜ ↔ Nontriv A := by
  unfold Nontriv; rw [compl_compl]; exact and_comm

lemma compat_compl_left {A C : Finset (Fin n)} : Compat Aᶜ C ↔ Compat A C := by
  unfold Compat; rw [compl_compl]; tauto

lemma compat_self (A : Finset (Fin n)) : Compat A A :=
  Or.inr (Or.inl (by simp))

/-- On sides away from `r`, compatibility is laminarity. -/
theorem compat_iff_laminar {r : Fin n} {A C : Finset (Fin n)} (hA : r ∉ A) (hC : r ∉ C) :
    Compat A C ↔ Disjoint A C ∨ A ⊆ C ∨ C ⊆ A := by
  unfold Compat
  rw [disjoint_iff_inter_eq_empty]
  have key : ∀ X Y : Finset (Fin n), X ∩ Yᶜ = ∅ ↔ X ⊆ Y := by
    intro X Y
    constructor
    · intro h x hx
      by_contra hc
      have : x ∈ X ∩ Yᶜ := by simp [hx, hc]
      simp [h] at this
    · intro h; ext x; simp only [mem_inter, mem_compl, notMem_empty, iff_false, not_and,
        not_not]; exact fun hx => h hx
  have h1 : A ∩ Cᶜ = ∅ ↔ A ⊆ C := key A C
  have h2 : Aᶜ ∩ C = ∅ ↔ C ⊆ A := by rw [inter_comm]; exact key C A
  have h3 : ¬ Aᶜ ∩ Cᶜ = ∅ := by
    intro h
    have : r ∈ Aᶜ ∩ Cᶜ := by simp [hA, hC]
    rw [h] at this; simp at this
  rw [h1, h2]; tauto

/-! ### Laminar families -/

/-- A laminar family: any two members are disjoint or nested. -/
def Laminar {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

section laminar

variable {α : Type*} [DecidableEq α]

/-- A laminar family of subsets of `U`, each with at least two elements, has at most `|U| - 1`
members.  Induction on `|U|`: delete one element `b` of an inclusion-minimal member `M`. -/
theorem laminar_card (k : ℕ) : ∀ (U : Finset α) (F : Finset (Finset α)), U.card = k →
    Laminar F → (∀ A ∈ F, A ⊆ U ∧ 2 ≤ A.card) → F = ∅ ∨ F.card + 1 ≤ U.card := by
  induction k with
  | zero =>
    intro U F hU _ hF
    left
    rw [card_eq_zero] at hU
    subst hU
    rw [eq_empty_iff_forall_notMem]
    intro A hA
    have := hF A hA
    rw [subset_empty] at this
    simp [this.1] at this
  | succ k ih =>
    intro U F hU hL hF
    rcases F.eq_empty_or_nonempty with h | hne
    · exact Or.inl h
    right
    obtain ⟨M, hMmin⟩ := F.exists_minimal hne
    have hM : M ∈ F := hMmin.prop
    have hmin : ∀ S ∈ F, S ⊆ M → S = M := fun S hS h =>
      le_antisymm h (hMmin.le_of_le hS h)
    have hM2 := (hF M hM).2
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < M.card)
    -- every member containing `b` contains `M`
    have hcont : ∀ S ∈ F, b ∈ S → M ⊆ S := by
      intro S hS hbS
      rcases hL S hS M hM with h | h | h
      · exact absurd hb (disjoint_left.mp h hbS)
      · rw [hmin S hS h]
      · exact h
    -- deleting `b` is injective on the other members
    have hside : ∀ S ∈ F.erase M, ∀ S' ∈ F.erase M, b ∈ S → b ∉ S' →
        S.erase b ≠ S'.erase b := by
      intro S hS S' hS' hbS hbS' heq
      have haS : a ∈ S := hcont S (mem_of_mem_erase hS) hbS ha
      have haS' : a ∈ S' := by
        have : a ∈ S.erase b := mem_erase.mpr ⟨hab, haS⟩
        rw [heq] at this; exact mem_of_mem_erase this
      rcases hL S' (mem_of_mem_erase hS') M hM with h | h | h
      · exact disjoint_left.mp h haS' ha
      · exact (ne_of_mem_erase hS') (hmin S' (mem_of_mem_erase hS') h)
      · exact hbS' (h hb)
    have hinj : Set.InjOn (fun S : Finset α => S.erase b) ↑(F.erase M) := by
      intro S hS S' hS' heq
      simp only [coe_erase, Set.mem_sdiff, mem_coe] at hS hS'
      by_cases hbS : b ∈ S <;> by_cases hbS' : b ∈ S'
      · rw [← insert_erase hbS, ← insert_erase hbS']; exact congrArg _ heq
      · exact absurd heq (hside S (mem_erase.mpr ⟨hS.2, hS.1⟩) S'
          (mem_erase.mpr ⟨hS'.2, hS'.1⟩) hbS hbS')
      · exact absurd heq.symm (hside S' (mem_erase.mpr ⟨hS'.2, hS'.1⟩) S
          (mem_erase.mpr ⟨hS.2, hS.1⟩) hbS' hbS)
      · simpa [erase_eq_of_notMem hbS, erase_eq_of_notMem hbS'] using heq
    set F' := (F.erase M).image (fun S => S.erase b) with hF'
    have hcardF' : F'.card + 1 = F.card := by
      rw [hF', card_image_of_injOn hinj, card_erase_of_mem hM]
      have : 0 < F.card := card_pos.mpr hne
      omega
    have hbU : b ∈ U := (hF M hM).1 hb
    have hU' : (U.erase b).card = k := by rw [card_erase_of_mem hbU]; omega
    have hL' : Laminar F' := by
      intro A hA B hB
      simp only [hF', mem_image] at hA hB
      obtain ⟨S, hS, rfl⟩ := hA
      obtain ⟨S', hS', rfl⟩ := hB
      rcases hL S (mem_of_mem_erase hS) S' (mem_of_mem_erase hS') with h | h | h
      · exact Or.inl (disjoint_of_subset_left (erase_subset _ _)
          (disjoint_of_subset_right (erase_subset _ _) h))
      · exact Or.inr (Or.inl (erase_subset_erase _ h))
      · exact Or.inr (Or.inr (erase_subset_erase _ h))
    have hF'b : ∀ A ∈ F', A ⊆ U.erase b ∧ 2 ≤ A.card := by
      intro A hA
      simp only [hF', mem_image] at hA
      obtain ⟨S, hS, rfl⟩ := hA
      have hSF := mem_of_mem_erase hS
      refine ⟨erase_subset_erase _ (hF S hSF).1, ?_⟩
      by_cases hbS : b ∈ S
      · have hMS : M ⊂ S := ssubset_of_subset_of_ne (hcont S hSF hbS)
          (fun h => ne_of_mem_erase hS h.symm)
        have := card_lt_card hMS
        rw [card_erase_of_mem hbS]; omega
      · rw [erase_eq_of_notMem hbS]; exact (hF S hSF).2
    have hMU : M.card ≤ U.card := card_le_card (hF M hM).1
    rcases ih (U.erase b) F' hU' hL' hF'b with h | h
    · have : F.card = 1 := by rw [← hcardF', h, card_empty]
      omega
    · omega

end laminar

/-! ### The counting facts (Lemma 3.3 of the report) -/

lemma laminar_of_system {r : Fin n} {S : Finset (Finset (Fin n))} (hS : IsSystem r S) :
    Laminar S := by
  intro A hA B hB
  by_cases hAB : A = B
  · subst hAB; exact Or.inr (Or.inl subset_rfl)
  exact (compat_iff_laminar (hS.1 A hA).1 (hS.1 B hB).1).mp (hS.2 A hA B hB hAB)

lemma side_sub {r : Fin n} {A : Finset (Fin n)} (h : IsSide r A) :
    A ⊆ univ.erase r ∧ A ≠ univ.erase r := by
  refine ⟨fun x hx => mem_erase.mpr ⟨fun e => h.1 (e ▸ hx), mem_univ x⟩, ?_⟩
  intro e
  have h2 := h.2.2
  have : Aᶜ = {r} := by
    rw [e]; ext x; simp [eq_comm]
  rw [this, card_singleton] at h2
  omega

/-- **Lemma 3.3(i) (`lem:facts`).** A pairwise compatible set of non-trivial full splits has at
most `n - 3` elements.  (Proved directly on split systems, by induction on laminar families, rather
than through Buneman's theorem and a degree count as in the report.) -/
theorem card_le {r : Fin n} {S : Finset (Finset (Fin n))} (hS : IsSystem r S) :
    S.card ≤ n - 3 := by
  rcases S.eq_empty_or_nonempty with h | ⟨A, hA⟩
  · simp [h]
  set U := univ.erase r
  have hUcard : U.card = n - 1 := by simp [U, card_erase_of_mem]
  have hUS : U ∉ S := fun hU => (side_sub (hS.1 U hU)).2 rfl
  have hAU := side_sub (hS.1 A hA)
  have hA2 := (hS.1 A hA).2.1
  have hlt := card_lt_card (ssubset_of_subset_of_ne hAU.1 hAU.2)
  have hL : Laminar (insert U S) := by
    intro X hX Y hY
    rw [mem_insert] at hX hY
    rcases hX with rfl | hX <;> rcases hY with rfl | hY
    · exact Or.inr (Or.inl subset_rfl)
    · exact Or.inr (Or.inr (side_sub (hS.1 Y hY)).1)
    · exact Or.inr (Or.inl (side_sub (hS.1 X hX)).1)
    · exact laminar_of_system hS X hX Y hY
  have hb : ∀ X ∈ insert U S, X ⊆ U ∧ 2 ≤ X.card := by
    intro X hX
    rw [mem_insert] at hX
    rcases hX with hX | hX
    · rw [hX]; exact ⟨subset_rfl, hA2.trans hlt.le⟩
    · exact ⟨(side_sub (hS.1 X hX)).1, (hS.1 X hX).2.1⟩
  rcases laminar_card _ U (insert U S) rfl hL hb with h | h
  · exact absurd (h ▸ mem_insert_self U S) (notMem_empty _)
  · rw [card_insert_of_notMem hUS] at h; omega

/-- **Lemma 3.3(ii) (`lem:facts`), maximality.**  Every non-trivial split compatible with all
splits of a binary stemma belongs to it. -/
theorem maximal {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    {τ : Finset (Fin n)} (hτ : IsSide r τ) (hc : ∀ σ ∈ T, Compat τ σ) : τ ∈ T := by
  by_contra hnot
  have hsys : IsSystem r (insert τ T) := by
    refine ⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩
    · rw [mem_insert] at hA; rcases hA with rfl | hA
      · exact hτ
      · exact hT.1.1 A hA
    · rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hc b hb
      · exact compat_symm (hc a ha)
      · exact hT.1.2 a ha b hb hab
  have := card_le hsys
  rw [card_insert_of_notMem hnot, hT.2] at this
  omega

/-! ### Displacement matching (Lemma 6.1 of the report) -/

/-- **Lemma 6.1 (`lem:hall`), displacement matching.**  Let `T` be (the split system of) a binary
stemma and `S ≠ T` a pairwise compatible set of non-trivial splits; put `A = T \ S`,
`B = S \ T`.  Then `A ≠ ∅`, `|B| ≤ |A|`, and there is an injection `φ : B → A` with `τ` and
`φ τ` in conflict for every `τ ∈ B`.  The matching comes from Mathlib's Hall marriage theorem. -/
theorem displacement_matching {r : Fin n} {T S : Finset (Finset (Fin n))}
    (hT : IsBinary r T) (hS : IsSystem r S) (hne : S ≠ T) :
    (T \ S).Nonempty ∧ (S \ T).card ≤ (T \ S).card ∧
    ∃ φ : ↥(S \ T) → Finset (Fin n), Function.Injective φ ∧
      ∀ τ, φ τ ∈ T \ S ∧ ¬ Compat τ.1 (φ τ) := by
  classical
  -- neighbourhoods along conflicts
  let t : ↥(S \ T) → Finset (Finset (Fin n)) := fun τ => (T \ S).filter (fun σ => ¬ Compat τ.1 σ)
  have hHall : ∀ s : Finset ↥(S \ T), s.card ≤ (s.biUnion t).card := by
    intro s
    set N := s.biUnion t
    set B' := s.map (Function.Embedding.subtype _)
    have hB'S : B' ⊆ S \ T := by
      intro x hx; simp only [B', mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, -, rfl⟩ := hx; exact y.2
    have hNT : N ⊆ T \ S := by
      intro x hx; simp only [N, t, mem_biUnion, mem_filter] at hx
      obtain ⟨_, _, h, _⟩ := hx; exact h
    have hsys : IsSystem r ((T \ N) ∪ B') := by
      refine ⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩
      · rcases mem_union.mp hA with h | h
        · exact hT.1.1 A (mem_sdiff.mp h).1
        · exact hS.1 A (mem_sdiff.mp (hB'S h)).1
      -- a true split outside `N` is compatible with every member of `B'`
      have cross : ∀ σ ∈ T \ N, ∀ τ ∈ B', Compat τ σ := by
        intro σ hσ τ hτ
        obtain ⟨hσT, hσN⟩ := mem_sdiff.mp hσ
        have hτ' := mem_sdiff.mp (hB'S hτ)
        have hne' : τ ≠ σ := fun e => hτ'.2 (e ▸ hσT)
        by_cases hσS : σ ∈ S
        · exact hS.2 τ hτ'.1 σ hσS hne'
        · by_contra hc
          apply hσN
          simp only [B', mem_map, Function.Embedding.coe_subtype] at hτ
          obtain ⟨y, hy, rfl⟩ := hτ
          simp only [N, t, mem_biUnion, mem_filter]
          exact ⟨y, hy, mem_sdiff.mpr ⟨hσT, hσS⟩, hc⟩
      rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
      · exact hT.1.2 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab
      · exact compat_symm (cross a ha b hb)
      · exact cross b hb a ha
      · exact hS.2 a (mem_sdiff.mp (hB'S ha)).1 b (mem_sdiff.mp (hB'S hb)).1 hab
    have hle := card_le hsys
    have hdisj : Disjoint (T \ N) B' := by
      rw [disjoint_left]; intro x hx hx'
      exact (mem_sdiff.mp (hB'S hx')).2 (mem_sdiff.mp hx).1
    rw [card_union_of_disjoint hdisj, card_sdiff_of_subset (hNT.trans sdiff_subset), hT.2.symm,
      card_map] at hle
    have : N.card ≤ T.card := card_le_card (hNT.trans sdiff_subset)
    omega
  obtain ⟨φ, hφinj, hφ⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hφ' : ∀ τ, φ τ ∈ T \ S ∧ ¬ Compat τ.1 (φ τ) := fun τ => by
    have := hφ τ; simp only [t, mem_filter] at this; exact this
  refine ⟨?_, ?_, φ, hφinj, hφ'⟩
  · rw [nonempty_iff_ne_empty]
    intro hA
    have hTS : T ⊂ S := ssubset_of_subset_of_ne (sdiff_eq_empty_iff_subset.mp hA) hne.symm
    have := card_lt_card hTS
    have := card_le hS
    rw [hT.2] at *; omega
  · have h := hHall univ
    have hsub : univ.biUnion t ⊆ T \ S := by
      intro x hx; simp only [t, mem_biUnion, mem_filter] at hx
      obtain ⟨_, _, h, _⟩ := hx; exact h
    have := card_le_card hsub
    rw [card_univ, Fintype.card_coe] at h
    omega

/-! ### Separation certificates (Theorems 6.2, 6.3 and Proposition 6.9 of the report) -/

/-- Total weight of a set of splits. -/
def wt (w : Finset (Fin n) → ℝ) (S : Finset (Finset (Fin n))) : ℝ := ∑ σ ∈ S, w σ

/-- `T` is the unique solution of the best-supported-stemma problem (report, eq. (1)): a pairwise
compatible set of candidates (splits of positive weight) strictly heavier than every other
pairwise compatible set of candidates. -/
def IsUniqueSolution (r : Fin n) (w : Finset (Fin n) → ℝ) (T : Finset (Finset (Fin n))) : Prop :=
  IsSystem r T ∧ (∀ σ ∈ T, 0 < w σ) ∧
    ∀ S, IsSystem r S → (∀ τ ∈ S, 0 < w τ) → S ≠ T → wt w S < wt w T

/-- Normalise a side to the side away from `r`. -/
def away (r : Fin n) (A : Finset (Fin n)) : Finset (Fin n) := if r ∈ A then Aᶜ else A

lemma isSide_away {r : Fin n} {A : Finset (Fin n)} (h : Nontriv A) : IsSide r (away r A) := by
  unfold away; split_ifs with hr
  · exact ⟨by simp [hr], nontriv_compl.mpr h⟩
  · exact ⟨hr, h⟩

lemma compat_away {r : Fin n} {A C : Finset (Fin n)} : Compat (away r A) C ↔ Compat A C := by
  unfold away; split_ifs
  · exact compat_compl_left
  · exact Iff.rfl

/-- Every non-trivial split is crossed by some non-trivial split: with `a₁ ≠ a₂` on one side and
`b₁ ≠ b₂` on the other, `{a₁, b₁}` crosses it.  (The report argues on the tree for a true split of
a binary stemma; this holds for every non-trivial split.) -/
theorem exists_conflict (r : Fin n) {σ : Finset (Fin n)} (hσ : Nontriv σ) :
    ∃ τ, IsSide r τ ∧ ¬ Compat τ σ := by
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := one_lt_card.mp (by have := hσ.1; omega : 1 < σ.card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := one_lt_card.mp (by have := hσ.2; omega : 1 < σᶜ.card)
  rw [mem_compl] at hb₁ hb₂
  have h11 : a₁ ≠ b₁ := fun e => hb₁ (e ▸ ha₁)
  have h21 : a₂ ≠ b₁ := fun e => hb₁ (e ▸ ha₂)
  have h12 : a₁ ≠ b₂ := fun e => hb₂ (e ▸ ha₁)
  have h22 : a₂ ≠ b₂ := fun e => hb₂ (e ▸ ha₂)
  set τ₀ : Finset (Fin n) := {a₁, b₁}
  have hτ₀ : Nontriv τ₀ := by
    refine ⟨by rw [card_pair h11], ?_⟩
    have hsub : ({a₂, b₂} : Finset (Fin n)) ⊆ τ₀ᶜ := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [τ₀, mem_compl, mem_insert, mem_singleton]
      rcases hx with rfl | rfl
      · push Not; exact ⟨fun e => ha (e.symm), h21⟩
      · push Not; exact ⟨h12.symm, fun e => hb (e.symm)⟩
    have := card_le_card hsub
    rw [card_pair h22] at this; exact this
  refine ⟨away r τ₀, isSide_away hτ₀, ?_⟩
  rw [compat_away]
  unfold Compat
  have ne : ∀ (X : Finset (Fin n)) (x : Fin n), x ∈ X → X ≠ ∅ := fun X x hx h => by
    rw [h] at hx; simp at hx
  refine not_or.mpr ⟨ne _ a₁ ?_, not_or.mpr ⟨ne _ b₁ ?_, not_or.mpr ⟨ne _ a₂ ?_, ne _ b₂ ?_⟩⟩⟩
  · simp [τ₀, ha₁]
  · simp [τ₀, hb₁]
  · simp [τ₀, ha₂, ha.symm, h21]
  · simp [τ₀, hb₂, h12.symm, hb.symm]

/-- A split in conflict with a member of a split system is not in it. -/
lemma not_mem_of_conflict {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsSystem r T)
    {σ τ : Finset (Fin n)} (hσ : σ ∈ T) (hc : ¬ Compat τ σ) : τ ∉ T := by
  intro hτ
  by_cases e : τ = σ
  · exact hc (e ▸ compat_self σ)
  · exact hc (hT.2 τ hτ σ hσ e)

/-- Local separation, strong form: under the hypotheses of Theorem 6.2, every true split has
positive weight and `T` is strictly heavier than every other pairwise compatible set of
non-trivial splits (candidates or not). -/
theorem local_separation_strong {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsSide r A → 0 ≤ w A)
    (hloc : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ → w τ < w σ) :
    (∀ σ ∈ T, 0 < w σ) ∧ ∀ S, IsSystem r S → S ≠ T → wt w S < wt w T := by
  have hpos : ∀ σ ∈ T, 0 < w σ := by
    intro σ hσ
    obtain ⟨τ, hτ, hc⟩ := exists_conflict r (hT.1.1 σ hσ).2
    have := hloc τ σ hτ (not_mem_of_conflict hT.1 hσ hc) hσ hc
    linarith [hw0 τ hτ]
  refine ⟨hpos, fun S hS hne => ?_⟩
  obtain ⟨hA, -, φ, hφinj, hφ⟩ := displacement_matching hT hS hne
  have hdiff : wt w T - wt w S = ∑ σ ∈ T \ S, w σ - ∑ τ ∈ S \ T, w τ :=
    (Finset.sum_sdiff_sub_sum_sdiff).symm
  -- `w(B) ≤ w(φ(B)) ≤ w(A)`, strictly if `B ≠ ∅`
  have himg : ∑ τ : ↥(S \ T), w (φ τ) = ∑ σ ∈ univ.image φ, w σ :=
    (sum_image (fun x _ y _ h => hφinj h)).symm
  have hsub : univ.image φ ⊆ T \ S := by
    intro x hx; simp only [mem_image] at hx; obtain ⟨y, -, rfl⟩ := hx; exact (hφ y).1
  have hle : ∑ σ ∈ univ.image φ, w σ ≤ ∑ σ ∈ T \ S, w σ :=
    sum_le_sum_of_subset_of_nonneg hsub fun σ hσ _ => (hpos σ (mem_sdiff.mp hσ).1).le
  have hB : ∑ τ ∈ S \ T, w τ = ∑ τ : ↥(S \ T), w τ.1 := (sum_coe_sort _ _).symm
  rcases (S \ T).eq_empty_or_nonempty with hBe | hBne
  · have : 0 < ∑ σ ∈ T \ S, w σ :=
      sum_pos (fun σ hσ => hpos σ (mem_sdiff.mp hσ).1) hA
    rw [hBe, sum_empty] at hdiff
    linarith
  · have hlt : ∑ τ : ↥(S \ T), w τ.1 < ∑ τ : ↥(S \ T), w (φ τ) := by
      apply sum_lt_sum_of_nonempty
      · obtain ⟨x, hx⟩ := hBne; exact ⟨⟨x, hx⟩, mem_univ _⟩
      · intro τ _
        have hτ := mem_sdiff.mp τ.2
        exact hloc τ.1 (φ τ) (hS.1 _ hτ.1) hτ.2 (mem_sdiff.mp (hφ τ).1).1 (hφ τ).2
    linarith

/-- **Theorem 6.2 (`thm:local`), local separation.**  Let `T` be binary and `w ≥ 0` on all
non-trivial splits.  If `w τ < w σ` whenever a false split `τ` and a true split `σ` are in
conflict, then `T` is the unique solution of the best-supported-stemma problem. -/
theorem local_separation {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsSide r A → 0 ≤ w A)
    (hloc : ∀ τ σ, IsSide r τ → τ ∉ T → σ ∈ T → ¬ Compat τ σ → w τ < w σ) :
    IsUniqueSolution r w T := by
  obtain ⟨hpos, hlt⟩ := local_separation_strong hT w hw0 hloc
  exact ⟨hT.1, hpos, fun S hS _ hne => hlt S hS hne⟩

/-- **Theorem 6.3 (`thm:global`), global separation.**  Let `T` be binary and `w ≥ 0` on all
non-trivial splits.  If every true split is heavier than every false split
(`min_{σ ∈ T} w σ > max_{τ ∉ T} w τ`), then `T` is the unique solution. -/
theorem global_separation {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsSide r A → 0 ≤ w A)
    (hglob : ∀ σ ∈ T, ∀ τ, IsSide r τ → τ ∉ T → w τ < w σ) :
    IsUniqueSolution r w T :=
  local_separation hT w hw0 fun τ σ hτ hτT hσ _ => hglob σ hσ τ hτ hτT

/-- **Proposition 6.9 (`prop:threshold`), threshold for non-binary stemmata.**  Let `T` be the
split system of any stemma with at least one non-trivial split, `w ≥ 0`, and
`max_{τ ∉ T} w τ ≤ t < min_{σ ∈ T} w σ`.  Then the splits of weight greater than `t` are exactly
those of `T`, and `T` is the unique solution of the problem restricted to them: it is a set of
such candidates, of positive weight, strictly heavier than every other pairwise compatible set of
splits of weight greater than `t`. -/
theorem threshold {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsSystem r T)
    (hTne : T.Nonempty) (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsSide r A → 0 ≤ w A) (t : ℝ)
    (hfalse : ∀ τ, IsSide r τ → τ ∉ T → w τ ≤ t) (htrue : ∀ σ ∈ T, t < w σ) :
    (∀ A, IsSide r A → (t < w A ↔ A ∈ T)) ∧ (∀ σ ∈ T, 0 < w σ) ∧
      ∀ S, IsSystem r S → (∀ τ ∈ S, t < w τ) → S ≠ T → wt w S < wt w T := by
  -- some false split exists, so `t ≥ 0`
  obtain ⟨σ₀, hσ₀⟩ := hTne
  obtain ⟨τ₀, hτ₀, hc₀⟩ := exists_conflict r (hT.1 σ₀ hσ₀).2
  have ht0 : 0 ≤ t := (hw0 τ₀ hτ₀).trans (hfalse τ₀ hτ₀ (not_mem_of_conflict hT hσ₀ hc₀))
  have hiff : ∀ A, IsSide r A → (t < w A ↔ A ∈ T) := fun A hA =>
    ⟨fun h => by by_contra hn; linarith [hfalse A hA hn], fun h => htrue A h⟩
  have hpos : ∀ σ ∈ T, 0 < w σ := fun σ hσ => lt_of_le_of_lt ht0 (htrue σ hσ)
  refine ⟨hiff, hpos, fun S hS hSt hne => ?_⟩
  have hST : S ⊆ T := fun τ hτ => (hiff τ (hS.1 τ hτ)).mp (hSt τ hτ)
  have hss : S ⊂ T := ssubset_of_subset_of_ne hST hne
  obtain ⟨x, hxT, hxS⟩ := exists_of_ssubset hss
  unfold wt
  rw [← sum_sdiff hST]
  have : 0 < ∑ σ ∈ T \ S, w σ :=
    sum_pos (fun σ hσ => hpos σ (mem_sdiff.mp hσ).1) ⟨x, mem_sdiff.mpr ⟨hxT, hxS⟩⟩
  linarith

end Stemma.Splits
