/-
Every split system extends to the split system of a binary stemma: a pairwise compatible set of
non-trivial splits on `n ≥ 3` witnesses lies in one of exactly `n - 3` (the resolution of
polytomies, used in the proof of Theorem 7.14(a) of the technical report).

Proved on laminar families, without trees: a laminar family of subsets of `U` with between `2` and
`|U| - 1` elements extends to one with exactly `|U| - 2` members.  Induction on `|U|`: choose two
elements `a ≠ b` that no member separates (two elements of a minimal member, or any two if the
family is empty), delete `b`, extend on `U \ {b}`, put `b` back beside `a`, and add `{a, b}`.

Consequence: the hypothesis `Cutting.Resolvable` holds for every `r`, so Theorem 7.14(a) holds
outright (`completable_iff_displayed'`).
-/
import Mathlib
import StemmaLean.Cutting

namespace Stemma.Resolve

open Finset Splits

section laminar

variable {α : Type*} [DecidableEq α]

/-- The bounds on the members of the family: inside `U`, at least two elements, not all of `U`. -/
def Inside (U : Finset α) (F : Finset (Finset α)) : Prop := ∀ A ∈ F, A ⊆ U ∧ 2 ≤ A.card ∧ A ≠ U

/-- Put `b` back beside `a`. -/
def lift (a b : α) (X : Finset α) : Finset α := if a ∈ X then insert b X else X

/-- **Extension of laminar families.**  If `|U| = k + 2`, every laminar family inside `U` (members
of size between `2` and `|U| - 1`) is contained in one with exactly `k` members. -/
theorem laminar_extend (k : ℕ) : ∀ (U : Finset α) (F : Finset (Finset α)), U.card = k + 2 →
    Laminar F → Inside U F → ∃ G, F ⊆ G ∧ Laminar G ∧ Inside U G ∧ G.card = k := by
  induction k with
  | zero =>
    intro U F hU _ hF
    have hFe : F = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intro A hA
      obtain ⟨h1, h2, h3⟩ := hF A hA
      exact h3 (eq_of_subset_of_card_le h1 (by omega))
    exact ⟨∅, by simp [hFe], fun A hA => by simp at hA, fun A hA => by simp at hA, rfl⟩
  | succ k ih =>
    intro U F hU hL hF
    -- two elements that no member separates
    obtain ⟨a, ha, b, hb, hab, hsep⟩ : ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ ∀ S ∈ F, (a ∈ S ↔ b ∈ S) := by
      rcases F.eq_empty_or_nonempty with he | hne
      · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < U.card)
        exact ⟨a, ha, b, hb, hab, fun S hS => by simp [he] at hS⟩
      · obtain ⟨M, hMmin⟩ := F.exists_minimal hne
        have hM : M ∈ F := hMmin.prop
        have hmin : ∀ S ∈ F, S ⊆ M → S = M := fun S hS h =>
          le_antisymm h (hMmin.le_of_le hS h)
        obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by have := (hF M hM).2.1; omega : 1 < M.card)
        refine ⟨a, (hF M hM).1 ha, b, (hF M hM).1 hb, hab, fun S hS => ?_⟩
        have key : ∀ x ∈ M, x ∈ S → M ⊆ S := fun x hx hxS => by
          rcases hL S hS M hM with h | h | h
          · exact absurd hx (disjoint_left.mp h hxS)
          · rw [hmin S hS h]
          · exact h
        exact ⟨fun h => key a ha h hb, fun h => key b hb h ha⟩
    set U' := U.erase b
    have hU' : U'.card = k + 2 := by rw [card_erase_of_mem hb]; omega
    have haU' : a ∈ U' := mem_erase.mpr ⟨hab, ha⟩
    set F' := (F.filter fun S => S ≠ {a, b}).image fun S => S.erase b
    have hL' : Laminar F' := by
      intro A hA B hB
      simp only [F', mem_image, mem_filter] at hA hB
      obtain ⟨S, ⟨hS, -⟩, rfl⟩ := hA
      obtain ⟨S', ⟨hS', -⟩, rfl⟩ := hB
      rcases hL S hS S' hS' with h | h | h
      · exact Or.inl (disjoint_of_subset_left (erase_subset _ _)
          (disjoint_of_subset_right (erase_subset _ _) h))
      · exact Or.inr (Or.inl (erase_subset_erase _ h))
      · exact Or.inr (Or.inr (erase_subset_erase _ h))
    have hF' : Inside U' F' := by
      intro A hA
      simp only [F', mem_image, mem_filter] at hA
      obtain ⟨S, ⟨hS, hSne⟩, rfl⟩ := hA
      obtain ⟨h1, h2, h3⟩ := hF S hS
      refine ⟨erase_subset_erase _ h1, ?_, ?_⟩
      · by_cases hbS : b ∈ S
        · have haS : a ∈ S := (hsep S hS).mpr hbS
          have hsub : ({a, b} : Finset α) ⊂ S := ssubset_of_subset_of_ne
            (by intro x hx; simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption) (Ne.symm hSne)
          have := card_lt_card hsub
          rw [card_pair hab] at this
          rw [card_erase_of_mem hbS]; omega
        · rw [erase_eq_of_notMem hbS]; exact h2
      · intro e
        by_cases hbS : b ∈ S
        · apply h3
          rw [← insert_erase hbS, ← insert_erase hb, e]
        · rw [erase_eq_of_notMem hbS] at e
          have : a ∈ S := e ▸ haU'
          exact hbS ((hsep S hS).mp this)
    obtain ⟨G', hFG', hLG', hG', hcard⟩ := ih U' F' hU' hL' hF'
    have hbG' : ∀ X ∈ G', b ∉ X := fun X hX hbX => by
      have := (hG' X hX).1 hbX; simp [U'] at this
    -- lift back and add `{a, b}`
    refine ⟨insert {a, b} (G'.image (lift a b)), ?_, ?_, ?_, ?_⟩
    · intro S hS
      by_cases e : S = {a, b}
      · rw [e]; exact mem_insert_self _ _
      apply mem_insert_of_mem
      refine mem_image.mpr ⟨S.erase b, hFG' (mem_image.mpr ⟨S, mem_filter.mpr ⟨hS, e⟩, rfl⟩), ?_⟩
      unfold lift
      by_cases hbS : b ∈ S
      · have haS : a ∈ (S.erase b) := mem_erase.mpr ⟨hab, (hsep S hS).mpr hbS⟩
        rw [if_pos haS, insert_erase hbS]
      · have haS : a ∉ S.erase b := fun h => hbS ((hsep S hS).mp (mem_of_mem_erase h))
        rw [if_neg haS, erase_eq_of_notMem hbS]
    · intro A hA B hB
      rw [mem_insert] at hA hB
      have pair_lam : ∀ X ∈ G', Disjoint ({a, b} : Finset α) (lift a b X) ∨
          ({a, b} : Finset α) ⊆ lift a b X ∨ lift a b X ⊆ {a, b} := by
        intro X hX
        unfold lift
        by_cases haX : a ∈ X
        · right; left; rw [if_pos haX]
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact mem_insert_of_mem haX
          · exact mem_insert_self _ _
        · left; rw [if_neg haX, disjoint_left]
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact haX
          · exact hbG' X hX
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact Or.inr (Or.inl subset_rfl)
      · obtain ⟨Y, hY, rfl⟩ := mem_image.mp hB; exact pair_lam Y hY
      · obtain ⟨X, hX, rfl⟩ := mem_image.mp hA
        rcases pair_lam X hX with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · obtain ⟨X, hX, rfl⟩ := mem_image.mp hA
        obtain ⟨Y, hY, rfl⟩ := mem_image.mp hB
        unfold lift
        rcases hLG' X hX Y hY with h | h | h
        · left
          by_cases haX : a ∈ X <;> by_cases haY : a ∈ Y
          · exact absurd haY (disjoint_left.mp h haX)
          · rw [if_pos haX, if_neg haY, disjoint_insert_left]
            exact ⟨hbG' Y hY, h⟩
          · rw [if_neg haX, if_pos haY, disjoint_insert_right]
            exact ⟨hbG' X hX, h⟩
          · rw [if_neg haX, if_neg haY]; exact h
        · right; left
          by_cases haX : a ∈ X
          · rw [if_pos haX, if_pos (h haX)]; exact insert_subset_insert _ h
          · rw [if_neg haX]; split_ifs
            · exact h.trans (subset_insert _ _)
            · exact h
        · right; right
          by_cases haY : a ∈ Y
          · rw [if_pos haY, if_pos (h haY)]; exact insert_subset_insert _ h
          · rw [if_neg haY]; split_ifs
            · exact h.trans (subset_insert _ _)
            · exact h
    · intro A hA
      rw [mem_insert] at hA
      rcases hA with rfl | hA
      · refine ⟨?_, by rw [card_pair hab], fun e => ?_⟩
        · intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · have := congrArg card e; rw [card_pair hab] at this; omega
      · obtain ⟨X, hX, rfl⟩ := mem_image.mp hA
        obtain ⟨h1, h2, h3⟩ := hG' X hX
        unfold lift
        split_ifs with haX
        · refine ⟨insert_subset hb (h1.trans (erase_subset _ _)), ?_, fun e => h3 ?_⟩
          · exact h2.trans (card_le_card (subset_insert _ _))
          · show X = U.erase b
            rw [← e, erase_insert (hbG' X hX)]
        · refine ⟨h1.trans (erase_subset _ _), h2, fun e => hbG' X hX ?_⟩
          rw [e]; exact hb
    · have hinj : Set.InjOn (lift a b) G' := by
        intro X hX Y hY e
        have hX' := hbG' X hX; have hY' := hbG' Y hY
        have : (lift a b X).erase b = (lift a b Y).erase b := by rw [e]
        unfold lift at this
        split_ifs at this <;> simpa [erase_insert, erase_eq_of_notMem, hX', hY'] using this
      have hnot : ({a, b} : Finset α) ∉ G'.image (lift a b) := by
        intro h
        obtain ⟨X, hX, e⟩ := mem_image.mp h
        unfold lift at e
        split_ifs at e with haX
        · have hsub : X ⊆ {a} := by
            intro x hx
            have : x ∈ ({a, b} : Finset α) := e ▸ mem_insert_of_mem hx
            simp only [mem_insert, mem_singleton] at this
            rcases this with rfl | rfl
            · simp
            · exact absurd hx (hbG' X hX)
          have := card_le_card hsub
          have := (hG' X hX).2.1
          simp at *; omega
        · exact haX (e ▸ mem_insert_self a {b})
      rw [card_insert_of_notMem hnot, card_image_of_injOn hinj, hcard]

end laminar

/-- **Every split system lies in that of a binary stemma.**  For `n ≥ 3`, every pairwise compatible
set of non-trivial splits (sides away from `r`) is contained in one of exactly `n - 3`. -/
theorem resolvable {n : ℕ} (r : Fin n) : Cutting.Resolvable r := by
  intro S hS
  rcases Nat.lt_or_ge n 3 with hn | hn
  · -- no non-trivial split exists on fewer than three witnesses
    have hSe : S = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intro A hA
      have h1 := (hS.1 A hA).2.1
      have h2 := (hS.1 A hA).2.2
      have h3 := card_compl A; rw [Fintype.card_fin] at h3
      have h4 := card_le_univ A; rw [Fintype.card_fin] at h4
      omega
    exact ⟨∅, ⟨⟨fun A hA => by simp at hA, fun a ha => by simp at ha⟩, by simp; omega⟩,
      by simp [hSe]⟩
  set U := univ.erase r
  have hU : U.card = (n - 3) + 2 := by simp [U, card_erase_of_mem]; omega
  have hIn : Inside U S := fun A hA => by
    have := side_sub (hS.1 A hA)
    exact ⟨this.1, (hS.1 A hA).2.1, this.2⟩
  obtain ⟨G, hSG, hLG, hG, hcard⟩ := laminar_extend (n - 3) U S hU (laminar_of_system hS) hIn
  have hside : ∀ A ∈ G, IsSide r A := by
    intro A hA
    obtain ⟨h1, h2, h3⟩ := hG A hA
    have hrA : r ∉ A := fun h => by have := h1 h; simp [U] at this
    have hlt := card_lt_card (ssubset_of_subset_of_ne h1 h3)
    refine ⟨hrA, h2, ?_⟩
    rw [card_compl, Fintype.card_fin]
    have : U.card = n - 1 := by simp [U, card_erase_of_mem]
    omega
  refine ⟨G, ⟨⟨hside, fun a ha b hb _ => ?_⟩, hcard⟩, hSG⟩
  exact (compat_iff_laminar (hside a ha).1 (hside b hb).1).mpr (hLG a ha b hb)

/-- **Theorem 7.14(a) (`thm:cuttingconsistency`), unconditional.**  A family of non-trivial
partial splits is jointly completable if and only if some binary stemma displays every member. -/
theorem completable_iff_displayed' {n : ℕ} (r : Fin n) (P : Finset (PSplit n))
    (hP : ∀ s ∈ P, Cutting.NontrivP s) :
    Cutting.JointlyCompletable P ↔ ∃ T, IsBinary r T ∧ ∀ s ∈ P, Cutting.Displays T s :=
  Cutting.completable_iff_displayed r (resolvable r) P hP

end Stemma.Resolve
