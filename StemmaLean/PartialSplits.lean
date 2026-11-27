/-
Fragmentary witnesses: compatibility of partial splits.

Formalises Proposition 5.2 of the technical report ("Pairs are exact, triples are not"),
used in the applied paper (Sec. 2.3) and its supplement S2.

A partial split of the witnesses observed at a unit is given by its domain `Y` (the legible
witnesses) and one side `A ⊆ Y`; the other side is `Y \ A`.  A full split is the case `Y = univ`.
-/
import Mathlib

namespace Stemma

variable {n : ℕ}

/-- A (possibly partial) split: a domain of observed witnesses and one side inside it. -/
structure PSplit (n : ℕ) where
  dom  : Finset (Fin n)
  side : Finset (Fin n)
  sub  : side ⊆ dom
deriving DecidableEq

/-- The other side of a split. -/
def PSplit.other (s : PSplit n) : Finset (Fin n) := s.dom \ s.side

/-- Two splits are compatible on their common witnesses when one of the four intersections of
their sides, restricted to the common domain, is empty. -/
def overlapCompat (s t : PSplit n) : Prop :=
  let W := s.dom ∩ t.dom
  s.side ∩ t.side ∩ W = ∅ ∨ s.side ∩ t.other ∩ W = ∅ ∨
  s.other ∩ t.side ∩ W = ∅ ∨ s.other ∩ t.other ∩ W = ∅

instance (s t : PSplit n) : Decidable (overlapCompat s t) := by
  unfold overlapCompat; infer_instance

/-- Compatibility of two full splits given by one side each (the other side is the complement). -/
def fullCompat (A C : Finset (Fin n)) : Prop :=
  A ∩ C = ∅ ∨ A ∩ Cᶜ = ∅ ∨ Aᶜ ∩ C = ∅ ∨ Aᶜ ∩ Cᶜ = ∅

instance (A C : Finset (Fin n)) : Decidable (fullCompat A C) := by
  unfold fullCompat; infer_instance

/-- `A'` (one side of a full split) extends the partial split `s`. -/
def Extends (s : PSplit n) (A' : Finset (Fin n)) : Prop := A' ∩ s.dom = s.side

instance (s : PSplit n) (A' : Finset (Fin n)) : Decidable (Extends s A') := by
  unfold Extends; infer_instance

/-- Two partial splits are jointly completable if they extend to compatible full splits. -/
def JointPair (s t : PSplit n) : Prop :=
  ∃ A' C', Extends s A' ∧ Extends t C' ∧ fullCompat A' C'

/-- Three partial splits are jointly completable if they extend to pairwise compatible full splits. -/
def JointTriple (s t u : PSplit n) : Prop :=
  ∃ A' C' E', Extends s A' ∧ Extends t C' ∧ Extends u E' ∧
    fullCompat A' C' ∧ fullCompat A' E' ∧ fullCompat C' E'

/-! ### (a) Pairs are exact -/

/-- Two candidate extensions of a partial split: the observed side alone (`s.side`), or
everything except the observed other side (`(s.other)ᶜ`). -/
lemma extends_side (s : PSplit n) : Extends s s.side := by
  unfold Extends
  exact Finset.inter_eq_left.mpr s.sub

lemma extends_compl_other (s : PSplit n) : Extends s (s.other)ᶜ := by
  unfold Extends PSplit.other
  ext x
  have h := s.sub
  by_cases hx : x ∈ s.side
  · simp [hx, h hx]
  · simp [hx]

/-- Elements of a side lie in the domain. -/
lemma mem_dom_of_side {s : PSplit n} {x : Fin n} (hx : x ∈ s.side) : x ∈ s.dom := s.sub hx


lemma other_sub (s : PSplit n) : s.other ⊆ s.dom := by
  unfold PSplit.other; exact Finset.sdiff_subset

/-- If two sets lie inside two domains and are disjoint on the common domain, they are disjoint. -/
lemma inter_empty_of {A C U V : Finset (Fin n)} (hA : A ⊆ U) (hC : C ⊆ V)
    (h : A ∩ C ∩ (U ∩ V) = ∅) : A ∩ C = ∅ := by
  have hsub : A ∩ C ⊆ A ∩ C ∩ (U ∩ V) := fun x hx => by
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨⟨hx.1, hx.2⟩, hA hx.1, hC hx.2⟩
  rw [h] at hsub
  exact Finset.subset_empty.mp hsub

/-- **Pairs are exact.** Two partial splits that are compatible on their common witnesses are
jointly completable. -/
theorem pair_exact (s t : PSplit n) (h : overlapCompat s t) : JointPair s t := by
  unfold overlapCompat at h
  rcases h with h | h | h | h
  · exact ⟨s.side, t.side, extends_side s, extends_side t,
      Or.inl (inter_empty_of s.sub t.sub h)⟩
  · refine ⟨s.side, (t.other)ᶜ, extends_side s, extends_compl_other t, Or.inr (Or.inl ?_)⟩
    rw [compl_compl]; exact inter_empty_of s.sub (other_sub t) h
  · refine ⟨(s.other)ᶜ, t.side, extends_compl_other s, extends_side t,
      Or.inr (Or.inr (Or.inl ?_))⟩
    rw [compl_compl]; exact inter_empty_of (other_sub s) t.sub h
  · refine ⟨(s.other)ᶜ, (t.other)ᶜ, extends_compl_other s, extends_compl_other t,
      Or.inr (Or.inr (Or.inr ?_))⟩
    rw [compl_compl, compl_compl]; exact inter_empty_of (other_sub s) (other_sub t) h

/-! ### (b) Triples are not: the obstruction on five witnesses

Witnesses 1–5 of the paper are `0`–`4` here.
`p = 12|34` observed on `1234`, `q = 12|35` on `1235`, `r = 14|25` on `1245`. -/

def p5 : PSplit 5 := ⟨{0, 1, 2, 3}, {0, 1}, by decide⟩
def q5 : PSplit 5 := ⟨{0, 1, 2, 4}, {0, 1}, by decide⟩
def r5 : PSplit 5 := ⟨{0, 1, 3, 4}, {0, 3}, by decide⟩

theorem triple_pairwise : overlapCompat p5 q5 ∧ overlapCompat p5 r5 ∧ overlapCompat q5 r5 := by
  decide

/-- **Triples are not exact.** The three partial splits are pairwise compatible on their common
witnesses but have no pairwise compatible full extensions. -/
theorem triple_not_joint : ¬ JointTriple p5 q5 r5 := by
  unfold JointTriple
  decide

/-! ### (c) Four witnesses are not enough

A non-trivial partial split needs at least four observed witnesses, so on four witnesses every
non-trivial split is full and pairwise compatibility is joint compatibility. -/

/-- On four witnesses, a split with two witnesses on each side has full domain. -/
theorem four_nontrivial_full (s : PSplit 4) (h1 : 2 ≤ s.side.card) (h2 : 2 ≤ s.other.card) :
    s.dom = Finset.univ := by
  have hcard : s.dom.card = s.side.card + s.other.card := by
    unfold PSplit.other
    have := Finset.card_sdiff_add_card_eq_card s.sub
    omega
  apply Finset.eq_univ_of_card
  have := Finset.card_le_univ s.dom
  simp at this ⊢
  omega

end Stemma
