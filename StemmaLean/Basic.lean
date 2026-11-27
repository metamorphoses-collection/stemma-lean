/-
Families, compatibility and the deterministic core of the Bédier effect.

* Exclusivity (Lemma 2.5 of the mathematical paper): two families proposed by the same variation
  unit, i.e. two classes of one partition of the witnesses, are compatible.
* Bédier effect (Proposition 3.1, deterministic core): if a family of positive weight is
  compatible with every family of a compatible set `S`, then `S` is not a maximum-weight
  compatible set.  The probabilistic statement then only needs the probability `(1 - m)^L` that no
  unit among `L` proposes that family.
-/
import Mathlib

namespace Stemma

variable {n : ℕ}

/-- Compatibility of two full splits, each given by one side. -/
def Compat (A C : Finset (Fin n)) : Prop :=
  A ∩ C = ∅ ∨ A ∩ Cᶜ = ∅ ∨ Aᶜ ∩ C = ∅ ∨ Aᶜ ∩ Cᶜ = ∅

/-- **Exclusivity.** Disjoint reading classes propose compatible splits. -/
theorem exclusivity {A C : Finset (Fin n)} (h : Disjoint A C) : Compat A C :=
  Or.inl (Finset.disjoint_iff_inter_eq_empty.mp h)

/-- **Exclusivity, for the fibres of a reading map.**  If unit `ρ` gives witness `x` the reading
`ρ x`, the classes of two distinct readings `a ≠ b` propose compatible splits (Lemma 2.5 of the
report, stated for the reading map itself). -/
theorem exclusivity_fibres {β : Type*} [DecidableEq β] (ρ : Fin n → β) {a b : β} (hab : a ≠ b) :
    Compat (Finset.univ.filter (ρ · = a)) (Finset.univ.filter (ρ · = b)) :=
  exclusivity (Finset.disjoint_filter.mpr fun _ _ h1 h2 => hab (h1.symm.trans h2))

/-- A set of families is pairwise compatible. -/
def PairwiseCompat (S : Finset (Finset (Fin n))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Compat a b

/-- Total weight of a set of families. -/
def weight (w : Finset (Fin n) → ℕ) (S : Finset (Finset (Fin n))) : ℕ := ∑ s ∈ S, w s

/-- `S` is a maximum-weight pairwise compatible set. -/
def IsOptimal (w : Finset (Fin n) → ℕ) (S : Finset (Finset (Fin n))) : Prop :=
  PairwiseCompat S ∧ ∀ T, PairwiseCompat T → weight w T ≤ weight w S

lemma compat_symm {A C : Finset (Fin n)} (h : Compat A C) : Compat C A := by
  unfold Compat at *
  rcases h with h | h | h | h
  · exact Or.inl (by rw [Finset.inter_comm]; exact h)
  · exact Or.inr (Or.inr (Or.inl (by rw [Finset.inter_comm]; exact h)))
  · exact Or.inr (Or.inl (by rw [Finset.inter_comm]; exact h))
  · exact Or.inr (Or.inr (Or.inr (by rw [Finset.inter_comm]; exact h)))

/-- **Bédier effect, deterministic core.** If a family `τ ∉ S` of positive weight is compatible
with every member of a compatible set `S`, then `S ∪ {τ}` is compatible and strictly heavier, so
`S` is not optimal. -/
theorem bedier_core (w : Finset (Fin n) → ℕ) (S : Finset (Finset (Fin n))) (τ : Finset (Fin n))
    (hS : PairwiseCompat S) (hτ : τ ∉ S) (hcomp : ∀ s ∈ S, Compat τ s) (hw : 0 < w τ) :
    ¬ IsOptimal w S := by
  rintro ⟨-, hopt⟩
  have hT : PairwiseCompat (insert τ S) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hcomp b hb
    · exact compat_symm (hcomp a ha)
    · exact hS a ha b hb hab
  have hle := hopt _ hT
  unfold weight at hle
  rw [Finset.sum_insert hτ] at hle
  omega

end Stemma
