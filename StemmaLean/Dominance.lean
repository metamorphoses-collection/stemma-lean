/-
Corollary 8.7 of the technical report (`cor:dominance`), the comparison of the codings at second
order, on the attraction model of `Attraction.lean`.

For a split `τ = C | D` (`D = Cᶜ`), the second-order support `Λ` of Theorem 8.6 is the part of the
expected support from outcomes with at most two innovations,
`Λ_P = ex K π α (fun M att => P M att ∧ |M| ≤ 2)`, in closed form `Attraction.lambda_eq`.

* `dominance`: `Λ` of each cluster `C`, `D` in the rooted coding is at most `Λ` of `τ` in the
  unrooted coding.  Lean proves it outcome by outcome: a cluster proposed in the rooted coding is a
  class of a reading, so the unrooted coding proposes its split (`propR_propU`).  The comparison
  therefore holds for every split, true or false, and at every order: the exact expected supports
  satisfy the same inequality (`dominance_exact`).
* `omega_dominance`: the same comparison for the pair weights `ω_{ef}` of the closed form, and
  the report's description of the pairs: a disjoint pair proposing the cluster has `ω = α²` in the
  rooted coding and `1` in the unrooted one (`Attraction.omega_coincidence`,
  `Attraction.omega_retention`); a nested pair has `1 - α²` in both
  (`Attraction.omega_overwrite_rooted`, `Attraction.omega_overwrite_unrooted`); a disjoint pair
  whose union is the other side proposes `τ` in the unrooted coding only (`omega_other_side`);
  and when `τ` is not a split of the tree no single innovation proposes it in either coding
  (`single_none`).
-/
import Mathlib
import StemmaLean.Attraction

open Finset
open scoped Classical

namespace Stemma.Dominance

open Stemma.Mechanisms Stemma.Attraction

variable {n : ℕ}

/-- A cluster proposed in the rooted coding is a class of a reading, so its split is proposed in
the unrooted coding. -/
lemma propR_propU {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool}
    {A : Finset (Fin n)} (h : PropR M att A) : PropU M att A :=
  ⟨h.1, h.2.choose, h.2.choose_spec.2⟩

/-- Outcome by outcome: the rooted coding proposes `C` or `Cᶜ` only when the unrooted coding
proposes `C | Cᶜ`. -/
lemma PR_PU (C : Finset (Fin n)) (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) :
    (PR C M att → PU C M att) ∧ (PR Cᶜ M att → PU C M att) :=
  ⟨fun h => Or.inl (propR_propU h), fun h => Or.inr (propR_propU h)⟩

section rates

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)

include hπ0 hπ1 hα0 hα1 in
/-- **Corollary 8.7 (`cor:dominance`), comparison of the codings at second order.**  In the
attraction model, for every split `τ = C | D` (`D = Cᶜ`), the second-order support `Λ` of each of
the clusters `C` and `D` in the rooted coding is at most the second-order support of `τ` in the
unrooted coding.  (Lean needs no hypothesis on `τ`: the report states it for false splits.) -/
theorem dominance (C : Finset (Fin n)) :
    ex K π α (fun M att => PR C M att ∧ M.card ≤ 2) ≤
        ex K π α (fun M att => PU C M att ∧ M.card ≤ 2) ∧
      ex K π α (fun M att => PR Cᶜ M att ∧ M.card ≤ 2) ≤
        ex K π α (fun M att => PU C M att ∧ M.card ≤ 2) :=
  ⟨ex_mono hπ0 hπ1 hα0 hα1 fun M att h => ⟨(PR_PU C M att).1 h.1, h.2⟩,
    ex_mono hπ0 hπ1 hα0 hα1 fun M att h => ⟨(PR_PU C M att).2 h.1, h.2⟩⟩

include hπ0 hπ1 hα0 hα1 in
/-- The comparison of Corollary 8.7 holds at every order: `m^root_C ≤ m^unr_τ` and
`m^root_D ≤ m^unr_τ` for the exact expected supports. -/
theorem dominance_exact (C : Finset (Fin n)) :
    ex K π α (PR C) ≤ ex K π α (PU C) ∧ ex K π α (PR Cᶜ) ≤ ex K π α (PU C) :=
  ⟨ex_mono hπ0 hπ1 hα0 hα1 fun M att h => (PR_PU C M att).1 h,
    ex_mono hπ0 hπ1 hα0 hα1 fun M att h => (PR_PU C M att).2 h⟩

end rates

/-- **Corollary 8.7, pair by pair.**  For `α ∈ [0,1]`, the weight `ω_{ef}` with which a pair of
innovations proposes the cluster `C` or `D = Cᶜ` in the rooted coding is at most the weight with
which it proposes `τ = C | D` in the unrooted coding. -/
theorem omega_dominance {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (C : Finset (Fin n))
    (S : Finset (Finset (Fin n))) :
    omega (PR C) α S ≤ omega (PU C) α S ∧ omega (PR Cᶜ) α S ≤ omega (PU C) α S := by
  have ha : 0 ≤ α ^ 2 := sq_nonneg α
  have hb : 0 ≤ 1 - α ^ 2 := by nlinarith
  have hind : ∀ {p q : Prop} [Decidable p] [Decidable q], (p → q) →
      (if p then (1 : ℝ) else 0) ≤ if q then 1 else 0 := by
    intro p q _ _ h
    by_cases hp : p
    · simp [hp, h hp]
    · by_cases hq : q <;> simp [hp, hq]
  unfold omega
  constructor
  · exact add_le_add (mul_le_mul_of_nonneg_left (hind ((PR_PU C _ _).1)) ha)
      (mul_le_mul_of_nonneg_left (hind ((PR_PU C _ _).1)) hb)
  · exact add_le_add (mul_le_mul_of_nonneg_left (hind ((PR_PU C _ _).2)) ha)
      (mul_le_mul_of_nonneg_left (hind ((PR_PU C _ _).2)) hb)

/-- **Corollary 8.7, the other side.**  A pair of innovations on disjoint non-empty clades
`C_e`, `C_f` whose union is the side `D` proposes `τ = C | D` in the unrooted coding with weight
`1` (`C` keeps the original reading), and the cluster `C` in the rooted coding with weight `0`. -/
theorem omega_other_side {e f : Finset (Fin n)} (hd : Disjoint e f) (he : e.Nonempty)
    (hf : f.Nonempty) (hrest : (e ∪ f)ᶜ.Nonempty) (α : ℝ) :
    omega (PU (e ∪ f)ᶜ) α {e, f} = 1 ∧ omega (PR (e ∪ f)ᶜ) α {e, f} = 0 := by
  have hU : ∀ att, PU (e ∪ f)ᶜ {e, f} att := fun att =>
    Or.inl ((retention_coincidence att hd he hf).1 hrest)
  have hR : ∀ att, ¬ PR (e ∪ f)ᶜ {e, f} att := by
    intro att h
    obtain ⟨x, hx⟩ := he
    obtain ⟨y, hy⟩ := hf
    obtain ⟨z, hz⟩ := hrest
    rcases (retention_coincidence att hd ⟨x, hx⟩ ⟨y, hy⟩).2.2.2 _ h with h1 | h1 | h1
    · have : x ∈ (e ∪ f)ᶜ := by rw [h1]; exact hx
      exact (mem_compl.mp this) (mem_union_left _ hx)
    · have : y ∈ (e ∪ f)ᶜ := by rw [h1]; exact hy
      exact (mem_compl.mp this) (mem_union_right _ hy)
    · have : z ∈ e ∪ f := by rw [← h1]; exact hz
      exact (mem_compl.mp hz) this
  unfold omega
  rw [if_pos (hU _), if_pos (hU _), if_neg (hR _), if_neg (hR _)]
  constructor <;> ring

/-- **Corollary 8.7, single innovations.**  If `τ = C | Cᶜ` is not the split of the edge `e`
(`C_e ≠ C`, `C_e ≠ Cᶜ`), an innovation on `e` alone proposes neither `τ` in the unrooted coding
nor `C` or `Cᶜ` in the rooted coding. -/
theorem single_none {e C : Finset (Fin n)} (h1 : e ≠ C) (h2 : e ≠ Cᶜ)
    (att : Finset (Fin n) → Bool) :
    ¬ PU C {e} att ∧ ¬ PR C {e} att ∧ ¬ PR Cᶜ {e} att := by
  have hs := fun A => single (n := n) att (e := e) A
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rintro (h | h)
    · rcases (hs C).2.2.1 h with h' | h'
      · exact h1 h'.symm
      · exact h2 (by rw [h', compl_compl])
    · rcases (hs Cᶜ).2.2.1 h with h' | h'
      · exact h2 h'.symm
      · exact h1 (compl_injective h').symm
  · exact h1 ((hs C).2.2.2 h).symm
  · exact h2 ((hs Cᶜ).2.2.2 h).symm

end Stemma.Dominance
