/-
Consistency for clusters: Theorem 7.4(a) (`thm:consistency`) and Lemma 7.3 (`lem:gamma`) of the
technical report in the rooted coding (Proposition 6.10, `prop:rooted`).

The consistency bound `Consistency.consistency_of_matching` takes the matching property as a
hypothesis, for any family system; for a binary rooted stemma (`Rooted.IsBinR T`, its `n - 2`
proper clusters) and the laminar sets of proper clusters (`Rooted.IsHier`) it is
`Rooted.displacement_matching_rooted`.

Formalised:
* `consistency_rooted`: the Hoeffding consistency bound for clusters,
  `Pr(some other laminar set of proper clusters is at least as heavy as T) ≤ 2 |R| exp(-L γ² / 2)`;
* `computing_gamma_rooted`: Lemma 7.3 for clusters: `T` is a maximum of the shifted supports
  `m^{(g)}` over laminar sets of proper clusters iff `g ≤ γ`, with the rooted margin
  `marginR` (minimum of the ratio over the rooted competitors); `marginR_gap`: the rooted margin
  satisfies the margin inequality of `consistency_rooted`.
-/
import Mathlib
import StemmaLean.Rooted
import StemmaLean.Consistency
import StemmaLean.Margin

open MeasureTheory ProbabilityTheory Real Finset
open scoped Classical

namespace Stemma.RootedConsistency

open Splits Rooted Margin

variable {n : ℕ}

section consistency

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Theorem 7.4(a) for clusters (`thm:consistency`, `prop:rooted`), Hoeffding form.**  Let `T`
be the proper clusters of a binary rooted stemma on `n` witnesses.  Units are `L` independent
draws; `Y σ u ∈ [0,1]` indicates that unit `u` proposes cluster `σ`, with expectation `m σ`;
clusters outside `R` are never proposed and have `m σ = 0`.  If `γ > 0` satisfies the margin
inequality (`γ |T \ S| ≤ m(T \ S) - m(S \ T)` for every laminar set `S ≠ T` of proper clusters),
the probability that some other laminar set of proper clusters is at least as heavy as `T` is at
most `2 |R| exp(-L γ² / 2)`.  The matching property is Lemma 6.1 for clusters, proved. -/
theorem consistency_rooted (T : Finset (Finset (Fin n))) (hT : IsBinR T)
    (m : Finset (Fin n) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ S, IsHier S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = m σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0) (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, IsHier S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      2 * R.card * exp (-L * γ ^ 2 / 2) :=
  Consistency.consistency_of_matching IsHier T m γ hγ
    (fun S hS hne => by
      obtain ⟨h1, h2, -⟩ := displacement_matching_rooted hT hS hne
      exact ⟨h1, h2⟩)
    hgap hL Y hmeas hb hind hmean R hR hmR

end consistency

/-! ### Lemma 7.3 for clusters, computing γ -/

/-- The rooted competitors of `T`: the laminar sets of proper clusters other than `T`. -/
noncomputable def competitorsR (T : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  univ.filter fun S => IsHier S ∧ S ≠ T

lemma competitorsR_nonempty {T : Finset (Finset (Fin n))} (hTne : T.Nonempty) :
    (competitorsR T).Nonempty :=
  ⟨∅, by
    simp only [competitorsR, mem_filter, mem_univ, true_and]
    exact ⟨⟨by simp, by simp⟩, (nonempty_iff_ne_empty.mp hTne).symm⟩⟩

/-- **Definition 7.2 for clusters, the rooted margin**: the minimum of the ratio over the rooted
competitors (for `T` with at least one cluster, so that `∅` is a competitor). -/
noncomputable def marginR (m : Finset (Fin n) → ℝ) (T : Finset (Finset (Fin n)))
    (hTne : T.Nonempty) : ℝ :=
  (competitorsR T).inf' (competitorsR_nonempty hTne) (ratio m T)

/-- **Lemma 7.3 for clusters (`lem:gamma`, `prop:rooted`), computing γ.**  For a binary rooted
stemma `T` and any real `g`, `T` is a maximum of the shifted supports `m^{(g)}` over laminar sets
of proper clusters if and only if `g ≤ γ` (the rooted margin), so bisection is valid. -/
theorem computing_gamma_rooted {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) (g : ℝ) :
    (∀ S, IsHier S → wt (shift T m g) S ≤ wt (shift T m g) T) ↔ g ≤ marginR m T hTne := by
  have hpos : ∀ S ∈ competitorsR T, (0 : ℝ) < (T \ S).card := fun S hS => by
    simp only [competitorsR, mem_filter, mem_univ, true_and] at hS
    exact_mod_cast card_pos.mpr (displacement_matching_rooted hT hS.1 hS.2).1
  unfold marginR
  rw [le_inf'_iff]
  constructor
  · intro h S hS
    have := h S (by simp [competitorsR] at hS; exact hS.1)
    have hd := shift_diff T S m g
    rw [ratio, le_div_iff₀ (hpos S hS)]
    linarith
  · intro h S hS
    by_cases e : S = T
    · rw [e]
    have hc : S ∈ competitorsR T := by simp [competitorsR, hS, e]
    have := h S hc
    rw [ratio, le_div_iff₀ (hpos S hc)] at this
    have hd := shift_diff T S m g
    linarith

/-- The rooted margin satisfies the margin inequality of `consistency_rooted`. -/
lemma marginR_gap {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    (hTne : T.Nonempty) (m : Finset (Fin n) → ℝ) :
    ∀ S, IsHier S → S ≠ T →
      marginR m T hTne * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ := by
  intro S hS hne
  have hc : S ∈ competitorsR T := by simp [competitorsR, hS, hne]
  have hpos : (0 : ℝ) < (T \ S).card :=
    by exact_mod_cast card_pos.mpr (displacement_matching_rooted hT hS hne).1
  have := inf'_le (ratio m T) hc
  rw [ratio, le_div_iff₀ hpos] at this
  exact this

end Stemma.RootedConsistency
