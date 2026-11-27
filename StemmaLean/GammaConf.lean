/-
Confidence bound for the margin (Theorem 7.9 of the technical report, `thm:gammaconf`).

For each non-trivial split `s` the report takes one-sided Clopper–Pearson bounds `ℓ_s`, `u_s` at
level `δ/(2N)`, `N` the number of non-trivial splits.  Lean takes the bounds as arbitrary random
quantities with that coverage, `P(m_s < ℓ_s) ≤ δ/(2N)` and `P(u_s < m_s) ≤ δ/(2N)`: the coverage of
the Clopper–Pearson construction itself (binomial tails against beta quantiles) is not formalised.
Lean proves the rest: simultaneously for every binary stemma, `γ(T) ≥ γ_lo(T)` with probability at
least `1 - δ`, and a false certificate has probability at most `δ`.
-/
import Mathlib
import StemmaLean.Margin

open MeasureTheory Finset
open scoped Classical

namespace Stemma.GammaConf

open Splits Margin

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The non-trivial splits (by their sides away from `r`). -/
noncomputable def sides (r : Fin n) : Finset (Finset (Fin n)) := univ.filter (IsSide r)

/-- The lower margin `γ_lo(T)`: the margin with `ℓ` on the splits of `T` and `u` on the others. -/
noncomputable def loMargin (r : Fin n) (ℓ u : Finset (Fin n) → ℝ) (T : Finset (Finset (Fin n)))
    (hTne : T.Nonempty) : ℝ :=
  (competitors r T).inf' (competitors_nonempty hTne)
    fun S => (∑ σ ∈ T \ S, ℓ σ - ∑ σ ∈ S \ T, u σ) / (T \ S).card

/-- On the event that every bound holds, `γ_lo(T) ≤ γ(T)` for every binary `T`. -/
lemma loMargin_le {r : Fin n} {m ℓ u : Finset (Fin n) → ℝ}
    (hE : ∀ s ∈ sides r, ℓ s ≤ m s ∧ m s ≤ u s) {T : Finset (Finset (Fin n))}
    (hT : IsBinary r T) (hTne : T.Nonempty) : loMargin r ℓ u T hTne ≤ margin r m T hTne := by
  unfold margin
  rw [le_inf'_iff]
  intro S hS
  have hS' := hS
  simp only [competitors, mem_filter, mem_univ, true_and] at hS'
  have hpos : (0 : ℝ) < (T \ S).card :=
    by exact_mod_cast card_pos.mpr (displacement_matching hT hS'.1 hS'.2).1
  refine (inf'_le _ hS).trans ?_
  unfold ratio
  apply div_le_div_of_nonneg_right _ hpos.le
  have h1 : ∑ σ ∈ T \ S, ℓ σ ≤ ∑ σ ∈ T \ S, m σ := sum_le_sum fun σ hσ =>
    (hE σ (by simp [sides, hT.1.1 σ (mem_sdiff.mp hσ).1])).1
  have h2 : ∑ σ ∈ S \ T, m σ ≤ ∑ σ ∈ S \ T, u σ := sum_le_sum fun σ hσ =>
    (hE σ (by simp [sides, hS'.1.1 σ (mem_sdiff.mp hσ).1])).2
  linarith

/-- A positive margin makes `T` the unique maximum of `m` over compatible sets. -/
lemma unique_max_of_margin_pos {r : Fin n} {m : Finset (Fin n) → ℝ}
    {T : Finset (Finset (Fin n))} (hT : IsBinary r T) (hTne : T.Nonempty)
    (hpos : 0 < margin r m T hTne) : ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T := by
  intro S hS hne
  have hgap := margin_gap hT hTne m S hS hne
  have hA : (1 : ℝ) ≤ (T \ S).card :=
    by exact_mod_cast card_pos.mpr (displacement_matching hT hS hne).1
  have := (Finset.sum_sdiff_sub_sum_sdiff (s₁ := S) (s₂ := T) (f := m))
  unfold wt
  nlinarith

/-- **Theorem 7.9 (`thm:gammaconf`), confidence bound for the margin.**  Let `ℓ s`, `u s` be random
lower and upper bounds for `m s`, each failing with probability at most `δ / (2N)`, `N` the number
of non-trivial splits (`2^(n-1) - n - 1`, Prop. 8.1).  Then (i) with probability at least `1 - δ`,
`γ(T) ≥ γ_lo(T)` for every binary stemma `T` simultaneously, in particular for one chosen from the
data; and (ii) the probability that some binary `T` has `γ_lo(T) > 0` without being the unique
maximum of `m` over compatible sets (a false certificate, whatever stemma is certified) is at most
`δ`.  The coverage of the bounds is the hypothesis `hlo`, `hup`; for the Clopper–Pearson bounds
it is proved in `ClopperPearson.lean` (`gamma_confidence_cp`). -/
theorem gamma_confidence (r : Fin n) (m : Finset (Fin n) → ℝ) (ℓ u : Finset (Fin n) → Ω → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : ∀ s ∈ sides r, μ.real {ω | m s < ℓ s ω} ≤ δ / (2 * (sides r).card))
    (hup : ∀ s ∈ sides r, μ.real {ω | u s ω < m s} ≤ δ / (2 * (sides r).card)) :
    μ.real {ω | ¬ ∀ T (hT : IsBinary r T) (hTne : T.Nonempty),
        loMargin r (fun s => ℓ s ω) (fun s => u s ω) T hTne ≤ margin r m T hTne} ≤ δ ∧
    μ.real {ω | ∃ T, ∃ (_ : IsBinary r T) (hTne : T.Nonempty),
        0 < loMargin r (fun s => ℓ s ω) (fun s => u s ω) T hTne ∧
        ¬ ∀ S, IsSystem r S → S ≠ T → wt m S < wt m T} ≤ δ := by
  set Bad : Set Ω := ⋃ s ∈ sides r, ({ω | m s < ℓ s ω} ∪ {ω | u s ω < m s})
  have hBad : μ.real Bad ≤ δ := by
    calc μ.real Bad ≤ ∑ s ∈ sides r, μ.real ({ω | m s < ℓ s ω} ∪ {ω | u s ω < m s}) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _s ∈ sides r, δ / (2 * (sides r).card) * 2 := by
          refine sum_le_sum fun s hs => (measureReal_union_le _ _).trans ?_
          linarith [hlo s hs, hup s hs]
      _ ≤ δ := by
          rw [sum_const, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos (sides r).card with h | h
          · simp [h, hδ]
          · have : (0 : ℝ) < (sides r).card := by exact_mod_cast h
            field_simp; rfl
  have hgood : ∀ ω ∉ Bad, ∀ s ∈ sides r, ℓ s ω ≤ m s ∧ m s ≤ u s ω := by
    intro ω hω s hs
    simp only [Bad, Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or,
      not_lt] at hω
    exact hω s hs
  constructor
  · refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans hBad
    by_contra hb
    exact hω fun T hT hTne => loMargin_le (hgood ω hb) hT hTne
  · refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans hBad
    by_contra hb
    obtain ⟨T, hT, hTne, hpos, hnot⟩ := hω
    exact hnot (unique_max_of_margin_pos hT hTne
      (lt_of_lt_of_le hpos (loMargin_le (hgood ω hb) hT hTne)))

end Stemma.GammaConf
