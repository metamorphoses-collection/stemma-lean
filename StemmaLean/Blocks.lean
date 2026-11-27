/-
Dependent blocks (Proposition 7.8 of the technical report, `prop:blocks`).

The units form `J` independent blocks of `k` units each, with arbitrary dependence inside a block.
The support of a split is the sum over all units; the Hoeffding argument of Theorem 7.4(a)
(`Consistency.consistency`) applies to the `J` block averages.
-/
import Mathlib
import StemmaLean.Consistency

open MeasureTheory ProbabilityTheory Real

namespace Stemma.Blocks

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Proposition 7.8 (`prop:blocks`), dependent blocks.**  Let `T` be (the split system of) a
binary stemma.  The units are indexed by a block `j : Fin J` and a position `i : Fin k` in the
block; `Y σ j i ∈ [0,1]` indicates that unit `(j, i)` proposes `σ`.  The blocks are independent
(`iIndepFun` of the block vectors `(Y σ j i)ᵢ` across `j`), with arbitrary dependence inside a
block, and `m σ` is the expected support of `σ` per unit, `E[w_j(σ)] = k m σ` for every block `j`
with `w_j(σ) = ∑ᵢ Y σ j i`.  Splits outside `R` are never proposed.  If `γ > 0` satisfies the margin
inequality for this `m`, the probability that some other compatible set is at least as heavy as
`T` (total support over all `J k` units) is at most `2 |R| exp(-J γ² / 2)`.
Lean needs equal block means and independence across blocks, not identical distribution. -/
theorem dependent_blocks {n : ℕ} (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : Splits.IsBinary r T) (m : Finset (Fin n) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ S, Splits.IsSystem r S → S ≠ T →
      γ * (T \ S).card ≤ ∑ σ ∈ T \ S, m σ - ∑ σ ∈ S \ T, m σ)
    {J k : ℕ} (hJ : 0 < J) (hk : 0 < k) (Y : Finset (Fin n) → Fin J → Fin k → Ω → ℝ)
    (hmeas : ∀ σ j i, Measurable (Y σ j i)) (hb : ∀ σ j i ω, Y σ j i ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (fun j ω => fun i => Y σ j i ω) μ)
    (hmean : ∀ σ j, μ[fun ω => ∑ i, Y σ j i ω] = k * m σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ j i ω, Y σ j i ω = 0)
    (hmR : ∀ σ ∉ R, m σ = 0) :
    μ.real {ω | ∃ S, Splits.IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, ∑ j, ∑ i, Y σ j i ω ≤ ∑ σ ∈ S, ∑ j, ∑ i, Y σ j i ω} ≤
      2 * R.card * exp (-J * γ ^ 2 / 2) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  -- block averages
  set Z : Finset (Fin n) → Fin J → Ω → ℝ := fun σ j ω => (∑ i, Y σ j i ω) / k with hZ
  have hZmeas : ∀ σ j, Measurable (Z σ j) := fun σ j =>
    (Finset.measurable_sum _ fun i _ => hmeas σ j i).div_const _
  have hZb : ∀ σ j ω, Z σ j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro σ j ω
    have h0 : 0 ≤ ∑ i, Y σ j i ω := Finset.sum_nonneg fun i _ => (hb σ j i ω).1
    have h1 : ∑ i, Y σ j i ω ≤ k := by
      calc ∑ i, Y σ j i ω ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb σ j i ω).2
        _ = k := by simp
    exact ⟨div_nonneg h0 hkpos.le, (div_le_one hkpos).mpr h1⟩
  have hZind : ∀ σ, iIndepFun (Z σ) μ := by
    intro σ
    have hf : ∀ _j : Fin J, Measurable (fun v : Fin k → ℝ => (∑ i, v i) / k) := fun _ =>
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _
    exact (hind σ).comp (fun _ v => (∑ i, v i) / k) hf
  have hZmean : ∀ σ j, μ[Z σ j] = m σ := by
    intro σ j
    simp only [hZ]
    rw [integral_div, hmean σ j]
    field_simp
  have hZR : ∀ σ ∉ R, ∀ j ω, Z σ j ω = 0 := by
    intro σ hσ j ω; simp [hZ, hR σ hσ]
  have H := Consistency.consistency r T hT m γ hγ hgap hJ Z hZmeas hZb hZind hZmean R hZR hmR
  refine le_trans (le_of_eq ?_) H
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  have e : ∀ S : Finset (Finset (Fin n)),
      ∑ σ ∈ S, (∑ j, Z σ j ω) / J = (∑ σ ∈ S, ∑ j, ∑ i, Y σ j i ω) / (k * J) := by
    intro S
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hZ, ← Finset.sum_div]
    rw [div_div]
  refine exists_congr fun S => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [e, e, div_le_div_iff_of_pos_right (mul_pos hkpos hJpos)]

end Stemma.Blocks
