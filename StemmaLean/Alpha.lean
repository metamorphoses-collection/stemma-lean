/-
Estimating the coincidence probability: Proposition 8.7 of the technical report (`prop:alpha`).

In the attraction model of `Attraction.lean`, `R_ij` is the probability that a unit proposes the
split `{i,j} | rest` in the unrooted coding and `C_ij` the probability that it proposes the
cluster `{i,j}` in the rooted coding.  The pair is isolated (`Isolated`) when `{i,j}` is not a
clade, no clade minus a sub-clade is `{i,j}` or its complement, no union of two disjoint clades
other than `{i} ∪ {j}` is either, and `X \ {i,j}` is not a clade.

Formalised:
* `two_part`: for an isolated pair, only the two pendant innovations on `i` and `j` propose
  `{i,j}` among outcomes with at most two innovations, so the two-innovation parts are
  `R⁽²⁾ = π_i π_j ∏_{g ≠ i,j} (1 - π_g)` and `C⁽²⁾ = α² R⁽²⁾`;
* `alpha_pair`: `|C_ij - α² R_ij| ≤ Pr(|M| ≥ 3)`;
* `alpha_pooled`: over a set `Ps` of isolated pairs with `∑ R > 0`,
  `|∑ C / ∑ R - α²| ≤ |Ps| Pr(|M| ≥ 3) / ∑ R`;
* `ratio_tendsto`: the ratio of the observed counts converges almost surely to `∑ C / ∑ R` (the
  strong law for numerator and denominator);
* `ratio_drop_empty`: the ratio is unchanged if units that propose nothing are removed.
The `O(ε)` order of the bias follows from `Attraction.P3_le` (`Pr(|M| ≥ 3) ≤ (∑ π)³ / 6`) and
`R_ij ≥ R⁽²⁾`; it is not restated.
-/
import Mathlib
import StemmaLean.Attraction

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped Classical

namespace Stemma.Alpha

open Stemma.Mechanisms Stemma.Attraction

variable {n : ℕ}

/-- The pair `{i, j}` is isolated in the stemma with clades `K`. -/
def Isolated (K : Finset (Finset (Fin n))) (i j : Fin n) : Prop :=
  ({i, j} : Finset (Fin n)) ∉ K ∧ ({i, j} : Finset (Fin n))ᶜ ∉ K ∧
  (∀ e ∈ K, ∀ f ∈ K, f ⊂ e → e \ f ≠ {i, j} ∧ e \ f ≠ ({i, j} : Finset (Fin n))ᶜ) ∧
  (∀ e ∈ K, ∀ f ∈ K, Disjoint e f → ({e, f} : Finset (Finset (Fin n))) ≠ {{i}, {j}} →
    e ∪ f ≠ {i, j} ∧ e ∪ f ≠ ({i, j} : Finset (Fin n))ᶜ)

section iso

variable {K : Finset (Finset (Fin n))} {i j : Fin n} (hK : Laminar K)
  (hKne : ∀ e ∈ K, e.Nonempty) (hiso : Isolated K i j) (hij : i ≠ j)
  (hrest : ({i, j} : Finset (Fin n))ᶜ.Nonempty)
include hK hKne hiso hij hrest

/-- Outcomes with at most two innovations, other than the two pendant ones, propose `{i,j}` in
neither coding. -/
lemma no_other {M : Finset (Finset (Fin n))} (hM : M ⊆ K) (h2 : M.card ≤ 2)
    (hne : M ≠ {{i}, {j}}) (att : Finset (Fin n) → Bool) :
    ¬ PU {i, j} M att ∧ ¬ PR {i, j} M att := by
  obtain ⟨h1, h2', h3, h4⟩ := hiso
  set τ : Finset (Fin n) := {i, j} with hτdef
  have hτne : τ.Nonempty := ⟨i, by simp [τ]⟩
  have hτu : τ ≠ univ := fun h => by
    obtain ⟨x, hx⟩ := hrest; simp [τ, h] at hx
  have hcc : ∀ {A : Finset (Fin n)}, τ = Aᶜ → τᶜ = A := fun h => by rw [h, compl_compl]
  rcases Nat.lt_or_ge M.card 1 with h0 | h0
  · -- no innovation
    rw [card_eq_zero.mp (by omega : M.card = 0)]
    refine ⟨?_, (single att (e := ∅) τ).2.1⟩
    rintro (h | h)
    · exact hτu ((single att (e := ∅) τ).1 h)
    · have := (single att (e := ∅) τᶜ).1 h
      exact hτne.ne_empty (by rw [← compl_compl τ, this, compl_univ])
  rcases Nat.lt_or_ge M.card 2 with h1' | h1'
  · -- one innovation
    obtain ⟨e, rfl⟩ := card_eq_one.mp (by omega : M.card = 1)
    have he : e ∈ K := hM (mem_singleton_self e)
    obtain ⟨-, -, hU, hR⟩ := single att (e := e) τ
    obtain ⟨-, -, hU', -⟩ := single att (e := e) τᶜ
    refine ⟨?_, fun h => h1 ((hR h) ▸ he)⟩
    rintro (h | h)
    · rcases hU h with h | h
      · exact h1 (h ▸ he)
      · exact h2' ((hcc h) ▸ he)
    · rcases hU' h with h | h
      · exact h2' (h ▸ he)
      · exact h1 (compl_injective h ▸ he)
  · -- two innovations
    obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp (by omega : M.card = 2)
    have he : e ∈ K := hM (by simp)
    have hf : f ∈ K := hM (by simp)
    have notK : ∀ {A}, A ∈ K → A ≠ τ ∧ A ≠ τᶜ := fun hA =>
      ⟨fun h => h1 (h ▸ hA), fun h => h2' (h ▸ hA)⟩
    rcases hK e he f hf hef with hd | hfe | hef'
    · obtain ⟨-, -, hU, hR⟩ := retention_coincidence att hd (hKne e he) (hKne f hf)
      obtain ⟨a1, a2⟩ := h4 e he f hf hd hne
      refine ⟨?_, fun h => ?_⟩
      · rintro (h | h)
        · rcases hU τ h with h | h | h | h
          · exact (notK he).1 h.symm
          · exact (notK hf).1 h.symm
          · exact a1 h.symm
          · exact a2 (hcc h).symm
        · rcases hU τᶜ h with h | h | h | h
          · exact (notK he).2 h.symm
          · exact (notK hf).2 h.symm
          · exact a2 h.symm
          · exact a1 (compl_injective h).symm
      · rcases hR τ h with h | h | h
        · exact (notK he).1 h.symm
        · exact (notK hf).1 h.symm
        · exact a1 h.symm
    · obtain ⟨-, -, hU, hR⟩ := overwrite att hfe (hKne f hf)
      obtain ⟨a1, a2⟩ := h3 e he f hf hfe
      refine ⟨?_, fun h => ?_⟩
      · rintro (h | h)
        · rcases hU τ h with h | h | h | h
          · exact (notK hf).1 h.symm
          · exact (notK he).1 h.symm
          · exact (notK he).2 (hcc h).symm
          · exact a1 h.symm
        · rcases hU τᶜ h with h | h | h | h
          · exact (notK hf).2 h.symm
          · exact (notK he).2 h.symm
          · exact (notK he).1 (compl_injective h).symm
          · exact a2 h.symm
      · rcases hR τ h with h | h | h
        · exact (notK hf).1 h.symm
        · exact (notK he).1 h.symm
        · exact a1 h.symm
    · rw [show ({e, f} : Finset (Finset (Fin n))) = {f, e} from pair_comm e f]
      obtain ⟨-, -, hU, hR⟩ := overwrite att hef' (hKne e he)
      obtain ⟨a1, a2⟩ := h3 f hf e he hef'
      refine ⟨?_, fun h => ?_⟩
      · rintro (h | h)
        · rcases hU τ h with h | h | h | h
          · exact (notK he).1 h.symm
          · exact (notK hf).1 h.symm
          · exact (notK hf).2 (hcc h).symm
          · exact a1 h.symm
        · rcases hU τᶜ h with h | h | h | h
          · exact (notK he).2 h.symm
          · exact (notK hf).2 h.symm
          · exact (notK hf).1 (compl_injective h).symm
          · exact a2 h.symm
      · rcases hR τ h with h | h | h
        · exact (notK he).1 h.symm
        · exact (notK hf).1 h.symm
        · exact a1 h.symm

end iso

lemma ex_congr {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
    {P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (h : ∀ M ⊆ K, ∀ A ⊆ M, (P M (attOf A) ↔ Q M (attOf A))) : ex K π α P = ex K π α Q := by
  unfold ex
  refine sum_congr rfl fun M hM => sum_congr rfl fun A hA => ?_
  rw [if_congr (h M (mem_powerset.mp hM) A (mem_powerset.mp hA)) rfl rfl]

/-- The expected value of `P` restricted to one innovation set `S ⊆ K`. -/
lemma ex_eq_single {K : Finset (Finset (Fin n))} (π : Finset (Fin n) → ℝ) (α : ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) {S : Finset (Finset (Fin n))}
    (hS : S ⊆ K) :
    ex K π α (fun M att => P M att ∧ M = S) =
      ∑ A ∈ S.powerset, wt K π α S A * (if P S (attOf A) then 1 else 0) := by
  unfold ex
  rw [sum_eq_single S]
  · exact sum_congr rfl fun A _ => by simp
  · intro M _ hMS; exact sum_eq_zero fun A _ => by simp [hMS]
  · intro h; exact absurd (mem_powerset.mpr hS) h

section iso

variable {K : Finset (Finset (Fin n))} {i j : Fin n} (hK : Laminar K)
  (hKne : ∀ e ∈ K, e.Nonempty) (hiso : Isolated K i j) (hij : i ≠ j)
  (hrest : ({i, j} : Finset (Fin n))ᶜ.Nonempty) (hi : {i} ∈ K) (hj : {j} ∈ K)
  (π : Finset (Fin n) → ℝ) (α : ℝ)
include hK hKne hiso hij hrest hi hj

/-- **Proposition 8.7, the two-innovation parts.**  `R⁽²⁾ = π_i π_j ∏_{g ≠ i,j} (1 - π_g)` and
`C⁽²⁾ = α² R⁽²⁾`. -/
theorem two_part :
    ex K π α (fun M att => PU {i, j} M att ∧ M.card ≤ 2) =
        π {i} * π {j} * ∏ g ∈ K \ {{i}, {j}}, (1 - π g) ∧
    ex K π α (fun M att => PR {i, j} M att ∧ M.card ≤ 2) =
        α ^ 2 * (π {i} * π {j} * ∏ g ∈ K \ {{i}, {j}}, (1 - π g)) := by
  set S0 : Finset (Finset (Fin n)) := {{i}, {j}}
  have hS0 : S0 ⊆ K := insert_subset hi (singleton_subset_iff.mpr hj)
  have hne : ({i} : Finset (Fin n)) ≠ {j} := fun h => hij (singleton_injective h)
  have hcard : S0.card = 2 := card_pair hne
  have hd : Disjoint ({i} : Finset (Fin n)) {j} := disjoint_singleton.mpr hij
  have hunion : ({i} : Finset (Fin n)) ∪ {j} = {i, j} := by rw [insert_eq]
  have red : ∀ P : Finset (Fin n) → Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop,
      (∀ M att, P {i, j} M att → PU {i, j} M att ∨ PR {i, j} M att) →
      ex K π α (fun M att => P {i, j} M att ∧ M.card ≤ 2) =
        ex K π α (fun M att => P {i, j} M att ∧ M = S0) := by
    intro P hP
    refine ex_congr fun M hM A _ => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, h2 ▸ hcard.le⟩⟩
    by_contra hMS
    have := no_other hK hKne hiso hij hrest hM h2 hMS (attOf A)
    rcases hP _ _ h1 with h | h
    · exact this.1 h
    · exact this.2 h
  have hprod : ∏ e ∈ S0, π e = π {i} * π {j} := prod_pair hne
  constructor
  · rw [red (fun τ => PU τ) fun M att h => Or.inl h, ex_eq_single π α _ hS0]
    have hall : ∀ A ∈ S0.powerset, PU {i, j} S0 (attOf A) := fun A _ => by
      refine Or.inr ?_
      have := (retention_coincidence (attOf A) hd ⟨i, by simp⟩ ⟨j, by simp⟩).1
      rw [hunion] at this
      exact this hrest
    rw [sum_congr rfl fun A hA => by rw [if_pos (hall A hA), mul_one], sum_wt_A, hprod]
  · rw [red (fun τ => PR τ) fun M att h => Or.inr h, ex_eq_single π α _ hS0]
    have hiff : ∀ A ∈ S0.powerset, PR {i, j} S0 (attOf A) ↔ A = S0 := by
      intro A hA
      have := (retention_coincidence (attOf A) hd ⟨i, by simp⟩ ⟨j, by simp⟩).2.1
      rw [hunion] at this
      unfold PR
      rw [this]
      simp only [attOf, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine subset_antisymm (mem_powerset.mp hA) ?_
        intro x hx; simp only [S0, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rintro rfl; simp [S0]
    rw [sum_congr rfl fun A hA => by rw [if_congr (hiff A hA) rfl rfl]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq']
    rw [if_pos (mem_powerset_self S0)]
    unfold wt
    rw [sdiff_self, bot_eq_empty, prod_empty, mul_one, prod_mul_distrib, prod_const, hcard,
      hprod]
    ring

/-- **Proposition 8.7 (`prop:alpha`), one pair.**  `|C_ij - α² R_ij| ≤ Pr(|M| ≥ 3)`. -/
theorem alpha_pair (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |ex K π α (PR {i, j}) - α ^ 2 * ex K π α (PU {i, j})| ≤ P3 K π α := by
  obtain ⟨eU, hU0, hU1⟩ := ex_split hπ0 hπ1 hα0 hα1 (K := K) (PU {i, j})
  obtain ⟨eR, hR0, hR1⟩ := ex_split hπ0 hπ1 hα0 hα1 (K := K) (PR {i, j})
  obtain ⟨tU, tR⟩ := two_part hK hKne hiso hij hrest hi hj π α
  rw [eU, eR, tU, tR]
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ α ^ 2 := sq_nonneg α
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg ha0 hU0]

end iso

/-- **Proposition 8.7, pooled.**  Over a set `Ps` of isolated pairs with `∑ R > 0`,
`|∑ C / ∑ R - α²| ≤ |Ps| Pr(|M| ≥ 3) / ∑ R`. -/
theorem alpha_pooled {K : Finset (Finset (Fin n))} (hK : Laminar K)
    (hKne : ∀ e ∈ K, e.Nonempty) {π : Finset (Fin n) → ℝ} {α : ℝ}
    (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (Ps : Finset (Fin n × Fin n))
    (hP : ∀ p ∈ Ps, Isolated K p.1 p.2 ∧ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset (Fin n))ᶜ.Nonempty ∧
      {p.1} ∈ K ∧ {p.2} ∈ K)
    (hpos : 0 < ∑ p ∈ Ps, ex K π α (PU {p.1, p.2})) :
    |(∑ p ∈ Ps, ex K π α (PR {p.1, p.2})) / (∑ p ∈ Ps, ex K π α (PU {p.1, p.2})) - α ^ 2| ≤
      Ps.card * P3 K π α / ∑ p ∈ Ps, ex K π α (PU {p.1, p.2}) := by
  set Rs := ∑ p ∈ Ps, ex K π α (PU {p.1, p.2})
  have h : (∑ p ∈ Ps, ex K π α (PR {p.1, p.2})) / Rs - α ^ 2 =
      (∑ p ∈ Ps, (ex K π α (PR {p.1, p.2}) - α ^ 2 * ex K π α (PU {p.1, p.2}))) / Rs := by
    rw [sum_sub_distrib, ← mul_sum]; field_simp; ring
  rw [h, abs_div, abs_of_pos hpos]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ Ps, |ex K π α (PR {p.1, p.2}) - α ^ 2 * ex K π α (PU {p.1, p.2})|
      ≤ ∑ _p ∈ Ps, P3 K π α := sum_le_sum fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hP p hp
        exact alpha_pair hK hKne h1 h2 h3 h4 h5 π α hπ0 hπ1 hα0 hα1
    _ = Ps.card * P3 K π α := by rw [sum_const, nsmul_eq_mul]

/-! ### The observed ratio -/

section ratio

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Proposition 8.7, the observed ratio.**  If the units' counts `Ĉ u` (clusters `{i,j}`
proposed over the pairs) and `R̂ u` (splits) are pairwise independent and identically distributed,
integrable, with means `c` and `r > 0`, the ratio of the observed counts converges almost surely
to `c / r`. -/
theorem ratio_tendsto (C R : ℕ → Ω → ℝ) (hC : ∀ u, Measurable (C u)) (hR : ∀ u, Measurable (R u))
    (hCi : Integrable (C 0) μ) (hRi : Integrable (R 0) μ)
    (hCind : Pairwise fun u v => IndepFun (C u) (C v) μ)
    (hRind : Pairwise fun u v => IndepFun (R u) (R v) μ)
    (hCid : ∀ u, IdentDistrib (C u) (C 0) μ μ) (hRid : ∀ u, IdentDistrib (R u) (R 0) μ μ)
    {c r : ℝ} (hc : μ[C 0] = c) (hr : μ[R 0] = r) (hrpos : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun L : ℕ => (∑ u ∈ range L, C u ω) / ∑ u ∈ range L, R u ω) atTop
      (𝓝 (c / r)) := by
  have HC := strong_law_ae (μ := μ) C hCi hCind hCid
  have HR := strong_law_ae (μ := μ) R hRi hRind hRid
  filter_upwards [HC, HR] with ω h1 h2
  rw [hc] at h1; rw [hr] at h2
  have := h1.div h2 hrpos.ne'
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [Pi.div_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ (inv_ne_zero hL')]

end ratio

/-- **Proposition 8.7, units that propose nothing.**  Removing the units that contribute to
neither count leaves the ratio unchanged. -/
theorem ratio_drop_empty {U V : Finset ℕ} (hVU : V ⊆ U) (C R : ℕ → ℝ)
    (hV : ∀ u ∈ U, u ∉ V → C u = 0 ∧ R u = 0) :
    (∑ u ∈ V, C u) / (∑ u ∈ V, R u) = (∑ u ∈ U, C u) / (∑ u ∈ U, R u) := by
  rw [sum_subset hVU fun u hu hv => (hV u hu hv).1, sum_subset hVU fun u hu hv => (hV u hu hv).2]

end Stemma.Alpha
