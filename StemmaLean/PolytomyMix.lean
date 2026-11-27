/-
The coincidence null at a polytomy with random rates: the second half of Proposition 8.8 of the
technical report (`prop:polytomynull`).

Given a factor `ρ`, drawn for each unit from a law `ν` on `[0, ρ_max]`, the edges innovate
independently with probabilities `ρ π_e`.  The expected support and the probabilities `q_D` are
then averages over `ν` (`mmix`, `qmix`).  With `κ = E ρ² / (E ρ)²`, `s = ∑ π` and
`ρ_max s ≤ 1`, `null_mixture` bounds

  `|m_τ - κ (α² q_{C_i} q_{C_j} + [k = 3, v not the root] (1 - α²) q_{C_v} q_{C_l})| ≤ 7 E ρ³ s³`,

the report's remainder `O(ε³ E ρ³)` with an explicit constant.
-/
import Mathlib
import StemmaLean.PolytomyNull

open MeasureTheory Finset
open scoped Classical

namespace Stemma.PolytomyMix

open Stemma.Mechanisms Stemma.Attraction Stemma.PolytomyNull

variable {n : ℕ}

/-- The rates scaled by `ρ`. -/
def sc (ρ : ℝ) (π : Finset (Fin n) → ℝ) : Finset (Fin n) → ℝ := fun e => ρ * π e

lemma continuous_ex (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) :
    Continuous fun ρ : ℝ => ex K (sc ρ π) α P := by
  unfold ex wt sc; fun_prop

lemma lead_sc (Cs K : Finset (Finset (Fin n))) (ci cj : Finset (Fin n)) (α ρ : ℝ)
    (π : Finset (Fin n) → ℝ) :
    lead Cs K ci cj α (sc ρ π) = ρ ^ 2 * lead Cs K ci cj α π := by
  unfold lead sc
  rw [mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun c _ => ?_
    split_ifs <;> ring

/-- One product of the mixture: `|κ (Eρ π_a + D_a)(Eρ π_b + D_b) - Eρ² π_a π_b| ≤ (21/4) s³ Eρ³`
when `|D| ≤ (3/2) s² Eρ²`. -/
lemma mix_prod {E1 E2 E3 ρm s pa pb Da Db : ℝ} (hE1 : 0 < E1) (hE2 : 0 ≤ E2)
    (hcs : E2 ^ 2 ≤ E1 * E3) (h21 : E2 ≤ ρm * E1) (hρs : ρm * s ≤ 1) (hs0 : 0 ≤ s)
    (hρm : 0 ≤ ρm) (ha0 : 0 ≤ pa) (hb0 : 0 ≤ pb) (has : pa ≤ s) (hbs : pb ≤ s)
    (hDa : |Da| ≤ 3 / 2 * s ^ 2 * E2) (hDb : |Db| ≤ 3 / 2 * s ^ 2 * E2) :
    |E2 / E1 ^ 2 * ((E1 * pa + Da) * (E1 * pb + Db)) - E2 * (pa * pb)| ≤ 21 / 4 * s ^ 3 * E3 := by
  set u := E2 / E1 with hu
  have hu0 : 0 ≤ u := div_nonneg hE2 hE1.le
  have huE : u * E1 = E2 := by rw [hu]; field_simp
  have hu_le : u ≤ ρm := by rw [hu, div_le_iff₀ hE1]; linarith
  have hu2 : u * E2 ≤ E3 := by
    have : u * E2 * E1 = E2 ^ 2 := by rw [← huE]; ring
    nlinarith
  have e : E2 / E1 ^ 2 * ((E1 * pa + Da) * (E1 * pb + Db)) - E2 * (pa * pb) =
      u * (pa * Db) + u * (pb * Da) + u / E1 * (Da * Db) := by
    rw [hu]; field_simp; ring
  rw [e]
  have hE3 : 0 ≤ E3 := by nlinarith [sq_nonneg E2]
  have h1 : |u * (pa * Db)| ≤ 3 / 2 * s ^ 3 * E3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg ha0]
    calc u * (pa * |Db|) ≤ u * (s * (3 / 2 * s ^ 2 * E2)) := by gcongr
      _ = 3 / 2 * s ^ 3 * (u * E2) := by ring
      _ ≤ 3 / 2 * s ^ 3 * E3 := by gcongr
  have h2 : |u * (pb * Da)| ≤ 3 / 2 * s ^ 3 * E3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hb0]
    calc u * (pb * |Da|) ≤ u * (s * (3 / 2 * s ^ 2 * E2)) := by gcongr
      _ = 3 / 2 * s ^ 3 * (u * E2) := by ring
      _ ≤ 3 / 2 * s ^ 3 * E3 := by gcongr
  have h3 : |u / E1 * (Da * Db)| ≤ 9 / 4 * s ^ 3 * E3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hu0 hE1.le)]
    have hab : |Da| * |Db| ≤ (3 / 2 * s ^ 2 * E2) * (3 / 2 * s ^ 2 * E2) :=
      mul_le_mul hDa hDb (abs_nonneg _) (le_trans (abs_nonneg _) hDa)
    have hkey : u / E1 * E2 ^ 2 ≤ ρm * E3 := by
      have : u / E1 * E2 ^ 2 = u * (u * E2) := by
        rw [← huE]; field_simp
      rw [this]
      exact mul_le_mul hu_le hu2 (by positivity) hρm
    calc u / E1 * (|Da| * |Db|) ≤ u / E1 * ((3 / 2 * s ^ 2 * E2) * (3 / 2 * s ^ 2 * E2)) :=
          mul_le_mul_of_nonneg_left hab (div_nonneg hu0 hE1.le)
      _ = 9 / 4 * s ^ 4 * (u / E1 * E2 ^ 2) := by ring
      _ ≤ 9 / 4 * s ^ 4 * (ρm * E3) := by gcongr
      _ = 9 / 4 * s ^ 3 * E3 * (ρm * s) := by ring
      _ ≤ 9 / 4 * s ^ 3 * E3 * 1 := by gcongr
      _ = 9 / 4 * s ^ 3 * E3 := by ring
  calc |u * (pa * Db) + u * (pb * Da) + u / E1 * (Da * Db)|
      ≤ |u * (pa * Db)| + |u * (pb * Da)| + |u / E1 * (Da * Db)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 / 2 * s ^ 3 * E3 + 3 / 2 * s ^ 3 * E3 + 9 / 4 * s ^ 3 * E3 :=
        add_le_add (add_le_add h1 h2) h3
    _ = 21 / 4 * s ^ 3 * E3 := by ring

section mix

variable {K Cs : Finset (Finset (Fin n))} (hV : Vertex K Cs) (hKne : ∀ e ∈ K, e.Nonempty)
  (hK : Laminar K) {ci cj : Finset (Fin n)} (hi : ci ∈ Cs) (hj : cj ∈ Cs) (hij : ci ≠ cj)
  {π : Finset (Fin n) → ℝ} {α : ℝ} (hπ0 : ∀ e, 0 ≤ π e) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
  {ν : Measure ℝ} [IsProbabilityMeasure ν] {ρm : ℝ}
  (hsupp : ∀ᵐ ρ ∂ν, 0 ≤ ρ ∧ ρ ≤ ρm) (hρs : ρm * ∑ g ∈ K, π g ≤ 1) (hE1 : 0 < ∫ ρ, ρ ∂ν)
include hV hKne hK hi hj hij hπ0 hα0 hα1 hsupp hρs hE1

/-- **Proposition 8.8, random rates.**  With `κ = E ρ² / (E ρ)²`, the expected support of `τ`
under the mixture is `κ` times the leading term in the mixed `q`, up to `7 E ρ³ s³`. -/
theorem null_mixture :
    |∫ ρ, ex K (sc ρ π) α (PR (ci ∪ cj)) ∂ν -
      (∫ ρ, ρ ^ 2 ∂ν) / (∫ ρ, ρ ∂ν) ^ 2 *
        lead Cs K ci cj α (fun D => ∫ ρ, q K (sc ρ π) α D ∂ν)| ≤
      7 * (∫ ρ, ρ ^ 3 ∂ν) * (∑ g ∈ K, π g) ^ 3 := by
  set s := ∑ g ∈ K, π g
  set E1 := ∫ ρ, ρ ∂ν
  set E2 := ∫ ρ, ρ ^ 2 ∂ν
  set E3 := ∫ ρ, ρ ^ 3 ∂ν
  have hs0 : 0 ≤ s := sum_nonneg fun g _ => hπ0 g
  have hle : ∀ {D}, D ∈ K → π D ≤ s := fun hD => single_le_sum (fun g _ => hπ0 g) hD
  have hπs : ∀ e, π e ≤ s ∨ e ∉ K := fun e => by
    by_cases h : e ∈ K
    · exact Or.inl (hle h)
    · exact Or.inr h
  have hρm : 0 ≤ ρm := by
    obtain ⟨ρ, hρ⟩ := hsupp.exists
    linarith [hρ.1, hρ.2]
  -- rates in `[0,1]` on the support (edges outside `K` play no role; we need all `e`)
  -- we use the rates `sc ρ π` only through `ex K`, which reads them on `K`
  set πK : Finset (Fin n) → ℝ := fun e => if e ∈ K then π e else 0
  have hexK : ∀ (f : Finset (Fin n) → ℝ) (g : Finset (Fin n) → ℝ), (∀ e ∈ K, f e = g e) →
      ∀ P, ex K f α P = ex K g α P := by
    intro f g hfg P
    unfold ex wt
    refine sum_congr rfl fun M hM => sum_congr rfl fun A hA => ?_
    have hMK := mem_powerset.mp hM
    have hAK := (mem_powerset.mp hA).trans hMK
    congr 2
    · congr 1
      · exact prod_congr rfl fun e he => by rw [hfg e (hAK he)]
      · exact prod_congr rfl fun e he => by rw [hfg e (hMK (mem_sdiff.mp he).1)]
    · exact prod_congr rfl fun e he => by rw [hfg e (mem_sdiff.mp he).1]
  have hsK : ∑ g ∈ K, πK g = s := sum_congr rfl fun g hg => by simp [πK, hg]
  have hK0 : ∀ e, 0 ≤ πK e := fun e => by unfold πK; split_ifs <;> simp [hπ0 e]
  have hKs : ∀ e, πK e ≤ s := fun e => by
    unfold πK; split_ifs with h
    · exact hle h
    · exact hs0
  have hsc0 : ∀ ρ, 0 ≤ ρ → ∀ e, 0 ≤ sc ρ πK e := fun ρ hρ e => mul_nonneg hρ (hK0 e)
  have hsc1 : ∀ ρ, 0 ≤ ρ → ρ ≤ ρm → ∀ e, sc ρ πK e ≤ 1 := fun ρ hρ0 hρ1 e => by
    unfold sc
    calc ρ * πK e ≤ ρm * s := mul_le_mul hρ1 (hKs e) (hK0 e) hρm
      _ ≤ 1 := hρs
  have hscK : ∀ ρ P, ex K (sc ρ π) α P = ex K (sc ρ πK) α P := fun ρ P =>
    hexK _ _ (fun e he => by simp [sc, πK, he]) P
  have hqK : ∀ ρ D, q K (sc ρ π) α D = q K (sc ρ πK) α D := fun ρ D => hscK ρ _
  have hleadK : lead Cs K ci cj α π = lead Cs K ci cj α πK := by
    unfold lead
    have hci : ci ∈ K := hV.sub hi
    have hcj : cj ∈ K := hV.sub hj
    simp only [πK, hci, hcj, if_true]
    congr 1
    refine sum_congr rfl fun c hc => ?_
    have hcK : c ∈ K := hV.sub (mem_filter.mp hc).1
    split_ifs with h1 h2 <;> simp_all
  -- integrability
  have hbdd : ∀ (f : ℝ → ℝ), Continuous f → (∀ ρ, 0 ≤ ρ → ρ ≤ ρm → |f ρ| ≤ 1) →
      Integrable f ν := by
    intro f hf hb
    refine Integrable.of_bound (C := 1) hf.aestronglyMeasurable ?_
    filter_upwards [hsupp] with ρ hρ
    rw [Real.norm_eq_abs]; exact hb ρ hρ.1 hρ.2
  have hpow : ∀ k : ℕ, Integrable (fun ρ : ℝ => ρ ^ k) ν := by
    intro k
    refine Integrable.of_bound (C := ρm ^ k)
      (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun ρ : ℝ => ρ ^ k)) ?_
    filter_upwards [hsupp] with ρ hρ
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ.1 k)]
    exact pow_le_pow_left₀ hρ.1 hρ.2 k
  have hint1 : Integrable (fun ρ : ℝ => ρ) ν := by simpa using hpow 1
  have hexint : ∀ P, Integrable (fun ρ => ex K (sc ρ π) α P) ν := by
    intro P
    refine hbdd _ (continuous_ex K π α P) fun ρ h0 h1 => ?_
    rw [hscK, abs_of_nonneg (ex_nonneg (hsc0 ρ h0) (hsc1 ρ h0 h1) hα0 hα1 P)]
    exact ex_le_one (hsc0 ρ h0) (hsc1 ρ h0 h1) hα0 hα1 P
  -- moments
  have hE2 : 0 ≤ E2 := integral_nonneg fun ρ => sq_nonneg ρ
  have h21 : E2 ≤ ρm * E1 := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hpow 2) (hint1.const_mul ρm) ?_
    filter_upwards [hsupp] with ρ hρ
    show ρ ^ 2 ≤ ρm * ρ
    nlinarith [hρ.1, hρ.2]
  have hcs : E2 ^ 2 ≤ E1 * E3 := by
    -- `0 ≤ E[ρ (t - ρ)²]` with `t = E2 / E1`
    set t := E2 / E1
    have hnn : 0 ≤ ∫ ρ, (t ^ 2 * ρ - 2 * t * ρ ^ 2 + ρ ^ 3) ∂ν := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hsupp] with ρ hρ
      show 0 ≤ t ^ 2 * ρ - 2 * t * ρ ^ 2 + ρ ^ 3
      have : t ^ 2 * ρ - 2 * t * ρ ^ 2 + ρ ^ 3 = ρ * (t - ρ) ^ 2 := by ring
      rw [this]; exact mul_nonneg hρ.1 (sq_nonneg _)
    have i1 : ∫ ρ, (t ^ 2 * ρ - 2 * t * ρ ^ 2 + ρ ^ 3) ∂ν =
        ∫ ρ, (t ^ 2 * ρ - 2 * t * ρ ^ 2) ∂ν + ∫ ρ, ρ ^ 3 ∂ν :=
      integral_add ((hint1.const_mul _).sub ((hpow 2).const_mul _)) (hpow 3)
    have i2 : ∫ ρ, (t ^ 2 * ρ - 2 * t * ρ ^ 2) ∂ν = ∫ ρ, t ^ 2 * ρ ∂ν - ∫ ρ, 2 * t * ρ ^ 2 ∂ν :=
      integral_sub (hint1.const_mul _) ((hpow 2).const_mul _)
    rw [i1, i2, integral_const_mul, integral_const_mul] at hnn
    have htE : t * E1 = E2 := by simp only [t]; field_simp
    have : t ^ 2 * E1 - 2 * t * E2 + E3 = E3 - E2 ^ 2 / E1 := by
      rw [← htE]; field_simp; ring
    rw [this, sub_nonneg, div_le_iff₀ hE1] at hnn
    linarith
  -- the support, pointwise
  have hm_pt : ∀ᵐ ρ ∂ν, |ex K (sc ρ π) α (PR (ci ∪ cj)) - ρ ^ 2 * lead Cs K ci cj α π| ≤
      7 / 6 * s ^ 3 * ρ ^ 3 := by
    filter_upwards [hsupp] with ρ hρ
    have := m_bound hV hKne hK hi hj hij (hsc0 ρ hρ.1) (hsc1 ρ hρ.1 hρ.2) hα0 hα1
    rw [← hscK, lead_sc, ← hleadK] at this
    have hsum : ∑ g ∈ K, sc ρ πK g = ρ * s := by simp only [sc]; rw [← mul_sum, hsK]
    rw [hsum] at this
    calc _ ≤ 7 / 6 * (ρ * s) ^ 3 := this
      _ = 7 / 6 * s ^ 3 * ρ ^ 3 := by ring
  have hq_pt : ∀ D ∈ K, ∀ᵐ ρ ∂ν, |q K (sc ρ π) α D - ρ * π D| ≤ 3 / 2 * s ^ 2 * ρ ^ 2 := by
    intro D hD
    filter_upwards [hsupp] with ρ hρ
    have := q_bound (hsc0 ρ hρ.1) (hsc1 ρ hρ.1 hρ.2) hα0 hα1 hD (hKne D hD)
    rw [← hqK] at this
    have hsum : ∑ g ∈ K, sc ρ πK g = ρ * s := by simp only [sc]; rw [← mul_sum, hsK]
    rw [hsum] at this
    have hπD : sc ρ πK D = ρ * π D := by simp [sc, πK, hD]
    rw [hπD] at this
    calc _ ≤ 3 / 2 * (ρ * s) ^ 2 := this
      _ = 3 / 2 * s ^ 2 * ρ ^ 2 := by ring
  -- integrated
  have hm_int : |∫ ρ, ex K (sc ρ π) α (PR (ci ∪ cj)) ∂ν - E2 * lead Cs K ci cj α π| ≤
      7 / 6 * s ^ 3 * E3 := by
    have e : ∫ ρ, ex K (sc ρ π) α (PR (ci ∪ cj)) ∂ν - E2 * lead Cs K ci cj α π =
        ∫ ρ, (ex K (sc ρ π) α (PR (ci ∪ cj)) - ρ ^ 2 * lead Cs K ci cj α π) ∂ν := by
      rw [integral_sub (hexint _) ((hpow 2).mul_const _), integral_mul_const]
    rw [e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hpow 3).const_mul _)
      (by filter_upwards [hm_pt] with ρ h; rwa [Real.norm_eq_abs])
  have hqint : ∀ D ∈ K, (∫ ρ, q K (sc ρ π) α D ∂ν) = E1 * π D +
      ∫ ρ, (q K (sc ρ π) α D - ρ * π D) ∂ν := by
    intro D _
    have hqi : Integrable (fun ρ => q K (sc ρ π) α D) ν := hexint _
    rw [integral_sub hqi (hint1.mul_const _), integral_mul_const]; ring
  have hD_int : ∀ D ∈ K, |∫ ρ, (q K (sc ρ π) α D - ρ * π D) ∂ν| ≤ 3 / 2 * s ^ 2 * E2 := by
    intro D hD
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hpow 2).const_mul _)
      (by filter_upwards [hq_pt D hD] with ρ h; rwa [Real.norm_eq_abs])
  -- the products
  have hprod : ∀ a b, a ∈ K → b ∈ K →
      |E2 / E1 ^ 2 * ((∫ ρ, q K (sc ρ π) α a ∂ν) * (∫ ρ, q K (sc ρ π) α b ∂ν)) -
        E2 * (π a * π b)| ≤ 21 / 4 * s ^ 3 * E3 := by
    intro a b ha hb
    rw [hqint a ha, hqint b hb]
    exact mix_prod hE1 hE2 hcs h21 hρs hs0 hρm (hπ0 a) (hπ0 b) (hle ha) (hle hb)
      (hD_int a ha) (hD_int b hb)
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hlead : |E2 / E1 ^ 2 * lead Cs K ci cj α (fun D => ∫ ρ, q K (sc ρ π) α D ∂ν) -
      E2 * lead Cs K ci cj α π| ≤ 21 / 4 * s ^ 3 * E3 := by
    have p1 := hprod ci cj (hV.sub hi) (hV.sub hj)
    unfold lead
    by_cases hc : Cs.card = 3 ∧ Cs.sup id ∈ K
    · obtain ⟨cl, hcl⟩ := third_unique (π := fun _ => (0 : ℝ)) hV hKne hK hi hj hij (fun _ => le_rfl)
        (fun _ => zero_le_one) hα0 hα1 hc.1
      rw [hcl, sum_singleton, sum_singleton, if_pos hc, if_pos hc]
      have hclC : cl ∈ Cs := (mem_filter.mp (hcl ▸ mem_singleton_self cl)).1
      have p2 := hprod (Cs.sup id) cl hc.2 (hV.sub hclC)
      set X := E2 / E1 ^ 2 * ((∫ ρ, q K (sc ρ π) α ci ∂ν) * (∫ ρ, q K (sc ρ π) α cj ∂ν)) -
        E2 * (π ci * π cj)
      set Y := E2 / E1 ^ 2 * ((∫ ρ, q K (sc ρ π) α (Cs.sup id) ∂ν) *
        (∫ ρ, q K (sc ρ π) α cl ∂ν)) - E2 * (π (Cs.sup id) * π cl)
      have e : E2 / E1 ^ 2 * (α ^ 2 * ((∫ ρ, q K (sc ρ π) α ci ∂ν) *
            (∫ ρ, q K (sc ρ π) α cj ∂ν)) + (1 - α ^ 2) *
            ((∫ ρ, q K (sc ρ π) α (Cs.sup id) ∂ν) * (∫ ρ, q K (sc ρ π) α cl ∂ν))) -
          E2 * (α ^ 2 * (π ci * π cj) + (1 - α ^ 2) * (π (Cs.sup id) * π cl)) =
          α ^ 2 * X + (1 - α ^ 2) * Y := by simp only [X, Y]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (by linarith : 0 ≤ 1 - α ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left p1 ha0,
        mul_le_mul_of_nonneg_left p2 (by linarith : 0 ≤ 1 - α ^ 2), abs_nonneg X, abs_nonneg Y]
    · simp only [if_neg hc, sum_const_zero, add_zero]
      have e : E2 / E1 ^ 2 * (α ^ 2 * ((∫ ρ, q K (sc ρ π) α ci ∂ν) *
            (∫ ρ, q K (sc ρ π) α cj ∂ν))) - E2 * (α ^ 2 * (π ci * π cj)) =
          α ^ 2 * (E2 / E1 ^ 2 * ((∫ ρ, q K (sc ρ π) α ci ∂ν) * (∫ ρ, q K (sc ρ π) α cj ∂ν)) -
            E2 * (π ci * π cj)) := by ring
      rw [e, abs_mul, abs_of_nonneg ha0]
      have hE3 : 0 ≤ E3 := by nlinarith [sq_nonneg E2]
      nlinarith [mul_le_mul_of_nonneg_left p1 ha0, mul_nonneg (pow_nonneg hs0 3) hE3]
  have hE3 : 0 ≤ E3 := by nlinarith [sq_nonneg E2]
  calc _ ≤ |∫ ρ, ex K (sc ρ π) α (PR (ci ∪ cj)) ∂ν - E2 * lead Cs K ci cj α π| +
        |E2 * lead Cs K ci cj α π -
          E2 / E1 ^ 2 * lead Cs K ci cj α (fun D => ∫ ρ, q K (sc ρ π) α D ∂ν)| :=
        abs_sub_le _ _ _
    _ ≤ 7 / 6 * s ^ 3 * E3 + 21 / 4 * s ^ 3 * E3 := by
        rw [abs_sub_comm (E2 * _)]; exact add_le_add hm_int hlead
    _ ≤ 7 * E3 * s ^ 3 := by nlinarith [mul_nonneg (pow_nonneg hs0 3) hE3]

end mix

end Stemma.PolytomyMix
