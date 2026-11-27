/-
Theorem 4.7 (a) and (b) of the mathematical paper, at the level of expected supports.

The estimator is consistent exactly when the true family set is the unique maximum of expected
support (Theorem 2.7 of the paper; its counting core and Hoeffding bound are in `Consistency.lean`).
Here we prove which family set has the maximum, for every sufficiently small `ε > 0`.
-/
import StemmaLean.CodingGen

open Filter Topology

namespace Stemma.Coding

open Stemma.Quartet

/-- If `G` is continuous with `G 0 > 0`, then `ε² G(ε) > 0` for all sufficiently small `ε > 0`. -/
lemma eventually_pos {G : ℝ → ℝ} (hG : Continuous G) (h0 : 0 < G 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ^ 2 * G ε := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < G ε := (hG.tendsto 0).eventually (lt_mem_nhds h0)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds h1, h2] with ε hG' hε
  positivity

/-- Unrooted supports after the substitution `r = ρ ε²`, `p₁ = a ε`, `p₃ = b ε`. -/
def sU (P : ℕ → ℕ → ℕ → ℕ → Bool) (ρ a b α ε : ℝ) : ℝ :=
  suppA (ρ * ε ^ 2) (a * ε) (b * ε) α P

/-- **Theorem 4.7 (a), consistent side.** If `a b < 2ρ` (with `ρ > 0`), then for all sufficiently
small `ε > 0` the true split `12|34` has strictly larger expected support than `13|24` and
`14|23` in the unrooted coding, whatever `α`. -/
theorem unrooted_consistent (ρ a b α : ℝ) (hρ : 0 < ρ) (h : a * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sU Stemma.Quartet.U13 ρ a b α ε < sU U12 ρ a b α ε ∧ sU U14 ρ a b α ε < sU U12 ρ a b α ε := by
  have e1 := eventually_pos (G := fun ε => gU12 ρ a b α ε - gU13 ρ a b α ε)
    ((cont_U12 ρ a b α).sub (cont_U13 ρ a b α)) (by simp [zero_U12, zero_U13]; linarith)
  have e2 := eventually_pos (G := fun ε => gU12 ρ a b α ε - gU14 ρ a b α ε)
    ((cont_U12 ρ a b α).sub (cont_U14 ρ a b α)) (by simp [zero_U12, zero_U14]; linarith)
  filter_upwards [e1, e2] with ε h1 h2
  simp only [sU, scale_U12, scale_U13, scale_U14] at *
  constructor <;> nlinarith

/-- **Theorem 4.7 (a), inconsistent side.** If `a b > 2ρ` (with `a, b > 0`), then for all
sufficiently small `ε > 0` the false split `13|24` has strictly the largest expected support. -/
theorem unrooted_inconsistent (ρ a b α : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 2 * ρ < a * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sU U12 ρ a b α ε < sU Stemma.Quartet.U13 ρ a b α ε ∧
        sU U14 ρ a b α ε < sU Stemma.Quartet.U13 ρ a b α ε := by
  have hab : 0 < a * b := mul_pos ha hb
  have e1 := eventually_pos (G := fun ε => gU13 ρ a b α ε - gU12 ρ a b α ε)
    ((cont_U13 ρ a b α).sub (cont_U12 ρ a b α)) (by simp [zero_U12, zero_U13]; linarith)
  have e2 := eventually_pos (G := fun ε => gU13 ρ a b α ε - gU14 ρ a b α ε)
    ((cont_U13 ρ a b α).sub (cont_U14 ρ a b α)) (by simp [zero_U13, zero_U14]; linarith)
  filter_upwards [e1, e2] with ε h1 h2
  simp only [sU, scale_U12, scale_U13, scale_U14] at *
  constructor <;> nlinarith

/-! ### Rooted coding: the ten proper clusters of four witnesses -/

/-- The ten proper clusters, in the order 12, 13, 14, 23, 24, 34, 123, 124, 134, 234. -/
def cl : Fin 10 → Finset (Fin 4)
  | 0 => {0, 1} | 1 => {0, 2} | 2 => {0, 3} | 3 => {1, 2} | 4 => {1, 3}
  | 5 => {2, 3} | 6 => {0, 1, 2} | 7 => {0, 1, 3} | 8 => {0, 2, 3} | 9 => {1, 2, 3}

/-- Two clusters are compatible when disjoint or nested. -/
def lam (i j : Fin 10) : Prop := Disjoint (cl i) (cl j) ∨ cl i ⊆ cl j ∨ cl j ⊆ cl i

instance (i j : Fin 10) : Decidable (lam i j) := by unfold lam; infer_instance

/-- A laminar family of clusters. -/
def Laminar (F : Finset (Fin 10)) : Prop := ∀ i ∈ F, ∀ j ∈ F, lam i j

/-- The true family: clusters `{1,2}` and `{3,4}`. -/
def T : Finset (Fin 10) := {0, 5}

/-- Rescaled expected support of each cluster. -/
def g (ρ a b α ε : ℝ) : Fin 10 → ℝ
  | 0 => gR12 ρ a b α ε | 1 => gR13 ρ a b α ε | 2 => gR14 ρ a b α ε | 3 => gR23 ρ a b α ε
  | 4 => gR24 ρ a b α ε | 5 => gR34 ρ a b α ε | 6 => gR123 ρ a b α ε | 7 => gR124 ρ a b α ε
  | 8 => gR134 ρ a b α ε | 9 => gR234 ρ a b α ε

/-- Expected support of each cluster after the substitution. -/
def m (ρ a b α ε : ℝ) : Fin 10 → ℝ
  | 0 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C12
  | 1 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C13
  | 2 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C14
  | 3 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C23
  | 4 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C24
  | 5 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C34
  | 6 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C123
  | 7 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C124
  | 8 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C134
  | 9 => suppA (ρ * ε ^ 2) (a * ε) (b * ε) α C234

lemma m_eq (ρ a b α ε : ℝ) (c : Fin 10) : m ρ a b α ε c = ε ^ 2 * g ρ a b α ε c := by
  fin_cases c <;> simp [m, g, scale_R12, scale_R13, scale_R14, scale_R23, scale_R24, scale_R34,
    scale_R123, scale_R124, scale_R134, scale_R234]

lemma g_cont (ρ a b α : ℝ) (c : Fin 10) : Continuous (fun ε => g ρ a b α ε c) := by
  fin_cases c <;> simp only [g] <;> [exact cont_R12 ..; exact cont_R13 ..; exact cont_R14 ..;
    exact cont_R23 ..; exact cont_R24 ..; exact cont_R34 ..; exact cont_R123 ..;
    exact cont_R124 ..; exact cont_R134 ..; exact cont_R234 ..]

/-- Values at `ε = 0`: only `{1,2}`, `{3,4}` (weight `ρ`) and `{1,3}` (weight `α² a b`) survive. -/
def g0 (ρ a b α : ℝ) : Fin 10 → ℝ
  | 0 => ρ | 1 => a * α ^ 2 * b | 5 => ρ | _ => 0

lemma g_zero (ρ a b α : ℝ) (c : Fin 10) : g ρ a b α 0 c = g0 ρ a b α c := by
  fin_cases c <;> simp [g, g0, zero_R12, zero_R13, zero_R14, zero_R23, zero_R24, zero_R34,
    zero_R123, zero_R124, zero_R134, zero_R234]

/-- Weight of a family of clusters. -/
def weight (ρ a b α ε : ℝ) (F : Finset (Fin 10)) : ℝ := ∑ c ∈ F, m ρ a b α ε c

/-! Structural facts, checked by evaluation. -/

lemma conflict_13 : ¬ lam 1 0 ∧ ¬ lam 1 5 := by decide

/-- Every cluster other than `{1,2}` and `{3,4}` conflicts with one of them. -/
lemma T_maximal : ∀ c : Fin 10, c ≠ 0 → c ≠ 5 → ¬ lam c 0 ∨ ¬ lam c 5 := by decide

lemma laminar_eq_T {F : Finset (Fin 10)} (hF : Laminar F) (h0 : (0 : Fin 10) ∈ F)
    (h5 : (5 : Fin 10) ∈ F) : F = T := by
  ext c
  simp only [T, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hc
    by_contra hne
    push Not at hne
    rcases T_maximal c hne.1 hne.2 with h | h
    · exact h (hF c hc 0 h0)
    · exact h (hF c hc 5 h5)
  · rintro (rfl | rfl) <;> assumption

/-- Sum of the values at `0` over a family, by membership of the three surviving clusters. -/
lemma sum_g0 (ρ a b α : ℝ) (F : Finset (Fin 10)) :
    ∑ c ∈ F, g0 ρ a b α c =
      (if (0 : Fin 10) ∈ F then ρ else 0) + (if (1 : Fin 10) ∈ F then a * α ^ 2 * b else 0) +
        (if (5 : Fin 10) ∈ F then ρ else 0) := by
  have h : ∀ c, g0 ρ a b α c = (if c = 0 then ρ else 0) + (if c = 1 then a * α ^ 2 * b else 0) +
      (if c = 5 then ρ else 0) := by
    intro c; fin_cases c <;> simp [g0]
  rw [Finset.sum_congr rfl (fun c _ => h c), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- **Theorem 4.7 (b), consistent side.** If `α² a b < 2ρ` (with `ρ > 0`), then for all
sufficiently small `ε > 0` the true family `{{1,2},{3,4}}` is strictly heavier than every other
laminar family of clusters in the rooted coding. -/
theorem rooted_consistent (ρ a b α : ℝ) (hρ : 0 < ρ) (h : a * α ^ 2 * b < 2 * ρ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : Finset (Fin 10), Laminar F → F ≠ T →
      weight ρ a b α ε F < weight ρ a b α ε T := by
  rw [eventually_all]
  intro F
  by_cases hF : Laminar F ∧ F ≠ T
  · obtain ⟨hlam, hne⟩ := hF
    let G : ℝ → ℝ := fun ε => (∑ c ∈ T, g ρ a b α ε c) - ∑ c ∈ F, g ρ a b α ε c
    have hG : Continuous G :=
      (continuous_finsetSum _ fun c _ => g_cont ρ a b α c).sub
        (continuous_finsetSum _ fun c _ => g_cont ρ a b α c)
    have h0 : 0 < G 0 := by
      simp only [G, g_zero, sum_g0]
      have hT0 : (0 : Fin 10) ∈ T := by decide
      have hT1 : (1 : Fin 10) ∉ T := by decide
      have hT5 : (5 : Fin 10) ∈ T := by decide
      simp only [hT0, hT1, hT5, ite_true, ite_false]
      by_cases h1 : (1 : Fin 10) ∈ F
      · have n0 : (0 : Fin 10) ∉ F := fun h0 => conflict_13.1 (hlam 1 h1 0 h0)
        have n5 : (5 : Fin 10) ∉ F := fun h5 => conflict_13.2 (hlam 1 h1 5 h5)
        simp only [h1, n0, n5, ite_true, ite_false]; linarith
      · by_cases h0F : (0 : Fin 10) ∈ F
        · by_cases h5F : (5 : Fin 10) ∈ F
          · exact absurd (laminar_eq_T hlam h0F h5F) hne
          · simp only [h1, h0F, h5F, ite_true, ite_false]; linarith
        · by_cases h5F : (5 : Fin 10) ∈ F <;> simp only [h1, h0F, h5F, ite_true, ite_false] <;>
            linarith
    filter_upwards [eventually_pos hG h0] with ε hε _ _
    have : weight ρ a b α ε T - weight ρ a b α ε F = ε ^ 2 * G ε := by
      simp only [weight, G, m_eq, ← Finset.mul_sum]; ring
    linarith
  · exact Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hF

/-- **Theorem 4.7 (b), inconsistent side.** If `α² a b > 2ρ`, then for all sufficiently small
`ε > 0` the single cluster `{1,3}` is heavier than the true family, so the true family is not the
maximum. -/
theorem rooted_inconsistent (ρ a b α : ℝ) (h : 2 * ρ < a * α ^ 2 * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), weight ρ a b α ε T < weight ρ a b α ε {1} := by
  let G : ℝ → ℝ := fun ε => g ρ a b α ε 1 - (g ρ a b α ε 0 + g ρ a b α ε 5)
  have hG : Continuous G := (g_cont ρ a b α 1).sub ((g_cont ρ a b α 0).add (g_cont ρ a b α 5))
  have h0 : 0 < G 0 := by simp only [G, g_zero, g0]; linarith
  filter_upwards [eventually_pos hG h0] with ε hε
  have : weight ρ a b α ε {1} - weight ρ a b α ε T = ε ^ 2 * G ε := by
    simp [weight, T, G, m_eq]; ring
  linarith

/-- **Theorem 4.7 (b), inconsistent side, every optimum contains `{1,3}`.** If `α² a b > 2ρ` (with
`ρ ≥ 0`), then for all sufficiently small `ε > 0` every laminar family that omits `{1,3}` is
strictly lighter than the single cluster `{1,3}`; hence every maximum-weight laminar family
contains `{1,3}`.  At `ε = 0` the rescaled weight of a family omitting `{1,3}` is `ρ` times the
number of true clusters it contains, at most `2ρ`, against `α² a b` for `{{1,3}}`. -/
theorem rooted_optimum_contains_13 (ρ a b α : ℝ) (hρ : 0 ≤ ρ) (h : 2 * ρ < a * α ^ 2 * b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ F : Finset (Fin 10), Laminar F → (1 : Fin 10) ∉ F →
        weight ρ a b α ε F < weight ρ a b α ε {1}) ∧
      (∀ F : Finset (Fin 10), Laminar F →
        (∀ F' : Finset (Fin 10), Laminar F' → weight ρ a b α ε F' ≤ weight ρ a b α ε F) →
        (1 : Fin 10) ∈ F) := by
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : Finset (Fin 10), Laminar F → (1 : Fin 10) ∉ F →
      weight ρ a b α ε F < weight ρ a b α ε {1} := by
    rw [eventually_all]
    intro F
    by_cases hF : (1 : Fin 10) ∉ F
    · let G : ℝ → ℝ := fun ε => g ρ a b α ε 1 - ∑ c ∈ F, g ρ a b α ε c
      have hG : Continuous G :=
        (g_cont ρ a b α 1).sub (continuous_finsetSum _ fun c _ => g_cont ρ a b α c)
      have h0 : 0 < G 0 := by
        simp only [G, g_zero, sum_g0, hF, ite_false]
        simp only [g0]
        by_cases h0F : (0 : Fin 10) ∈ F <;> by_cases h5F : (5 : Fin 10) ∈ F <;>
          simp only [h0F, h5F, ite_true, ite_false] <;> linarith
      filter_upwards [eventually_pos hG h0] with ε hε _ _
      have : weight ρ a b α ε {1} - weight ρ a b α ε F = ε ^ 2 * G ε := by
        simp only [weight, G, m_eq, ← Finset.mul_sum, Finset.sum_singleton]; ring
      linarith
    · exact Eventually.of_forall fun ε _ h2 => absurd h2 hF
  filter_upwards [hall] with ε hε
  refine ⟨hε, fun F hF hmax => ?_⟩
  by_contra h1
  have hlt := hε F hF h1
  have hle := hmax {1} (by intro i hi j hj; rw [Finset.mem_singleton.mp hi,
    Finset.mem_singleton.mp hj]; decide)
  linarith

end Stemma.Coding
