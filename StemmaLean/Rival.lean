/-
The rival test (Proposition 8.3 of the technical report, `prop:rival`): for two splits `σ` and
`τ` in conflict and i.i.d. units, conditionally on `w(σ) + w(τ) = N`, `w(σ)` is binomial with
parameters `N` and `m_σ / (m_σ + m_τ)`.

Model.  By exclusivity (Lemma 3.5, `Stemma.exclusivity`), no unit proposes two splits in conflict,
so each unit has one of three outcomes: it proposes `σ` (outcome `0`), `τ` (outcome `1`), or
neither (outcome `2`), with probabilities `p 0 = m_σ`, `p 1 = m_τ`, `p 2`.  A collation of `L`
independent units is a sequence `x : Fin L → Fin 3`, of probability `∏ u, p (x u)`; the probability
of an event is the sum over the sequences in it.  The conditional statement is given in product
form, `P(w σ = k ∧ w σ + w τ = N) = Bin(N, a)(k) · P(w σ + w τ = N)`, which needs no division by a
possibly zero probability.  The tail `P(w σ ≥ k | N)`, the `p`-value of the test, is `rival_tail`
(`rival_tail_null` under `m_σ = m_τ`).
-/
import Mathlib

namespace Stemma.Rival

open Finset

/-- Close `∀ x, P x ↔ Q x` where `P`, `Q` are conjunctions of linear constraints on counts. -/
macro "cnt_iff" : tactic =>
  `(tactic| (intro x; constructor <;> intro h <;> (try obtain ⟨h1, h2⟩ := h) <;>
    (first | omega | exact ⟨by omega, by omega⟩)))

/-- The number of units with outcome `i`. -/
def cnt {L : ℕ} (i : Fin 3) (x : Fin L → Fin 3) : ℕ := (univ.filter (fun u => x u = i)).card

/-- The probability of an event under `L` i.i.d. units with outcome probabilities `p`. -/
noncomputable def prob (p : Fin 3 → ℝ) (L : ℕ) (E : (Fin L → Fin 3) → Prop) [DecidablePred E] :
    ℝ := ∑ x, if E x then ∏ u, p (x u) else 0

/-- `P(w σ = k ∧ w τ = j)`. -/
noncomputable def G (p : Fin 3 → ℝ) (L k j : ℕ) : ℝ := prob p L (fun x => cnt 0 x = k ∧ cnt 1 x = j)

/-- `P(w σ + w τ = N)`. -/
noncomputable def Hm (p : Fin 3 → ℝ) (L N : ℕ) : ℝ := prob p L (fun x => cnt 0 x + cnt 1 x = N)

lemma cnt_cons {L : ℕ} (i a : Fin 3) (x : Fin L → Fin 3) :
    cnt i (Fin.cons a x : Fin (L + 1) → Fin 3) = (if a = i then 1 else 0) + cnt i x := by
  unfold cnt
  rw [Fin.card_filter_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  split_ifs <;> omega

/-- Decomposing a sequence of `L + 1` units into its first unit and the rest. -/
lemma prob_succ (p : Fin 3 → ℝ) (L : ℕ) (E : (Fin (L + 1) → Fin 3) → Prop) [DecidablePred E] :
    prob p (L + 1) E =
      ∑ a : Fin 3, p a * ∑ x : Fin L → Fin 3,
        if E (Fin.cons a x) then ∏ u, p (x u) else 0 := by
  unfold prob
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3) (fun ax =>
      if E (Fin.cons ax.1 ax.2) then ∏ u, p ((Fin.cons ax.1 ax.2 : Fin (L + 1) → Fin 3) u) else 0)
    _ (fun _ => rfl), Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Fin.prod_univ_succ]; simp
  · simp

lemma G_succ (p : Fin 3 → ℝ) (L k j : ℕ) :
    G p (L + 1) k j =
      p 0 * prob p L (fun x => cnt 0 x + 1 = k ∧ cnt 1 x = j) +
      p 1 * prob p L (fun x => cnt 0 x = k ∧ cnt 1 x + 1 = j) + p 2 * G p L k j := by
  unfold G
  rw [prob_succ, Fin.sum_univ_three]
  simp only [cnt_cons]
  unfold prob
  simp [add_comm]

lemma Hm_succ (p : Fin 3 → ℝ) (L N : ℕ) :
    Hm p (L + 1) N =
      (p 0 + p 1) * prob p L (fun x => cnt 0 x + cnt 1 x + 1 = N) + p 2 * Hm p L N := by
  unfold Hm
  rw [prob_succ, Fin.sum_univ_three]
  simp only [cnt_cons]
  unfold prob
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, add_zero, zero_add]
  have e : ∀ x : Fin L → Fin 3, cnt 0 x + (1 + cnt 1 x) = cnt 0 x + cnt 1 x + 1 := fun x => by
    ring
  have e' : ∀ x : Fin L → Fin 3, 1 + cnt 0 x + cnt 1 x = cnt 0 x + cnt 1 x + 1 := fun x => by
    ring
  simp only [e, e']
  ring

lemma prob_false (p : Fin 3 → ℝ) (L : ℕ) : prob p L (fun _ => False) = 0 := by
  simp [prob]

lemma prob_congr (p : Fin 3 → ℝ) (L : ℕ) {E F : (Fin L → Fin 3) → Prop} [DecidablePred E]
    [DecidablePred F] (h : ∀ x, E x ↔ F x) : prob p L E = prob p L F := by
  unfold prob; exact sum_congr rfl fun x _ => by simp only [h x]

lemma G_00 (p : Fin 3 → ℝ) (L : ℕ) : G p (L + 1) 0 0 = p 2 * G p L 0 0 := by
  rw [G_succ, prob_congr p L (E := fun x => cnt 0 x + 1 = 0 ∧ cnt 1 x = 0) (F := fun _ => False)
    (by cnt_iff), prob_congr p L (E := fun x => cnt 0 x = 0 ∧ cnt 1 x + 1 = 0)
    (F := fun _ => False) (by cnt_iff), prob_false]; ring

lemma G_0s (p : Fin 3 → ℝ) (L j : ℕ) :
    G p (L + 1) 0 (j + 1) = p 1 * G p L 0 j + p 2 * G p L 0 (j + 1) := by
  rw [G_succ, prob_congr p L (E := fun x => cnt 0 x + 1 = 0 ∧ cnt 1 x = j + 1)
    (F := fun _ => False) (by cnt_iff), prob_congr p L
    (E := fun x => cnt 0 x = 0 ∧ cnt 1 x + 1 = j + 1) (F := fun x => cnt 0 x = 0 ∧ cnt 1 x = j)
    (by cnt_iff), prob_false]; unfold G; ring

lemma G_s0 (p : Fin 3 → ℝ) (L k : ℕ) :
    G p (L + 1) (k + 1) 0 = p 0 * G p L k 0 + p 2 * G p L (k + 1) 0 := by
  rw [G_succ, prob_congr p L (E := fun x => cnt 0 x + 1 = k + 1 ∧ cnt 1 x = 0)
    (F := fun x => cnt 0 x = k ∧ cnt 1 x = 0) (by cnt_iff), prob_congr p L
    (E := fun x => cnt 0 x = k + 1 ∧ cnt 1 x + 1 = 0) (F := fun _ => False)
    (by cnt_iff), prob_false]; unfold G; ring

lemma G_ss (p : Fin 3 → ℝ) (L k j : ℕ) :
    G p (L + 1) (k + 1) (j + 1) =
      p 0 * G p L k (j + 1) + p 1 * G p L (k + 1) j + p 2 * G p L (k + 1) (j + 1) := by
  rw [G_succ, prob_congr p L (E := fun x => cnt 0 x + 1 = k + 1 ∧ cnt 1 x = j + 1)
    (F := fun x => cnt 0 x = k ∧ cnt 1 x = j + 1) (by cnt_iff), prob_congr p L
    (E := fun x => cnt 0 x = k + 1 ∧ cnt 1 x + 1 = j + 1)
    (F := fun x => cnt 0 x = k + 1 ∧ cnt 1 x = j) (by cnt_iff)]; unfold G; ring

lemma Hm_0 (p : Fin 3 → ℝ) (L : ℕ) : Hm p (L + 1) 0 = p 2 * Hm p L 0 := by
  rw [Hm_succ, prob_congr p L (E := fun x => cnt 0 x + cnt 1 x + 1 = 0) (F := fun _ => False)
    (by cnt_iff), prob_false]; ring

lemma Hm_s (p : Fin 3 → ℝ) (L N : ℕ) :
    Hm p (L + 1) (N + 1) = (p 0 + p 1) * Hm p L N + p 2 * Hm p L (N + 1) := by
  rw [Hm_succ, prob_congr p L (E := fun x => cnt 0 x + cnt 1 x + 1 = N + 1)
    (F := fun x => cnt 0 x + cnt 1 x = N) (by cnt_iff)]; rfl

/-- The product form, without division: `P(w σ = k, w τ = j) · s^(k+j) = C(k+j, k) p₀^k p₁^j
P(w σ + w τ = k + j)` with `s = p₀ + p₁`.  Induction on the number of units. -/
theorem G_eq (p : Fin 3 → ℝ) (L : ℕ) : ∀ k j : ℕ,
    G p L k j * (p 0 + p 1) ^ (k + j) =
      ((k + j).choose k : ℝ) * p 0 ^ k * p 1 ^ j * Hm p L (k + j) := by
  induction L with
  | zero =>
    intro k j
    have hc : ∀ i (x : Fin 0 → Fin 3), cnt i x = 0 := fun i x => by simp [cnt]
    unfold G Hm prob
    simp only [hc, sum_singleton, univ_eq_empty, prod_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk <;> rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · simp [show (0 : ℕ) ≠ j by omega]
    · simp [show (0 : ℕ) ≠ k by omega]
    · simp [show (0 : ℕ) ≠ k by omega, show (0 : ℕ) ≠ k + j by omega]
  | succ L ih =>
    intro k j
    rcases k with _ | k <;> rcases j with _ | j
    · rw [G_00, Hm_0]; have := ih 0 0; simp only [add_zero, pow_zero, mul_one,
        Nat.choose_self, Nat.cast_one, one_mul] at this ⊢
      rw [this]
    · rw [G_0s, zero_add, Hm_s]
      have h1 := ih 0 j
      have h2 := ih 0 (j + 1)
      simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero] at h1 h2 ⊢
      linear_combination (p 1 * (p 0 + p 1)) * h1 + p 2 * h2
    · rw [G_s0, add_zero, Hm_s]
      have h1 := ih k 0
      have h2 := ih (k + 1) 0
      simp only [add_zero, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one] at h1 h2 ⊢
      linear_combination (p 0 * (p 0 + p 1)) * h1 + p 2 * h2
    · have e : k + 1 + (j + 1) = (k + 1 + j) + 1 := by ring
      rw [G_ss, e, Hm_s]
      have h1 := ih k (j + 1)
      have h2 := ih (k + 1) j
      have h3 := ih (k + 1) (j + 1)
      rw [show k + (j + 1) = k + 1 + j by ring] at h1
      rw [e] at h3
      have hpas : ((k + 1 + j + 1).choose (k + 1) : ℝ) =
          ((k + 1 + j).choose k : ℝ) + ((k + 1 + j).choose (k + 1) : ℝ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      linear_combination (p 0 * (p 0 + p 1)) * h1 + (p 1 * (p 0 + p 1)) * h2 + p 2 * h3 -
        (p 0 ^ (k + 1) * p 1 ^ (j + 1) * (p 0 + p 1) * Hm p L (k + 1 + j)) * hpas

/-- **Proposition 8.3 (`prop:rival`), the rival test.**  Let `σ` and `τ` be in conflict, with
i.i.d. units proposing `σ`, `τ` or neither with probabilities `p 0 = m_σ`, `p 1 = m_τ`, `p 2`
(exclusive outcomes, by Lemma 3.5), and `m_σ + m_τ ≠ 0`.  Conditionally on `w(σ) + w(τ) = N`,
`w(σ)` is binomial with parameters `N` and `m_σ / (m_σ + m_τ)`:
`P(w σ = k ∧ w σ + w τ = N) = C(N, k) a^k (1 - a)^(N - k) · P(w σ + w τ = N)`, `a = m_σ/(m_σ + m_τ)`.
-/
theorem rival (p : Fin 3 → ℝ) (hs : p 0 + p 1 ≠ 0) (L k N : ℕ) :
    prob p L (fun x => cnt 0 x = k ∧ cnt 0 x + cnt 1 x = N) =
      (N.choose k : ℝ) * (p 0 / (p 0 + p 1)) ^ k * (1 - p 0 / (p 0 + p 1)) ^ (N - k) *
        Hm p L N := by
  by_cases hk : k ≤ N
  · obtain ⟨j, rfl⟩ : ∃ j, N = k + j := ⟨N - k, by omega⟩
    rw [prob_congr p L (F := fun x => cnt 0 x = k ∧ cnt 1 x = j) (by cnt_iff)]
    have h := G_eq p L k j
    have hb : 1 - p 0 / (p 0 + p 1) = p 1 / (p 0 + p 1) := by field_simp; ring
    rw [hb, show k + j - k = j by omega, div_pow, div_pow]
    change G p L k j = _
    have hpow : (p 0 + p 1) ^ (k + j) ≠ 0 := pow_ne_zero _ hs
    rw [pow_add] at h hpow
    field_simp
    linear_combination h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul, zero_mul,
      prob_congr p L (F := fun _ => False) (by cnt_iff), prob_false]

/-- Under the null `m_σ = m_τ`, the conditional law is binomial with parameter `1/2`, independent
of the common rate: the exact test of the report. -/
theorem rival_null (p : Fin 3 → ℝ) (heq : p 0 = p 1) (hpos : p 0 ≠ 0) (L k N : ℕ) :
    prob p L (fun x => cnt 0 x = k ∧ cnt 0 x + cnt 1 x = N) =
      (N.choose k : ℝ) * (1 / 2) ^ N * Hm p L N := by
  have hs : p 0 + p 1 ≠ 0 := by rw [← heq, ← two_mul]; exact mul_ne_zero two_ne_zero hpos
  rw [rival p hs]
  have : p 0 / (p 0 + p 1) = 1 / 2 := by rw [← heq]; field_simp; ring
  rw [this]
  by_cases hk : k ≤ N
  · rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc (N.choose k : ℝ), ← pow_add,
      Nat.add_sub_cancel' hk]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The same statement with Mathlib's binomial law: for non-negative rates, the conditional law
of `w(σ)` given `w(σ) + w(τ) = N` is `ProbabilityTheory.binomial N a`, `a = m_σ/(m_σ + m_τ)`. -/
theorem rival_binomial (p : Fin 3 → ℝ) (h0 : 0 ≤ p 0) (h1 : 0 ≤ p 1) (hs : p 0 + p 1 ≠ 0)
    (L k N : ℕ) :
    prob p L (fun x => cnt 0 x = k ∧ cnt 0 x + cnt 1 x = N) =
      (ProbabilityTheory.binomial N ⟨p 0 / (p 0 + p 1), div_nonneg h0 (add_nonneg h0 h1),
        div_le_one_of_le₀ (by linarith) (add_nonneg h0 h1)⟩).real {k} * Hm p L N := by
  rw [ProbabilityTheory.binomial_real_singleton, rival p hs]


/-- Splitting an event by the count of outcome `0`. -/
lemma prob_ge_eq_sum (p : Fin 3 → ℝ) (L k N : ℕ) :
    prob p L (fun x => k ≤ cnt 0 x ∧ cnt 0 x + cnt 1 x = N) =
      ∑ i ∈ Icc k N, prob p L (fun x => cnt 0 x = i ∧ cnt 0 x + cnt 1 x = N) := by
  unfold prob
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [ite_and]
  rw [sum_ite_eq]
  by_cases h : cnt 0 x + cnt 1 x = N
  · by_cases hk : k ≤ cnt 0 x
    · have : cnt 0 x ∈ Icc k N := mem_Icc.mpr ⟨hk, by omega⟩
      simp [this, hk, h]
    · have : cnt 0 x ∉ Icc k N := fun hm => hk (mem_Icc.mp hm).1
      simp [this, hk]
  · simp [h]

/-- **Proposition 8.3 (`prop:rival`), the tail probability.**  For `σ`, `τ` in conflict and i.i.d.
units, `P(w σ ≥ k ∧ w σ + w τ = N) = (∑_{i = k}^{N} C(N, i) a^i (1 - a)^{N - i}) · P(w σ + w τ = N)`
with `a = m_σ / (m_σ + m_τ)`: conditionally on `N`, the tail of the binomial law, the `p`-value of
the rival test. -/
theorem rival_tail (p : Fin 3 → ℝ) (hs : p 0 + p 1 ≠ 0) (L k N : ℕ) :
    prob p L (fun x => k ≤ cnt 0 x ∧ cnt 0 x + cnt 1 x = N) =
      (∑ i ∈ Icc k N, (N.choose i : ℝ) * (p 0 / (p 0 + p 1)) ^ i *
        (1 - p 0 / (p 0 + p 1)) ^ (N - i)) * Hm p L N := by
  rw [prob_ge_eq_sum, sum_mul]
  exact sum_congr rfl fun i _ => rival p hs L i N

/-- **Proposition 8.3, the exact test.**  Under the null `m_σ = m_τ > 0`, the tail probability is
`P(w σ ≥ k | N) = 2^{-N} ∑_{i = k}^{N} C(N, i)`, whatever the common rate (product form). -/
theorem rival_tail_null (p : Fin 3 → ℝ) (heq : p 0 = p 1) (hpos : p 0 ≠ 0) (L k N : ℕ) :
    prob p L (fun x => k ≤ cnt 0 x ∧ cnt 0 x + cnt 1 x = N) =
      ((∑ i ∈ Icc k N, (N.choose i : ℝ)) * (1 / 2) ^ N) * Hm p L N := by
  rw [prob_ge_eq_sum, sum_mul, sum_mul]
  exact sum_congr rfl fun i _ => rival_null p heq hpos L i N

end Stemma.Rival
