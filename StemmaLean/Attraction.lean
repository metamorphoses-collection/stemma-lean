/-
The attraction model as a probability distribution, and the bounds of Theorem 8.5 of the
technical report (`thm:mechanisms`).

A rooted stemma is given by the clades `K` of its edges (`Mechanisms.lean`).  In one unit each edge
`e` independently innovates with probability `π e`; an innovation is attractive with probability
`α`.  An outcome is the set `M ⊆ K` of innovating edges with the set `A ⊆ M` of attractive ones,
of probability `wt M A = ∏_{A} π α · ∏_{M \ A} π (1 - α) · ∏_{K \ M} (1 - π)`.  The expected support
of a proposal `P` (a predicate of the outcome) is `ex P = ∑_{M, A} wt M A · [P]`.

Formalised:
* `sum_wt_A`: summing over the readings, an innovation set `M` has probability
  `∏_M π · ∏_{K \ M} (1 - π)`;
* `ex_split`: `m_τ = Λ_τ + R_τ` with `Λ_τ` the part of at most two innovations and
  `0 ≤ R_τ ≤ Pr(|M| ≥ 3)`;
* `P3_le`: `Pr(|M| ≥ 3) ≤ ∑_{|S| = 3} ∏_S π ≤ (∑ π)³ / 6`;
* `lambda_eq`: `Λ_τ` in closed form, a term `π_e ∏_{g ≠ e} (1 - π_g)` for each single edge that
  proposes `τ` and `π_e π_f ω_{ef} ∏_{g ≠ e, f} (1 - π_g)` for each pair, with
  `ω_{ef} = α² [τ proposed when both are attractive] + (1 - α²) [τ proposed otherwise]`, for
  proposals that depend only on the classes of witnesses (both codings);
* the three values of `ω`: `1` for retention in the unrooted coding, `α²` for coincidence in the
  rooted coding, `1 - α²` for overwrite in the rooted coding (`omega_retention`,
  `omega_coincidence`, `omega_overwrite`).
-/
import Mathlib
import StemmaLean.Mechanisms

open Finset
open scoped Classical

namespace Stemma.Attraction

open Stemma.Mechanisms

variable {n : ℕ}

/-- Which innovations are attractive. -/
def attOf (A : Finset (Finset (Fin n))) : Finset (Fin n) → Bool := fun C => decide (C ∈ A)

/-- The probability of the outcome: innovations on `M`, the attractive ones `A ⊆ M`. -/
noncomputable def wt (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ)
    (M A : Finset (Finset (Fin n))) : ℝ :=
  (∏ e ∈ A, π e * α) * (∏ e ∈ M \ A, π e * (1 - α)) * ∏ g ∈ K \ M, (1 - π g)

/-- The expected value of the indicator of `P`: the probability that a unit's outcome satisfies
`P`. -/
noncomputable def ex (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) : ℝ :=
  ∑ M ∈ K.powerset, ∑ A ∈ M.powerset, wt K π α M A * (if P M (attOf A) then 1 else 0)

section rates

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)

include hπ0 hπ1 hα0 hα1 in
lemma wt_nonneg (M A : Finset (Finset (Fin n))) : 0 ≤ wt K π α M A := by
  unfold wt
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact prod_nonneg fun e _ => mul_nonneg (hπ0 e) hα0
  · exact prod_nonneg fun e _ => mul_nonneg (hπ0 e) (by linarith)
  · exact prod_nonneg fun g _ => by linarith [hπ1 g]

/-- Summing over the readings: innovations exactly on `M` have probability
`∏_M π · ∏_{K \ M} (1 - π)`. -/
lemma sum_wt_A (M : Finset (Finset (Fin n))) :
    ∑ A ∈ M.powerset, wt K π α M A = (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) := by
  unfold wt
  rw [← sum_mul]
  congr 1
  rw [← prod_add (fun e => π e * α) (fun e => π e * (1 - α)) M]
  exact prod_congr rfl fun e _ => by ring

/-- The probability of three or more innovations. -/
noncomputable def P3 (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ) : ℝ :=
  ex K π α fun M _ => 3 ≤ M.card

include hπ0 hπ1 hα0 hα1 in
lemma ex_mono {P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (h : ∀ M att, P M att → Q M att) : ex K π α P ≤ ex K π α Q := by
  unfold ex
  refine sum_le_sum fun M _ => sum_le_sum fun A _ => ?_
  have := wt_nonneg (K := K) hπ0 hπ1 hα0 hα1 M A
  by_cases hP : P M (attOf A)
  · simp [hP, h _ _ hP]
  · by_cases hQ : Q M (attOf A) <;> simp [hP, hQ, this]

lemma ex_add (P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) :
    ex K π α P = ex K π α (fun M att => P M att ∧ Q M att) +
      ex K π α (fun M att => P M att ∧ ¬ Q M att) := by
  unfold ex
  rw [← sum_add_distrib]
  refine sum_congr rfl fun M _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun A _ => ?_
  by_cases hP : P M (attOf A) <;> by_cases hQ : Q M (attOf A) <;> simp [hP, hQ]

include hπ0 hπ1 hα0 hα1 in
/-- **Theorem 8.5, the sandwich.**  `m_τ = Λ_τ + R_τ`, with `Λ_τ` the part of at most two
innovations and `0 ≤ R_τ ≤ Pr(|M| ≥ 3)`. -/
theorem ex_split (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) :
    ex K π α P = ex K π α (fun M att => P M att ∧ M.card ≤ 2) +
      ex K π α (fun M att => P M att ∧ ¬ M.card ≤ 2) ∧
    0 ≤ ex K π α (fun M att => P M att ∧ ¬ M.card ≤ 2) ∧
    ex K π α (fun M att => P M att ∧ ¬ M.card ≤ 2) ≤ P3 K π α := by
  refine ⟨ex_add P _, ?_, ex_mono hπ0 hπ1 hα0 hα1 fun M att h => by omega⟩
  unfold ex
  exact sum_nonneg fun M _ => sum_nonneg fun A _ =>
    mul_nonneg (wt_nonneg hπ0 hπ1 hα0 hα1 M A) (by split_ifs <;> norm_num)

end rates

/-! ### Three or more innovations -/

/-- The elementary symmetric sum `e_k(π)` over `K`. -/
noncomputable def esymm (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ K.powersetCard k, ∏ e ∈ S, π e

lemma esymm_insert {K : Finset (Finset (Fin n))} {a : Finset (Fin n)} (ha : a ∉ K)
    (π : Finset (Fin n) → ℝ) (k : ℕ) :
    esymm (insert a K) π (k + 1) = esymm K π (k + 1) + π a * esymm K π k := by
  unfold esymm
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · refine congrArg _ (sum_congr rfl fun S hS => ?_)
    rw [prod_insert fun h => ha ((mem_powersetCard.mp hS).1 h)]
  · intro S hS S' hS' h
    have h1 : a ∉ S := fun h' => ha ((mem_powersetCard.mp hS).1 h')
    have h2 : a ∉ S' := fun h' => ha ((mem_powersetCard.mp hS').1 h')
    rw [← erase_insert h1, ← erase_insert h2]
    exact congrArg (fun s => erase s a) h
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨T, -, rfl⟩ := mem_image.mp hS'
    exact ha ((mem_powersetCard.mp hS).1 (mem_insert_self a T))

lemma esymm_zero (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) : esymm K π 0 = 1 := by
  simp [esymm]

lemma esymm_empty (π : Finset (Fin n) → ℝ) (k : ℕ) : esymm ∅ π (k + 1) = 0 := by
  rw [esymm, powersetCard_eq_empty.mpr (by simp), sum_empty]

lemma esymm_one (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) :
    esymm K π 1 = ∑ e ∈ K, π e := by
  simp [esymm, powersetCard_one]

/-- `e₂ ≤ (∑ π)² / 2` and `e₃ ≤ (∑ π)³ / 6` for non-negative rates. -/
lemma esymm_le (K : Finset (Finset (Fin n))) {π : Finset (Fin n) → ℝ} (hπ0 : ∀ e, 0 ≤ π e) :
    esymm K π 2 ≤ (∑ e ∈ K, π e) ^ 2 / 2 ∧ esymm K π 3 ≤ (∑ e ∈ K, π e) ^ 3 / 6 := by
  induction K using Finset.induction_on with
  | empty => simp [esymm_empty]
  | insert a K ha ih =>
    rw [esymm_insert ha π 2, esymm_insert ha π 1, esymm_one, sum_insert ha]
    have hp : 0 ≤ ∑ e ∈ K, π e := sum_nonneg fun e _ => hπ0 e
    have h2 := ih.1
    have h3 := ih.2
    have hpa := hπ0 a
    constructor
    · nlinarith
    · nlinarith [mul_nonneg hpa (mul_nonneg hpa hp), mul_nonneg hpa (mul_nonneg hp hp),
        mul_nonneg hpa (mul_nonneg hpa hpa)]

/-- A product over `K` of a choice between two factors, summed over the subsets `M ⊆ K` of the
first choice, is the product of the sums. -/
lemma sum_prod_ite (K : Finset (Finset (Fin n))) (a b : Finset (Fin n) → ℝ) :
    ∑ M ∈ K.powerset, (∏ e ∈ M, a e) * ∏ g ∈ K \ M, b g = ∏ e ∈ K, (a e + b e) :=
  (prod_add a b K).symm

section three

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)

/-- The probability that every edge of `S ⊆ K` innovates is `∏_S π`. -/
lemma sum_superset {S : Finset (Finset (Fin n))} (hS : S ⊆ K) :
    ∑ M ∈ K.powerset, (if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) =
      ∏ e ∈ S, π e := by
  have key : ∀ M ∈ K.powerset, (if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) =
      (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (if g ∈ S then 0 else 1 - π g) := by
    intro M hM
    by_cases h : S ⊆ M
    · rw [if_pos h]
      congr 1
      refine prod_congr rfl fun g hg => ?_
      rw [if_neg fun hgS => (mem_sdiff.mp hg).2 (h hgS)]
    · rw [if_neg h]
      obtain ⟨g, hgS, hgM⟩ := not_subset.mp h
      have : ∏ g ∈ K \ M, (if g ∈ S then (0 : ℝ) else 1 - π g) = 0 :=
        prod_eq_zero (mem_sdiff.mpr ⟨hS hgS, hgM⟩) (by simp [hgS])
      rw [this, mul_zero]
  rw [sum_congr rfl key, sum_prod_ite K π fun g => if g ∈ S then 0 else 1 - π g]
  rw [← prod_sdiff hS]
  have h1 : ∏ e ∈ K \ S, (π e + if e ∈ S then 0 else 1 - π e) = 1 :=
    prod_eq_one fun e he => by rw [if_neg (mem_sdiff.mp he).2]; ring
  have h2 : ∏ e ∈ S, (π e + if e ∈ S then 0 else 1 - π e) = ∏ e ∈ S, π e :=
    prod_congr rfl fun e he => by rw [if_pos he, add_zero]
  rw [h1, h2, one_mul]

include hπ0 hπ1 in
/-- **Theorem 8.5, three innovations.**  `Pr(|M| ≥ 3) ≤ ∑_{|S| = 3} ∏_S π ≤ (∑ π)³ / 6`. -/
theorem P3_le : P3 K π α ≤ esymm K π 3 ∧ esymm K π 3 ≤ (∑ e ∈ K, π e) ^ 3 / 6 := by
  refine ⟨?_, (esymm_le K hπ0).2⟩
  have hx : ∀ M, 0 ≤ (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) := fun M =>
    mul_nonneg (prod_nonneg fun e _ => hπ0 e) (prod_nonneg fun g _ => by linarith [hπ1 g])
  have hP3 : P3 K π α = ∑ M ∈ K.powerset,
      (if 3 ≤ M.card then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) := by
    unfold P3 ex
    refine sum_congr rfl fun M _ => ?_
    by_cases h : 3 ≤ M.card
    · simp only [h, if_true, mul_one]; exact sum_wt_A M
    · simp [h]
  rw [hP3]
  -- each `M` with three innovations contains a triple
  calc ∑ M ∈ K.powerset, (if 3 ≤ M.card then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0)
      ≤ ∑ M ∈ K.powerset, ∑ S ∈ K.powersetCard 3,
          (if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) := by
        refine sum_le_sum fun M hM => ?_
        split_ifs with h
        · obtain ⟨S, hSM, hS⟩ := exists_subset_card_eq h
          have hSK : S ∈ K.powersetCard 3 :=
            mem_powersetCard.mpr ⟨hSM.trans (mem_powerset.mp hM), hS⟩
          refine le_trans ?_ (single_le_sum (f := fun S =>
            if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0)
            (fun S _ => by split_ifs <;> first | exact hx M | exact le_rfl) hSK)
          rw [if_pos hSM]
        · exact sum_nonneg fun S _ => by split_ifs <;> first | exact hx M | exact le_rfl
    _ = ∑ S ∈ K.powersetCard 3, ∏ e ∈ S, π e := by
        rw [sum_comm]
        exact sum_congr rfl fun S hS => sum_superset (mem_powersetCard.mp hS).1

end three

/-! ### Proposals depend only on the classes -/

/-- A proposal that depends only on the partition into classes and on which class keeps the
original reading. -/
def ClassDet (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) : Prop :=
  ∀ M att att', (∀ x y, read M att x = read M att y ↔ read M att' x = read M att' y) →
    (∀ x, read M att x = .orig ↔ read M att' x = .orig) → (P M att ↔ P M att')

lemma propU_iff {M : Finset (Finset (Fin n))} {att att' : Finset (Fin n) → Bool}
    (h1 : ∀ x y, read M att x = read M att y ↔ read M att' x = read M att' y) (A : Finset (Fin n)) :
    PropU M att A → PropU M att' A := by
  rintro ⟨⟨y, hy⟩, v, rfl⟩
  refine ⟨⟨y, hy⟩, read M att' y, ?_⟩
  · ext x
    rw [mem_cls, mem_cls]
    have hyv := mem_cls.mp hy
    rw [← hyv]
    exact h1 x y

lemma propR_iff {M : Finset (Finset (Fin n))} {att att' : Finset (Fin n) → Bool}
    (h1 : ∀ x y, read M att x = read M att y ↔ read M att' x = read M att' y)
    (h2 : ∀ x, read M att x = .orig ↔ read M att' x = .orig) (A : Finset (Fin n)) :
    PropR M att A → PropR M att' A := by
  rintro ⟨⟨y, hy⟩, v, hv, rfl⟩
  have hyv := mem_cls.mp hy
  refine ⟨⟨y, hy⟩, read M att' y, fun h => hv (hyv ▸ (h2 y).mpr h), ?_⟩
  ext x
  rw [mem_cls, mem_cls, ← hyv]
  exact h1 x y

/-- The unrooted coding proposes the split `τ | τᶜ`. -/
def PU (τ : Finset (Fin n)) (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) : Prop :=
  PropU M att τ ∨ PropU M att τᶜ

/-- The rooted coding proposes the cluster `τ`. -/
def PR (τ : Finset (Fin n)) (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) : Prop :=
  PropR M att τ

lemma classDet_PU (τ : Finset (Fin n)) : ClassDet (PU τ) := by
  intro M att att' h1 _
  have h1' : ∀ x y, read M att' x = read M att' y ↔ read M att x = read M att y :=
    fun x y => (h1 x y).symm
  exact ⟨fun h => h.imp (propU_iff h1 _) (propU_iff h1 _),
    fun h => h.imp (propU_iff h1' _) (propU_iff h1' _)⟩

lemma classDet_PR (τ : Finset (Fin n)) : ClassDet (PR τ) := by
  intro M att att' h1 h2
  exact ⟨propR_iff h1 h2 τ, propR_iff (fun x y => (h1 x y).symm) (fun x => (h2 x).symm) τ⟩

/-! ### When the partition is the same -/

lemma rel_single {e : Finset (Fin n)} (att att' : Finset (Fin n) → Bool) :
    (∀ x y, read {e} att x = read {e} att y ↔ read {e} att' x = read {e} att' y) ∧
    (∀ x, read {e} att x = .orig ↔ read {e} att' x = .orig) := by
  have hr : ∀ (a : Finset (Fin n) → Bool) x,
      read {e} a x = if x ∈ e then val a e else .orig := by
    intro a x
    split_ifs with hx
    · exact read_of_lowest ⟨mem_singleton_self e, hx, fun D hD _ => (mem_singleton.mp hD) ▸ le_rfl⟩
    · exact read_of_none (by simpa using hx)
  have h0 := val_ne_orig att e
  have h0' := val_ne_orig att' e
  constructor
  · intro x y
    rw [hr, hr, hr, hr]
    by_cases hx : x ∈ e <;> by_cases hy : y ∈ e <;> simp [hx, hy, h0, h0', Ne.symm h0, Ne.symm h0']
  · intro x
    rw [hr, hr]
    by_cases hx : x ∈ e <;> simp [hx, h0, h0']

/-- Three regions with the values of `a`, of `b`, and the original reading: the partition depends
on the readings only through whether both are attractive. -/
lemma rel3 {a b : Finset (Fin n)} (hab : a ≠ b) (att att' : Finset (Fin n) → Bool)
    (hb : (att a = true ∧ att b = true) ↔ (att' a = true ∧ att' b = true))
    (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q] :
    (∀ x y, ((if p x then val att a else if q x then val att b else Rd.orig) =
        (if p y then val att a else if q y then val att b else Rd.orig) ↔
      (if p x then val att' a else if q x then val att' b else Rd.orig) =
        (if p y then val att' a else if q y then val att' b else Rd.orig))) ∧
    (∀ x, (if p x then val att a else if q x then val att b else Rd.orig) = Rd.orig ↔
      (if p x then val att' a else if q x then val att' b else Rd.orig) = Rd.orig) := by
  have hb' : (att b = true ∧ att a = true) ↔ (att' b = true ∧ att' a = true) :=
    and_comm.trans (hb.trans and_comm)
  constructor
  · intro x y
    by_cases px : p x <;> by_cases qx : q x <;> by_cases py : p y <;> by_cases qy : q y <;>
      simp only [px, qx, py, qy, if_true, if_false, val_eq_iff att hab, val_eq_iff att' hab,
        val_eq_iff att (Ne.symm hab), val_eq_iff att' (Ne.symm hab), val_ne_orig, orig_ne_val,
        iff_self] <;>
      first | exact hb | exact hb' | trivial
  · intro x
    by_cases px : p x <;> by_cases qx : q x <;>
      simp only [px, qx, if_true, if_false, val_ne_orig, iff_self]

lemma rel_pair {e f : Finset (Fin n)} (hef : e ≠ f) (hlam : Disjoint e f ∨ f ⊂ e ∨ e ⊂ f)
    (att att' : Finset (Fin n) → Bool)
    (hb : (att e = true ∧ att f = true) ↔ (att' e = true ∧ att' f = true)) :
    (∀ x y, read {e, f} att x = read {e, f} att y ↔ read {e, f} att' x = read {e, f} att' y) ∧
    (∀ x, read {e, f} att x = .orig ↔ read {e, f} att' x = .orig) := by
  rcases hlam with hd | hfe | hef'
  · have h := rel3 hef att att' hb (· ∈ e) (· ∈ f)
    simp only [← read_disj att hd, ← read_disj att' hd] at h
    exact h
  · have h := rel3 (Ne.symm hef) att att' (and_comm.trans (hb.trans and_comm)) (· ∈ f) (· ∈ e)
    simp only [← read_nest att hfe, ← read_nest att' hfe] at h
    exact h
  · have h := rel3 hef att att' hb (· ∈ e) (· ∈ f)
    rw [pair_comm]
    simp only [← read_nest att hef', ← read_nest att' hef'] at h
    exact h

/-! ### The closed form of `Λ_τ` -/

/-- The fraction of the readings of a pair `S = {e, f}` of innovations for which the unit
proposes `P`: `α²` when both are attractive, `1 - α²` otherwise. -/
noncomputable def omega (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) (α : ℝ)
    (S : Finset (Finset (Fin n))) : ℝ :=
  α ^ 2 * (if P S (attOf S) then 1 else 0) + (1 - α ^ 2) * (if P S (attOf ∅) then 1 else 0)

/-- The clades of a rooted stemma: two distinct clades are disjoint or nested. -/
def Laminar (K : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f ∨ f ⊂ e ∨ e ⊂ f

/-- **Theorem 8.5, `Λ_τ` in closed form.**  For a proposal `P` determined by the classes of
witnesses (`PU τ`, `PR τ`), the part of `m_τ` with at most two innovations is
`[P(no innovation)] ∏ (1 - π) + ∑_e π_e ∏_{g ≠ e} (1 - π_g) [e alone proposes τ]
  + ∑_{e,f} π_e π_f ω_{ef} ∏_{g ≠ e,f} (1 - π_g)`. -/
theorem lambda_eq {K : Finset (Finset (Fin n))} (hK : Laminar K) (π : Finset (Fin n) → ℝ) (α : ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) (hP : ClassDet P) :
    ex K π α (fun M att => P M att ∧ M.card ≤ 2) =
      (if P ∅ (attOf ∅) then 1 else 0) * ∏ g ∈ K, (1 - π g) +
      ∑ e ∈ K, π e * (∏ g ∈ K.erase e, (1 - π g)) * (if P {e} (attOf ∅) then 1 else 0) +
      ∑ S ∈ K.powersetCard 2, (∏ e ∈ S, π e) * omega P α S * ∏ g ∈ K \ S, (1 - π g) := by
  set g : Finset (Finset (Fin n)) → ℝ := fun M =>
    ∑ A ∈ M.powerset, wt K π α M A * (if P M (attOf A) then 1 else 0)
  have h1 : ex K π α (fun M att => P M att ∧ M.card ≤ 2) =
      ∑ M ∈ K.powerset.filter (fun M => M.card ≤ 2), g M := by
    unfold ex
    rw [sum_filter]
    refine sum_congr rfl fun M _ => ?_
    by_cases h : M.card ≤ 2
    · simp only [h, and_true, if_true, g]
    · simp [h]
  have hsplit : K.powerset.filter (fun M => M.card ≤ 2) =
      (K.powersetCard 0 ∪ K.powersetCard 1) ∪ K.powersetCard 2 := by
    ext M
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    by_cases hM : M ⊆ K <;> simp only [hM, true_and, false_and, or_false] <;> omega
  have hdisj : ∀ {i j : ℕ}, i ≠ j → Disjoint (K.powersetCard i) (K.powersetCard j) := by
    intro i j hij
    rw [disjoint_left]
    intro M h1 h2
    exact hij ((mem_powersetCard.mp h1).2.symm.trans (mem_powersetCard.mp h2).2)
  rw [h1, hsplit, sum_union (disjoint_union_left.mpr ⟨hdisj (by norm_num), hdisj (by norm_num)⟩),
    sum_union (hdisj (by norm_num))]
  congr 1
  congr 1
  · -- no innovation
    rw [powersetCard_zero, sum_singleton]
    simp [g, wt, attOf]
  · -- one innovation
    rw [powersetCard_one, sum_map]
    refine sum_congr rfl fun e he => ?_
    simp only [Function.Embedding.coeFn_mk, g]
    have hinv : ∀ A, (P {e} (attOf A) ↔ P {e} (attOf ∅)) := fun A =>
      hP _ _ _ (rel_single _ _).1 (rel_single _ _).2
    rw [sum_congr rfl fun A _ => by rw [if_congr (hinv A) rfl rfl], ← sum_mul, sum_wt_A,
      prod_singleton, sdiff_singleton_eq_erase]
  · -- two innovations
    refine sum_congr rfl fun S hS => ?_
    obtain ⟨hSK, hS2⟩ := mem_powersetCard.mp hS
    obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp hS2
    have heK : e ∈ K := hSK (by simp)
    have hfK : f ∈ K := hSK (by simp)
    set S : Finset (Finset (Fin n)) := {e, f} with hSdef
    set yv : ℝ := if P S (attOf ∅) then 1 else 0
    set xv : ℝ := if P S (attOf S) then 1 else 0
    have hinv : ∀ A ∈ S.powerset,
        (if P S (attOf A) then (1 : ℝ) else 0) = if A = S then xv else yv := by
      intro A hA
      by_cases hAS : A = S
      · rw [if_pos hAS, hAS]
      · rw [if_neg hAS]
        have hb : (attOf A e = true ∧ attOf A f = true) ↔
            (attOf (∅ : Finset (Finset (Fin n))) e = true ∧ attOf ∅ f = true) := by
          simp only [attOf, decide_eq_true_eq, notMem_empty, and_false, iff_false]
          rintro ⟨h1, h2⟩
          apply hAS
          refine subset_antisymm (mem_powerset.mp hA) ?_
          intro x hx; simp only [hSdef, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have r := rel_pair hef (hK e heK f hfK hef) _ _ hb
        exact if_congr (hP _ _ _ r.1 r.2) rfl rfl
    have hg : g S = ∑ A ∈ S.powerset, wt K π α S A * yv + wt K π α S S * (xv - yv) := by
      simp only [g]
      rw [sum_congr rfl fun A hA => by rw [hinv A hA]]
      rw [← sum_erase_add _ _ (mem_powerset_self S), ← sum_erase_add _ _ (mem_powerset_self S)]
      rw [sum_congr rfl fun A hA => by rw [if_neg (ne_of_mem_erase hA)], if_pos rfl]
      ring
    have hwS : wt K π α S S = α ^ 2 * ((∏ x ∈ S, π x) * ∏ g ∈ K \ S, (1 - π g)) := by
      unfold wt
      rw [sdiff_self, bot_eq_empty, prod_empty, mul_one, prod_mul_distrib, prod_const, hS2]
      ring
    rw [hg, ← sum_mul, sum_wt_A, hwS, omega]
    ring

/-! ### The three values of `ω` -/

lemma attOf_pair {e f : Finset (Fin n)} : attOf {e, f} e = true ∧ attOf {e, f} f = true := by
  simp [attOf]

lemma attOf_empty (e f : Finset (Fin n)) :
    ¬ (attOf (∅ : Finset (Finset (Fin n))) e = true ∧ attOf ∅ f = true) := by
  simp [attOf]

/-- **Retention** (unrooted coding, disjoint clades): `ω = 1`. -/
theorem omega_retention {e f : Finset (Fin n)} (hd : Disjoint e f) (he : e.Nonempty)
    (hf : f.Nonempty) (hrest : (e ∪ f)ᶜ.Nonempty) (α : ℝ) :
    omega (PU (e ∪ f)) α {e, f} = 1 := by
  have h : ∀ att, PU (e ∪ f) {e, f} att := fun att =>
    Or.inr ((retention_coincidence att hd he hf).1 hrest)
  simp [omega, h]

/-- **Coincidence** (rooted coding, disjoint clades): `ω = α²`. -/
theorem omega_coincidence {e f : Finset (Fin n)} (hd : Disjoint e f) (he : e.Nonempty)
    (hf : f.Nonempty) (α : ℝ) :
    omega (PR (e ∪ f)) α {e, f} = α ^ 2 := by
  have h1 : PR (e ∪ f) {e, f} (attOf {e, f}) :=
    ((retention_coincidence _ hd he hf).2.1).mpr attOf_pair
  have h2 : ¬ PR (e ∪ f) {e, f} (attOf ∅) := fun h =>
    attOf_empty e f (((retention_coincidence _ hd he hf).2.1).mp h)
  simp [omega, h1, h2]

/-- **Overwrite** (rooted coding, nested clades `C_f ⊊ C_e`): `ω = 1 - α²`. -/
theorem omega_overwrite_rooted {e f : Finset (Fin n)} (hfe : f ⊂ e) (hf : f.Nonempty) (α : ℝ) :
    omega (PR (e \ f)) α {e, f} = 1 - α ^ 2 := by
  have h1 : ¬ PR (e \ f) {e, f} (attOf {e, f}) := fun h =>
    ((overwrite _ hfe hf).2.1.mp h) attOf_pair
  have h2 : PR (e \ f) {e, f} (attOf ∅) := (overwrite _ hfe hf).2.1.mpr (attOf_empty e f)
  simp [omega, h1, h2]

/-- The complement of `C_e \ C_f` is never a class, for a proper clade `C_e`. -/
lemma not_class_compl {e f : Finset (Fin n)} (hfe : f ⊂ e) (hf : f.Nonempty) (he : e ≠ univ)
    (att : Finset (Fin n) → Bool) : ¬ PropU {e, f} att (e \ f)ᶜ := by
  intro h
  obtain ⟨z, hz⟩ : (e \ f).Nonempty := sdiff_nonempty.mpr (not_subset_of_ssubset hfe)
  obtain ⟨y, hy⟩ := hf
  obtain ⟨w, hw⟩ : ∃ w, w ∉ e := by
    by_contra hc; push Not at hc; exact he (eq_univ_of_forall hc)
  have hz' : z ∉ (e \ f)ᶜ := by simp [hz]
  rcases (overwrite att hfe ⟨y, hy⟩).2.2.1 _ h with h1 | h1 | h1 | h1
  · have : w ∈ (e \ f)ᶜ := by simp [hw]
    rw [h1] at this; exact hw (hfe.1 this)
  · rw [h1] at hz'; exact hz' (mem_sdiff.mp hz).1
  · have : y ∈ (e \ f)ᶜ := by simp [hy]
    rw [h1] at this; exact (mem_compl.mp this) (hfe.1 hy)
  · rw [h1] at hz'; exact hz' hz

/-- **Overwrite** (unrooted coding, nested clades, `C_e` proper): `ω = 1 - α²`. -/
theorem omega_overwrite_unrooted {e f : Finset (Fin n)} (hfe : f ⊂ e) (hf : f.Nonempty)
    (he : e ≠ univ) (α : ℝ) :
    omega (PU (e \ f)) α {e, f} = 1 - α ^ 2 := by
  have hPU : ∀ att, PU (e \ f) {e, f} att ↔ ¬ (att e = true ∧ att f = true) := fun att =>
    ⟨fun h => h.elim (overwrite att hfe hf).1.mp (fun h' => absurd h' (not_class_compl hfe hf he att)),
      fun h => Or.inl ((overwrite att hfe hf).1.mpr h)⟩
  have h1 : ¬ PU (e \ f) {e, f} (attOf {e, f}) := fun h => (hPU _).mp h attOf_pair
  have h2 : PU (e \ f) {e, f} (attOf ∅) := (hPU _).mpr (attOf_empty e f)
  simp [omega, h1, h2]

end Stemma.Attraction

namespace Stemma.Attraction

open Stemma.Mechanisms

variable {n : ℕ}

/-! ### Positivity of the false split of a polytomy (Proposition 8.1) -/

section pos

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)

include hπ0 hπ1 hα0 hα1 in
/-- The expected support is at least the contribution of one pair of innovations. -/
lemma ex_ge_pair (hK : Laminar K) (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop)
    (hP : ClassDet P) {S : Finset (Finset (Fin n))} (hS : S ∈ K.powersetCard 2) :
    (∏ e ∈ S, π e) * omega P α S * ∏ g ∈ K \ S, (1 - π g) ≤ ex K π α P := by
  have hω : ∀ T, 0 ≤ omega P α T := fun T => by
    unfold omega
    have : α ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ α ^ 2 := sq_nonneg α
    refine add_nonneg (mul_nonneg ‹_› ?_) (mul_nonneg (by linarith) ?_) <;>
      split_ifs <;> norm_num
  have hq : ∀ T, 0 ≤ ∏ g ∈ K \ T, (1 - π g) := fun T =>
    prod_nonneg fun g _ => by linarith [hπ1 g]
  have hp : ∀ T : Finset (Finset (Fin n)), 0 ≤ ∏ e ∈ T, π e := fun T =>
    prod_nonneg fun e _ => hπ0 e
  obtain ⟨hsplit, hR, -⟩ := ex_split hπ0 hπ1 hα0 hα1 (K := K) P
  rw [hsplit, lambda_eq hK π α P hP]
  have h0 : 0 ≤ (if P ∅ (attOf ∅) then (1 : ℝ) else 0) * ∏ g ∈ K, (1 - π g) :=
    mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun g _ => by linarith [hπ1 g])
  have h1 : 0 ≤ ∑ e ∈ K, π e * (∏ g ∈ K.erase e, (1 - π g)) *
      (if P {e} (attOf ∅) then (1 : ℝ) else 0) :=
    sum_nonneg fun e _ => mul_nonneg (mul_nonneg (hπ0 e)
      (prod_nonneg fun g _ => by linarith [hπ1 g])) (by split_ifs <;> norm_num)
  have h2 := single_le_sum (f := fun T => (∏ e ∈ T, π e) * omega P α T * ∏ g ∈ K \ T, (1 - π g))
    (fun T _ => mul_nonneg (mul_nonneg (hp T) (hω T)) (hq T)) hS
  linarith

end pos

/-- **Proposition 8.1, positivity.**  In the attraction model with rates in `(0,1)`, let two
distinct, disjoint, non-empty clades `C_i`, `C_j` (two branches of a polytomy) leave some witness
outside.  The false split `(C_i ∪ C_j) | rest` has positive expected support in the unrooted
coding, and the cluster `C_i ∪ C_j` has positive expected support in the rooted coding when
`α > 0`: two innovations on the branches propose it (Theorem 8.5(ii)). -/
theorem polytomy_support_pos {K : Finset (Finset (Fin n))} (hK : Laminar K)
    {π : Finset (Fin n) → ℝ} {α : ℝ} (hπ0 : ∀ e, 0 < π e) (hπ1 : ∀ e, π e < 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {ci cj : Finset (Fin n)} (hi : ci ∈ K) (hj : cj ∈ K) (hij : ci ≠ cj)
    (hd : Disjoint ci cj) (hne_i : ci.Nonempty) (hne_j : cj.Nonempty)
    (hrest : (ci ∪ cj)ᶜ.Nonempty) :
    0 < ex K π α (PU (ci ∪ cj)) ∧ (0 < α → 0 < ex K π α (PR (ci ∪ cj))) := by
  have hS : ({ci, cj} : Finset (Finset (Fin n))) ∈ K.powersetCard 2 :=
    mem_powersetCard.mpr ⟨insert_subset hi (singleton_subset_iff.mpr hj), card_pair hij⟩
  have hp : 0 < ∏ e ∈ ({ci, cj} : Finset (Finset (Fin n))), π e := prod_pos fun e _ => hπ0 e
  have hq : 0 < ∏ g ∈ K \ {ci, cj}, (1 - π g) := prod_pos fun g _ => by linarith [hπ1 g]
  have h0 : ∀ e, 0 ≤ π e := fun e => (hπ0 e).le
  have h1 : ∀ e, π e ≤ 1 := fun e => (hπ1 e).le
  refine ⟨?_, fun hα => ?_⟩
  · have := ex_ge_pair h0 h1 hα0 hα1 hK (PU (ci ∪ cj)) (classDet_PU _) hS
    rw [omega_retention hd hne_i hne_j hrest, mul_one] at this
    exact lt_of_lt_of_le (mul_pos hp hq) this
  · have := ex_ge_pair h0 h1 hα0 hα1 hK (PR (ci ∪ cj)) (classDet_PR _) hS
    rw [omega_coincidence hd hne_i hne_j] at this
    exact lt_of_lt_of_le (mul_pos (mul_pos hp (pow_pos hα 2)) hq) this


/-- **Proposition 8.1 and Theorem 8.5(ii), with the report's size conditions.**  As
`polytomy_support_pos`, with at least two witnesses outside `C_i ∪ C_j` and rates in `[0,1]`,
positive on the two branches `C_i`, `C_j` and below `1` on the other edges of `K`.  The false split
`(C_i ∪ C_j) | rest` is non-trivial (two witnesses on each side) and has positive expected support
in the unrooted coding; the cluster `C_i ∪ C_j` is non-trivial (two witnesses, not all) and has
positive expected support in the rooted coding when `α > 0`. -/
theorem polytomy_support_pos_nt {K : Finset (Finset (Fin n))} (hK : Laminar K)
    {π : Finset (Fin n) → ℝ} {α : ℝ} (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {ci cj : Finset (Fin n)} (hi : ci ∈ K) (hj : cj ∈ K) (hij : ci ≠ cj)
    (hd : Disjoint ci cj) (hne_i : ci.Nonempty) (hne_j : cj.Nonempty)
    (hpi : 0 < π ci) (hpj : 0 < π cj) (hlt : ∀ g ∈ K, g ≠ ci → g ≠ cj → π g < 1)
    (hrest : 2 ≤ (ci ∪ cj)ᶜ.card) :
    SplitNT (ci ∪ cj) ∧ ClusterNT (ci ∪ cj) ∧
      0 < ex K π α (PU (ci ∪ cj)) ∧ (0 < α → 0 < ex K π α (PR (ci ∪ cj))) := by
  have h2 := two_le_card_union hd hne_i hne_j
  have hrest' : (ci ∪ cj)ᶜ.Nonempty := card_pos.mp (by omega)
  have hS : ({ci, cj} : Finset (Finset (Fin n))) ∈ K.powersetCard 2 :=
    mem_powersetCard.mpr ⟨insert_subset hi (singleton_subset_iff.mpr hj), card_pair hij⟩
  have hp : 0 < ∏ e ∈ ({ci, cj} : Finset (Finset (Fin n))), π e := by
    rw [prod_pair hij]; exact mul_pos hpi hpj
  have hq : 0 < ∏ g ∈ K \ {ci, cj}, (1 - π g) := prod_pos fun g hg => by
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hg
    linarith [hlt g hg.1 hg.2.1 hg.2.2]
  refine ⟨⟨h2, hrest⟩, ⟨h2, fun e => ?_⟩, ?_, fun hα => ?_⟩
  · rw [e, compl_univ, card_empty] at hrest; omega
  · have := ex_ge_pair hπ0 hπ1 hα0 hα1 hK (PU (ci ∪ cj)) (classDet_PU _) hS
    rw [omega_retention hd hne_i hne_j hrest', mul_one] at this
    exact lt_of_lt_of_le (mul_pos hp hq) this
  · have := ex_ge_pair hπ0 hπ1 hα0 hα1 hK (PR (ci ∪ cj)) (classDet_PR _) hS
    rw [omega_coincidence hd hne_i hne_j] at this
    exact lt_of_lt_of_le (mul_pos (mul_pos hp (pow_pos hα 2)) hq) this

end Stemma.Attraction
