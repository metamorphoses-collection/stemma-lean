/-
The attraction model with several attractive readings, and the transfer of the bounds of
Theorem 8.5 of the technical report (`thm:mechanisms`) from the model with one attractive reading
(`Attraction.lean`).

A rooted stemma is given by the clades `K` of its edges (`Mechanisms.lean`).  There are `k`
attractive readings, taken with probabilities `a j ≥ 0`, `∑ a ≤ 1`.  In one unit each edge `e`
independently innovates with probability `π e`; an innovation takes the attractive reading `j` with
probability `a j`, or a reading of its own with probability `1 - ∑ a`.  An outcome is the set
`M ⊆ K` of innovating edges with an assignment `g : Finset (Fin n) → Option (Fin k)` of readings
(`some j`: attractive reading `j`; `none`: the edge's own reading), of probability
`wtG M g = ∏_C fac M C (g C) · ∏_{K \ M} (1 - π)`, where an innovating edge contributes
`π_C · q(g C)` (`q (some j) = a j`, `q none = 1 - ∑ a`) and a non-innovating edge forces
`g C = none` (the value of `g` off `M` carries no probability).  A witness reads the value of the
lowest innovating edge above it (`readG`), or the original reading.  The two codings propose, as
in `Mechanisms.lean`, the split of a class (`PUG τ`: `τ` or `τᶜ` is a class) and the cluster of a
class of a non-original reading (`PRG τ`).  Let `A = ∑_j a_j²` and `α = √A` (`alpha`).

Formalised:
* `sumsq_le`, `alpha_sq`, `alpha_nonneg`, `alpha_le_one`: `∑ a² ≤ ∑ a ≤ 1`, so `0 ≤ α ≤ 1` and
  `α² = A`;
* `reduction`, `reduction_PU`, `reduction_PR` (deterministic, every outcome): with at most two
  innovations, the partition into classes and the class keeping the original reading coincide with
  those of the one-reading model in which the two innovations are both attractive iff they carry
  the same attractive reading (`attG`); hence `PUG τ M g ↔ PU τ M (attG M g)` and
  `PRG τ M g ↔ PR τ M (attG M g)`.  No laminarity is needed;
* `lambdaG_PU`, `lambdaG_PR`: the part of the expected support with at most two innovations equals
  the one-reading `Λ_τ` at `α = √A`, for every split and cluster `τ` (`lambdaG_eq` for every
  proposal determined by the classes, `lambdaG_closed` the closed form of
  `Attraction.lambda_eq` with `α²` replaced by `A`);
* `exG_Monly`, `P3G_eq`: a predicate of the innovation set alone has the same probability in both
  models, in particular `Pr(|M| ≥ 3) = P3 K π α`;
* `exG_split`: the sandwich `m_τ = Λ_τ + R_τ`, `0 ≤ R_τ ≤ Pr(|M| ≥ 3)`;
* `transfer_PU`, `transfer_PR`, `transfer_cubic`: `|m^G_τ - m_τ(α)| ≤ Pr(|M| ≥ 3) ≤ (∑ π)³ / 6`,
  so every leading-order result on the one-reading model transfers with `α = √A`;
* `PRG_PUG`, `dominanceG`: the comparison of the codings at every order: a cluster proposed in the
  rooted coding has its split proposed in the unrooted coding, outcome by outcome, so
  `m^root_C ≤ m^unr_τ` (and for `Cᶜ`) exactly; `PRG_PUG_nt` with the report's size conditions.
-/
import Mathlib
import StemmaLean.Attraction

open Finset
open scoped Classical

namespace Stemma.MultiAttraction

open Stemma.Mechanisms Stemma.Attraction

variable {n k : ℕ}

/-! ### Readings and proposals -/

/-- A reading: the original one, the attractive reading `j`, or the own reading of an innovation
(named by its clade). -/
inductive RdG (n k : ℕ)
  | orig : RdG n k
  | attr : Fin k → RdG n k
  | own : Finset (Fin n) → RdG n k
  deriving DecidableEq

/-- The value of an innovation on `C` under the assignment `g`. -/
def valG (g : Finset (Fin n) → Option (Fin k)) (C : Finset (Fin n)) : RdG n k :=
  match g C with
  | some j => .attr j
  | none => .own C

/-- The reading of witness `x`: the value of the lowest innovating edge above it, or the original
reading. -/
noncomputable def readG (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k))
    (x : Fin n) : RdG n k :=
  if h : ∃ C, Lowest M x C then valG g h.choose else .orig

/-- The class of witnesses with reading `v`. -/
noncomputable def clsG (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k))
    (v : RdG n k) : Finset (Fin n) :=
  univ.filter fun x => readG M g x = v

/-- The unrooted coding proposes the split `A | Aᶜ` of the class `A`. -/
def PropUG (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k))
    (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ ∃ v, A = clsG M g v

/-- The rooted coding proposes the cluster `A`, a class of a non-original reading. -/
def PropRG (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k))
    (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ ∃ v, v ≠ .orig ∧ A = clsG M g v

/-- The unrooted coding proposes the split `τ | τᶜ`. -/
def PUG (τ : Finset (Fin n)) (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) :
    Prop :=
  PropUG M g τ ∨ PropUG M g τᶜ

/-- The rooted coding proposes the cluster `τ`. -/
def PRG (τ : Finset (Fin n)) (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) :
    Prop :=
  PropRG M g τ

lemma mem_clsG {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)} {v : RdG n k}
    {x : Fin n} : x ∈ clsG M g v ↔ readG M g x = v := by simp [clsG]

lemma valG_ne_orig (g : Finset (Fin n) → Option (Fin k)) (C : Finset (Fin n)) :
    valG g C ≠ .orig := by
  unfold valG; split <;> simp

lemma valG_eq_iff (g : Finset (Fin n) → Option (Fin k)) {C D : Finset (Fin n)} (hCD : C ≠ D) :
    valG g C = valG g D ↔ ∃ j, g C = some j ∧ g D = some j := by
  rcases hC : g C with _ | i <;> rcases hD : g D with _ | j <;> simp [valG, hC, hD, hCD, eq_comm]

lemma readG_of_lowest {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)}
    {x : Fin n} {C : Finset (Fin n)} (h : Lowest M x C) : readG M g x = valG g C := by
  have hex : ∃ C, Lowest M x C := ⟨C, h⟩
  unfold readG
  rw [dif_pos hex, lowest_unique hex.choose_spec h]

lemma readG_of_not {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)}
    {x : Fin n} (h : ¬ ∃ C, Lowest M x C) : readG M g x = .orig := by
  unfold readG; rw [dif_neg h]

lemma read_of_not {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {x : Fin n}
    (h : ¬ ∃ C, Lowest M x C) : read M att x = .orig := by
  unfold Mechanisms.read; rw [dif_neg h]

lemma read_eq_val {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {x : Fin n}
    {C : Finset (Fin n)} (h : Lowest M x C) : read M att x = val att C := by
  rw [read_of_lowest h]; rfl

/-! ### Two reading functions with the same pattern of values -/

/-- Two reading functions that both read the value of the lowest innovating edge, with values
never the original reading and equal on the same pairs of innovating edges, induce the same
partition into classes and the same original class. -/
lemma rel_of_lowest {V W : Type*} {M : Finset (Finset (Fin n))} {r : Fin n → V} {s : Fin n → W}
    {o : V} {o' : W} {fv : Finset (Fin n) → V} {fw : Finset (Fin n) → W}
    (hr1 : ∀ x C, Lowest M x C → r x = fv C) (hr0 : ∀ x, (¬ ∃ C, Lowest M x C) → r x = o)
    (hs1 : ∀ x C, Lowest M x C → s x = fw C) (hs0 : ∀ x, (¬ ∃ C, Lowest M x C) → s x = o')
    (hv : ∀ C, fv C ≠ o) (hw : ∀ C, fw C ≠ o')
    (hvw : ∀ C ∈ M, ∀ D ∈ M, (fv C = fv D ↔ fw C = fw D)) :
    (∀ x y, r x = r y ↔ s x = s y) ∧ (∀ x, r x = o ↔ s x = o') := by
  constructor
  · intro x y
    by_cases hx : ∃ C, Lowest M x C <;> by_cases hy : ∃ C, Lowest M y C
    · obtain ⟨C, hC⟩ := hx
      obtain ⟨D, hD⟩ := hy
      rw [hr1 x C hC, hr1 y D hD, hs1 x C hC, hs1 y D hD]
      exact hvw C hC.1 D hD.1
    · obtain ⟨C, hC⟩ := hx
      rw [hr1 x C hC, hr0 y hy, hs1 x C hC, hs0 y hy]
      exact ⟨fun h => absurd h (hv C), fun h => absurd h (hw C)⟩
    · obtain ⟨D, hD⟩ := hy
      rw [hr0 x hx, hr1 y D hD, hs0 x hx, hs1 y D hD]
      exact ⟨fun h => absurd h.symm (hv D), fun h => absurd h.symm (hw D)⟩
    · rw [hr0 x hx, hr0 y hy, hs0 x hx, hs0 y hy]
      simp
  · intro x
    by_cases hx : ∃ C, Lowest M x C
    · obtain ⟨C, hC⟩ := hx
      rw [hr1 x C hC, hs1 x C hC]
      exact ⟨fun h => absurd h (hv C), fun h => absurd h (hw C)⟩
    · rw [hr0 x hx, hs0 x hx]
      simp

/-- With at most two innovations, two distinct innovating edges are all of them. -/
lemma eq_pair_of_card_le_two {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2)
    {C D : Finset (Fin n)} (hC : C ∈ M) (hD : D ∈ M) (hCD : C ≠ D) : M = {C, D} := by
  symm
  apply eq_of_subset_of_card_le
  · intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact hC
    · rw [mem_singleton.mp hE]; exact hD
  · rw [card_pair hCD]; exact hM

/-! ### (1) The deterministic reduction to one attractive reading -/

/-- The one-reading assignment of an outcome: the innovations are attractive iff all of them carry
the same attractive reading (for two innovations: both carry `some j`, the same `j`). -/
noncomputable def attG (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) :
    Finset (Fin n) → Bool :=
  fun _ => decide (∃ j, ∀ C ∈ M, g C = some j)

/-- **Reduction, every outcome with at most two innovations.**  The partition of the witnesses
into classes, and which witnesses keep the original reading, are those of the one-reading model
with the two innovations both attractive iff they carry the same attractive reading (`attG`).  No
laminarity is needed. -/
theorem reduction {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2)
    (g : Finset (Fin n) → Option (Fin k)) :
    (∀ x y, readG M g x = readG M g y ↔ read M (attG M g) x = read M (attG M g) y) ∧
    (∀ x, readG M g x = .orig ↔ read M (attG M g) x = .orig) := by
  refine rel_of_lowest (fun x C h => readG_of_lowest h) (fun x h => readG_of_not h)
    (fun x C h => read_eq_val h) (fun x h => read_of_not h) (valG_ne_orig g) (val_ne_orig _) ?_
  intro C hC D hD
  by_cases hCD : C = D
  · subst hCD; simp
  · rw [valG_eq_iff g hCD, val_eq_iff _ hCD]
    have hMe := eq_pair_of_card_le_two hM hC hD hCD
    simp only [attG, decide_eq_true_eq, and_self, hMe, mem_insert, mem_singleton,
      forall_eq_or_imp, forall_eq]

lemma propUG_iff {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)}
    {att : Finset (Fin n) → Bool}
    (h1 : ∀ x y, readG M g x = readG M g y ↔ read M att x = read M att y) (A : Finset (Fin n)) :
    PropUG M g A ↔ PropU M att A := by
  constructor
  · rintro ⟨⟨y, hy⟩, v, rfl⟩
    have hyv := mem_clsG.mp hy
    refine ⟨⟨y, hy⟩, read M att y, ?_⟩
    ext x
    rw [mem_clsG, mem_cls, ← hyv]
    exact h1 x y
  · rintro ⟨⟨y, hy⟩, v, rfl⟩
    have hyv := mem_cls.mp hy
    refine ⟨⟨y, hy⟩, readG M g y, ?_⟩
    ext x
    rw [mem_clsG, mem_cls, ← hyv]
    exact (h1 x y).symm

lemma propRG_iff {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)}
    {att : Finset (Fin n) → Bool}
    (h1 : ∀ x y, readG M g x = readG M g y ↔ read M att x = read M att y)
    (h2 : ∀ x, readG M g x = .orig ↔ read M att x = .orig) (A : Finset (Fin n)) :
    PropRG M g A ↔ PropR M att A := by
  constructor
  · rintro ⟨⟨y, hy⟩, v, hv, rfl⟩
    have hyv := mem_clsG.mp hy
    refine ⟨⟨y, hy⟩, read M att y, fun h => hv (hyv ▸ (h2 y).mpr h), ?_⟩
    ext x
    rw [mem_clsG, mem_cls, ← hyv]
    exact h1 x y
  · rintro ⟨⟨y, hy⟩, v, hv, rfl⟩
    have hyv := mem_cls.mp hy
    refine ⟨⟨y, hy⟩, readG M g y, fun h => hv (hyv ▸ (h2 y).mp h), ?_⟩
    ext x
    rw [mem_clsG, mem_cls, ← hyv]
    exact (h1 x y).symm

/-- **Reduction, unrooted coding.**  With at most two innovations, the unrooted coding proposes
`τ | τᶜ` iff it does in the one-reading model with readings `attG M g`. -/
theorem reduction_PU (τ : Finset (Fin n)) {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2)
    (g : Finset (Fin n) → Option (Fin k)) : PUG τ M g ↔ PU τ M (attG M g) := by
  have h1 := (reduction hM g).1
  exact or_congr (propUG_iff h1 τ) (propUG_iff h1 τᶜ)

/-- **Reduction, rooted coding.**  With at most two innovations, the rooted coding proposes the
cluster `τ` iff it does in the one-reading model with readings `attG M g`. -/
theorem reduction_PR (τ : Finset (Fin n)) {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2)
    (g : Finset (Fin n) → Option (Fin k)) : PRG τ M g ↔ PR τ M (attG M g) :=
  propRG_iff (reduction hM g).1 (reduction hM g).2 τ

/-- In the one-reading model, with at most two innovations, a proposal determined by the classes
depends on the readings only through whether all innovations are attractive. -/
lemma classDet_const {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (hP : ClassDet P) {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2)
    (att : Finset (Fin n) → Bool) :
    P M att ↔ P M (fun _ => decide (∀ C ∈ M, att C = true)) := by
  have hvw : ∀ C ∈ M, ∀ D ∈ M, (val att C = val att D ↔
      val (fun _ => decide (∀ C ∈ M, att C = true)) C =
        val (fun _ => decide (∀ C ∈ M, att C = true)) D) := by
    intro C hC D hD
    by_cases hCD : C = D
    · subst hCD; simp
    · rw [val_eq_iff att hCD, val_eq_iff _ hCD]
      have hMe := eq_pair_of_card_le_two hM hC hD hCD
      simp only [decide_eq_true_eq, and_self, hMe, mem_insert, mem_singleton,
        forall_eq_or_imp, forall_eq]
  have r := rel_of_lowest (fun x C h => read_eq_val (att := att) h) (fun x h => read_of_not h)
    (fun x C h => read_eq_val h) (fun x h => read_of_not h) (val_ne_orig att) (val_ne_orig _) hvw
  exact hP M _ _ r.1 r.2

/-- In the one-reading model, with at most one innovation, a proposal determined by the classes
does not depend on the readings. -/
lemma classDet_le_one {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (hP : ClassDet P) {M : Finset (Finset (Fin n))} (hM : M.card ≤ 1)
    (att att' : Finset (Fin n) → Bool) : P M att ↔ P M att' := by
  have hvw : ∀ C ∈ M, ∀ D ∈ M, (val att C = val att D ↔ val att' C = val att' D) := by
    intro C hC D hD
    rw [card_le_one.mp hM C hC D hD]; simp
  have r := rel_of_lowest (fun x C h => read_eq_val (att := att) h) (fun x h => read_of_not h)
    (fun x C h => read_eq_val (att := att') h) (fun x h => read_of_not h) (val_ne_orig att)
    (val_ne_orig att') hvw
  exact hP M _ _ r.1 r.2

/-! ### The probability model -/

/-- The probability that an innovation takes the reading `o`: `a j` for the attractive reading
`j`, `1 - ∑ a` for its own reading. -/
noncomputable def q (a : Fin k → ℝ) : Option (Fin k) → ℝ
  | none => 1 - ∑ j, a j
  | some j => a j

/-- The factor of edge `C` in the probability of an outcome: `π_C q(o)` if it innovates, and the
indicator of `o = none` if it does not (the assignment off `M` is fixed). -/
noncomputable def fac (π : Finset (Fin n) → ℝ) (a : Fin k → ℝ) (M : Finset (Finset (Fin n)))
    (C : Finset (Fin n)) (o : Option (Fin k)) : ℝ :=
  if C ∈ M then π C * q a o else if o = none then 1 else 0

/-- The probability of the outcome: innovations on `M`, readings `g`. -/
noncomputable def wtG (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (a : Fin k → ℝ)
    (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) : ℝ :=
  (∏ C, fac π a M C (g C)) * ∏ e ∈ K \ M, (1 - π e)

/-- The expected value of the indicator of `P`: the probability that a unit's outcome satisfies
`P`. -/
noncomputable def exG (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (a : Fin k → ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop) : ℝ :=
  ∑ M ∈ K.powerset, ∑ g : Finset (Fin n) → Option (Fin k),
    wtG K π a M g * (if P M g then 1 else 0)

/-- `α = √A`, `A = ∑ a²`, the attraction rate of the matching one-reading model. -/
noncomputable def alpha (a : Fin k → ℝ) : ℝ := Real.sqrt (∑ j, a j ^ 2)

lemma alpha_sq (a : Fin k → ℝ) : alpha a ^ 2 = ∑ j, a j ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg (a j))

lemma alpha_nonneg (a : Fin k → ℝ) : 0 ≤ alpha a := Real.sqrt_nonneg _

/-- `∑ a² ≤ ∑ a ≤ 1`. -/
lemma sumsq_le {a : Fin k → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j ≤ 1) :
    ∑ j, a j ^ 2 ≤ ∑ j, a j ∧ ∑ j, a j ≤ 1 := by
  refine ⟨sum_le_sum fun j _ => ?_, ha1⟩
  have h1 : a j ≤ 1 := (single_le_sum (fun i _ => ha0 i) (mem_univ j)).trans ha1
  nlinarith [ha0 j]

lemma alpha_le_one {a : Fin k → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j ≤ 1) : alpha a ≤ 1 := by
  unfold alpha
  rw [Real.sqrt_le_one]
  exact (sumsq_le ha0 ha1).1.trans ha1

lemma sum_q (a : Fin k → ℝ) : ∑ o, q a o = 1 := by
  rw [Fintype.sum_option]; simp [q]

lemma sum_fac (π : Finset (Fin n) → ℝ) (a : Fin k → ℝ) (M : Finset (Finset (Fin n)))
    (C : Finset (Fin n)) : ∑ o, fac π a M C o = if C ∈ M then π C else 1 := by
  unfold fac
  by_cases hC : C ∈ M
  · simp only [hC, if_true]; rw [← mul_sum, sum_q, mul_one]
  · simp [hC]

section sums

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {a : Fin k → ℝ}

/-- The sum over readings factorises over the edges. -/
lemma sum_wtG_mul (M : Finset (Finset (Fin n))) (d : Finset (Fin n) → Option (Fin k) → ℝ) :
    ∑ g : Finset (Fin n) → Option (Fin k), wtG K π a M g * ∏ C, d C (g C) =
      (∏ C, ∑ o, fac π a M C o * d C o) * ∏ e ∈ K \ M, (1 - π e) := by
  rw [Fintype.prod_sum (fun C o => fac π a M C o * d C o), sum_mul]
  refine sum_congr rfl fun g _ => ?_
  unfold wtG
  rw [prod_mul_distrib]
  ring

/-- Summing over the readings: innovations exactly on `M` have probability
`∏_M π · ∏_{K \ M} (1 - π)`, as in the one-reading model. -/
lemma sum_wtG (M : Finset (Finset (Fin n))) :
    ∑ g : Finset (Fin n) → Option (Fin k), wtG K π a M g =
      (∏ e ∈ M, π e) * ∏ e ∈ K \ M, (1 - π e) := by
  have h := sum_wtG_mul (K := K) (π := π) (a := a) M (fun _ _ => 1)
  simp only [prod_const_one, mul_one] at h
  rw [h, prod_congr rfl fun C _ => sum_fac π a M C, Fintype.prod_ite_mem]

/-- The indicator that every innovation of `M` carries the attractive reading `j`. -/
noncomputable def dj (j : Fin k) (M : Finset (Finset (Fin n))) (C : Finset (Fin n))
    (o : Option (Fin k)) : ℝ :=
  if C ∈ M then (if o = some j then 1 else 0) else 1

lemma prod_dj (j : Fin k) (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) :
    ∏ C, dj j M C (g C) = if ∀ C ∈ M, g C = some j then 1 else 0 := by
  simp only [dj]
  rw [Fintype.prod_ite_mem, prod_boole]
  congr

lemma ind_same {M : Finset (Finset (Fin n))} (hM : M.Nonempty)
    (g : Finset (Fin n) → Option (Fin k)) :
    (if ∃ j, ∀ C ∈ M, g C = some j then (1 : ℝ) else 0) = ∑ j, ∏ C, dj j M C (g C) := by
  simp only [prod_dj]
  by_cases h : ∃ j, ∀ C ∈ M, g C = some j
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩, sum_eq_single j]
    · rw [if_pos hj]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      obtain ⟨C, hC⟩ := hM
      exact hb (Option.some_injective _ ((hb' C hC).symm.trans (hj C hC)))
    · simp
  · rw [if_neg h]
    symm
    exact sum_eq_zero fun j _ => if_neg fun hj => h ⟨j, hj⟩

lemma sum_fac_dj (j : Fin k) (M : Finset (Finset (Fin n))) (C : Finset (Fin n)) :
    ∑ o, fac π a M C o * dj j M C o = if C ∈ M then π C * a j else 1 := by
  unfold fac dj
  by_cases hC : C ∈ M
  · simp [hC, q]
  · simp [hC]

/-- The probability that the innovations on `M ≠ ∅` all carry the same attractive reading:
`∏_M π · ∑_j a_j^{|M|} · ∏_{K \ M} (1 - π)`. -/
lemma sum_wtG_same {M : Finset (Finset (Fin n))} (hM : M.Nonempty) :
    ∑ g : Finset (Fin n) → Option (Fin k),
        wtG K π a M g * (if ∃ j, ∀ C ∈ M, g C = some j then 1 else 0) =
      (∏ e ∈ M, π e) * (∑ j, a j ^ M.card) * ∏ e ∈ K \ M, (1 - π e) := by
  simp only [ind_same hM, mul_sum]
  rw [sum_comm]
  rw [sum_congr rfl fun j _ => sum_wtG_mul (K := K) (π := π) (a := a) M (dj j M)]
  simp only [sum_fac_dj, Fintype.prod_ite_mem, prod_mul_distrib, prod_const]
  rw [← sum_mul, ← mul_sum]

end sums

/-! ### (2) The part with at most two innovations -/

section lambda

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {a : Fin k → ℝ}

/-- The binary outcome with all of `M` attractive has probability `α^{|M|} ∏_M π ∏_{K\M}(1-π)`. -/
lemma wt_self (α : ℝ) (M : Finset (Finset (Fin n))) :
    wt K π α M M = (∏ e ∈ M, π e) * α ^ M.card * ∏ e ∈ K \ M, (1 - π e) := by
  unfold wt
  rw [sdiff_self, bot_eq_empty, prod_empty, mul_one, prod_mul_distrib, prod_const]

/-- One innovation set `M` with at most two innovations contributes the same expected support in
both models, for a proposal determined by the classes, when `α² = ∑ a²`. -/
lemma inner_eq {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop} (hP : ClassDet P)
    {α : ℝ} (hα : α ^ 2 = ∑ j, a j ^ 2) {M : Finset (Finset (Fin n))} (hM : M.card ≤ 2) :
    ∑ g : Finset (Fin n) → Option (Fin k), wtG K π a M g * (if P M (attG M g) then 1 else 0) =
      ∑ A ∈ M.powerset, wt K π α M A * (if P M (attOf A) then 1 else 0) := by
  set xv : ℝ := if P M (fun _ => true) then 1 else 0 with hxv
  set yv : ℝ := if P M (fun _ => false) then 1 else 0 with hyv
  set B : ℝ := (∏ e ∈ M, π e) * ∏ e ∈ K \ M, (1 - π e) with hB
  have hG : ∀ g : Finset (Fin n) → Option (Fin k), (if P M (attG M g) then (1 : ℝ) else 0) =
      yv + (xv - yv) * (if ∃ j, ∀ C ∈ M, g C = some j then 1 else 0) := by
    intro g
    by_cases h : ∃ j, ∀ C ∈ M, g C = some j
    · have : attG M g = fun _ => true := by funext C; simp [attG, h]
      rw [this, if_pos h]; ring
    · have : attG M g = fun _ => false := by funext C; simp [attG, h]
      rw [this, if_neg h]; ring
  have hBin : ∀ A ∈ M.powerset, (if P M (attOf A) then (1 : ℝ) else 0) =
      yv + (xv - yv) * (if A = M then 1 else 0) := by
    intro A hA
    have hc := classDet_const hP hM (attOf A)
    have hiff : (∀ C ∈ M, attOf A C = true) ↔ A = M := by
      simp only [attOf, decide_eq_true_eq]
      exact ⟨fun h => subset_antisymm (mem_powerset.mp hA) h, fun h => h ▸ fun C hC => hC⟩
    by_cases h : A = M
    · have e : (fun _ : Finset (Fin n) => decide (∀ C ∈ M, attOf A C = true)) = fun _ => true := by
        funext C; simp only [decide_eq_true_eq]; exact hiff.mpr h
      rw [if_congr hc rfl rfl, e, if_pos h]; ring
    · have e : (fun _ : Finset (Fin n) => decide (∀ C ∈ M, attOf A C = true)) =
          fun _ => false := by
        funext C; simp only [decide_eq_false_iff_not]; exact fun h' => h (hiff.mp h')
      rw [if_congr hc rfl rfl, e, if_neg h]; ring
  have lhs : ∑ g : Finset (Fin n) → Option (Fin k),
      wtG K π a M g * (if P M (attG M g) then 1 else 0) =
      yv * B + (xv - yv) * ∑ g : Finset (Fin n) → Option (Fin k),
        wtG K π a M g * (if ∃ j, ∀ C ∈ M, g C = some j then 1 else 0) := by
    rw [hB, ← sum_wtG (K := K) (π := π) (a := a) M, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    rw [hG g]; ring
  have rhs : ∑ A ∈ M.powerset, wt K π α M A * (if P M (attOf A) then 1 else 0) =
      yv * B + (xv - yv) * wt K π α M M := by
    rw [hB, ← sum_wt_A (K := K) (π := π) (α := α) M, sum_congr rfl fun A hA => by rw [hBin A hA]]
    simp only [mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' M.powerset M, if_pos (mem_powerset_self M), ← sum_mul]
    ring
  rw [lhs, rhs]
  by_cases h1 : M.card ≤ 1
  · have : xv = yv := by rw [hxv, hyv, if_congr (classDet_le_one hP h1 _ _) rfl rfl]
    rw [this]; ring
  · have h2 : M.card = 2 := by omega
    have hne : M.Nonempty := card_pos.mp (by omega)
    rw [sum_wtG_same hne, wt_self, h2, hα]

lemma exG_congr {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {a : Fin k → ℝ}
    {P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop}
    (h : ∀ M g, P M g ↔ Q M g) : exG K π a P = exG K π a Q := by
  unfold exG
  exact sum_congr rfl fun M _ => sum_congr rfl fun g _ => by rw [if_congr (h M g) rfl rfl]

/-- **The part with at most two innovations, every proposal determined by the classes.**  For a
proposal `P` of the one-reading model determined by the classes (`ClassDet`), its lift
`P M (attG M g)` has the same second-order support in the model with `k` attractive readings as
`P` in the one-reading model with `α² = ∑ a²`.  (No laminarity or positivity is needed.) -/
theorem lambdaG_eq {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (hP : ClassDet P) {α : ℝ} (hα : α ^ 2 = ∑ j, a j ^ 2) :
    exG K π a (fun M g => P M (attG M g) ∧ M.card ≤ 2) =
      ex K π α (fun M att => P M att ∧ M.card ≤ 2) := by
  unfold exG ex
  refine sum_congr rfl fun M _ => ?_
  by_cases hM : M.card ≤ 2
  · simp only [hM, and_true]
    exact inner_eq hP hα hM
  · simp [hM]

/-- **Theorem 8.5 for `k` attractive readings, unrooted coding, at most two innovations.**  The
second-order support of the split `τ` equals that of the one-reading model with `α = √(∑ a²)`. -/
theorem lambdaG_PU (τ : Finset (Fin n)) :
    exG K π a (fun M g => PUG τ M g ∧ M.card ≤ 2) =
      ex K π (alpha a) (fun M att => PU τ M att ∧ M.card ≤ 2) := by
  rw [← lambdaG_eq (classDet_PU τ) (alpha_sq a)]
  exact exG_congr fun M g => ⟨fun h => ⟨(reduction_PU τ h.2 g).mp h.1, h.2⟩,
    fun h => ⟨(reduction_PU τ h.2 g).mpr h.1, h.2⟩⟩

/-- **Theorem 8.5 for `k` attractive readings, rooted coding, at most two innovations.**  The
second-order support of the cluster `τ` equals that of the one-reading model with
`α = √(∑ a²)`. -/
theorem lambdaG_PR (τ : Finset (Fin n)) :
    exG K π a (fun M g => PRG τ M g ∧ M.card ≤ 2) =
      ex K π (alpha a) (fun M att => PR τ M att ∧ M.card ≤ 2) := by
  rw [← lambdaG_eq (classDet_PR τ) (alpha_sq a)]
  exact exG_congr fun M g => ⟨fun h => ⟨(reduction_PR τ h.2 g).mp h.1, h.2⟩,
    fun h => ⟨(reduction_PR τ h.2 g).mpr h.1, h.2⟩⟩

/-- **`Λ_τ` in closed form for `k` attractive readings.**  For a laminar `K` and a proposal
determined by the classes, the second-order support is the closed form of
`Attraction.lambda_eq` with `α²` replaced by `A = ∑ a²` (the pair weight `omega` at `√A`). -/
theorem lambdaG_closed (hK : Laminar K)
    {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop} (hP : ClassDet P) :
    exG K π a (fun M g => P M (attG M g) ∧ M.card ≤ 2) =
      (if P ∅ (attOf ∅) then 1 else 0) * ∏ g ∈ K, (1 - π g) +
      ∑ e ∈ K, π e * (∏ g ∈ K.erase e, (1 - π g)) * (if P {e} (attOf ∅) then 1 else 0) +
      ∑ S ∈ K.powersetCard 2, (∏ e ∈ S, π e) *
        ((∑ j, a j ^ 2) * (if P S (attOf S) then 1 else 0) +
          (1 - ∑ j, a j ^ 2) * (if P S (attOf ∅) then 1 else 0)) * ∏ g ∈ K \ S, (1 - π g) := by
  rw [lambdaG_eq hP (alpha_sq a), lambda_eq hK π (alpha a) P hP]
  simp only [omega, alpha_sq]

end lambda

/-! ### (3) The sandwich and the transfer -/

section rates

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {a : Fin k → ℝ}

/-- **A predicate of the innovation set alone** has the same probability in both models, for any
`α`. -/
theorem exG_Monly (α : ℝ) (R : Finset (Finset (Fin n)) → Prop) :
    exG K π a (fun M _ => R M) = ex K π α (fun M _ => R M) := by
  unfold exG ex
  refine sum_congr rfl fun M _ => ?_
  rw [← sum_mul, ← sum_mul, sum_wtG, sum_wt_A]

/-- The probability of three or more innovations is `P3 K π α`, whatever `α`. -/
theorem P3G_eq (α : ℝ) : exG K π a (fun M _ => 3 ≤ M.card) = P3 K π α :=
  exG_Monly α _

variable (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j ≤ 1)

include hπ0 hπ1 ha0 ha1 in
lemma wtG_nonneg (M : Finset (Finset (Fin n))) (g : Finset (Fin n) → Option (Fin k)) :
    0 ≤ wtG K π a M g := by
  unfold wtG
  refine mul_nonneg (prod_nonneg fun C _ => ?_) (prod_nonneg fun e _ => by linarith [hπ1 e])
  unfold fac
  split_ifs
  · refine mul_nonneg (hπ0 C) ?_
    cases g C with
    | none => simp only [q]; linarith
    | some j => exact ha0 j
  · norm_num
  · norm_num

include hπ0 hπ1 ha0 ha1 in
lemma exG_mono {P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop}
    (h : ∀ M g, P M g → Q M g) : exG K π a P ≤ exG K π a Q := by
  unfold exG
  refine sum_le_sum fun M _ => sum_le_sum fun g _ => ?_
  have := wtG_nonneg hπ0 hπ1 ha0 ha1 (K := K) M g
  by_cases hP : P M g
  · simp [hP, h _ _ hP]
  · by_cases hQ : Q M g <;> simp [hP, hQ, this]

lemma exG_add (P Q : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop) :
    exG K π a P = exG K π a (fun M g => P M g ∧ Q M g) +
      exG K π a (fun M g => P M g ∧ ¬ Q M g) := by
  unfold exG
  rw [← sum_add_distrib]
  refine sum_congr rfl fun M _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun g _ => ?_
  by_cases hP : P M g <;> by_cases hQ : Q M g <;> simp [hP, hQ]

include hπ0 hπ1 ha0 ha1 in
/-- **Theorem 8.5, the sandwich, for `k` attractive readings.**  `m_τ = Λ_τ + R_τ`, with `Λ_τ`
the part of at most two innovations and `0 ≤ R_τ ≤ Pr(|M| ≥ 3) = P3 K π α` (any `α`). -/
theorem exG_split (α : ℝ)
    (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop) :
    exG K π a P = exG K π a (fun M g => P M g ∧ M.card ≤ 2) +
      exG K π a (fun M g => P M g ∧ ¬ M.card ≤ 2) ∧
    0 ≤ exG K π a (fun M g => P M g ∧ ¬ M.card ≤ 2) ∧
    exG K π a (fun M g => P M g ∧ ¬ M.card ≤ 2) ≤ P3 K π α := by
  refine ⟨exG_add P _, ?_, ?_⟩
  · unfold exG
    exact sum_nonneg fun M _ => sum_nonneg fun g _ =>
      mul_nonneg (wtG_nonneg hπ0 hπ1 ha0 ha1 M g) (by split_ifs <;> norm_num)
  · rw [← P3G_eq (a := a) α]
    exact exG_mono hπ0 hπ1 ha0 ha1 fun M g h => by omega

include hπ0 hπ1 ha0 ha1 in
/-- Transfer, for any proposal whose second-order parts agree. -/
lemma transfer_of_lambda
    {PG : Finset (Finset (Fin n)) → (Finset (Fin n) → Option (Fin k)) → Prop}
    {P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop}
    (hΛ : exG K π a (fun M g => PG M g ∧ M.card ≤ 2) =
      ex K π (alpha a) (fun M att => P M att ∧ M.card ≤ 2)) :
    |exG K π a PG - ex K π (alpha a) P| ≤ P3 K π (alpha a) := by
  obtain ⟨hG, hG0, hG1⟩ := exG_split hπ0 hπ1 ha0 ha1 (alpha a) PG
  obtain ⟨hB, hB0, hB1⟩ := ex_split hπ0 hπ1 (alpha_nonneg a) (alpha_le_one ha0 ha1) (K := K) P
  rw [hG, hB, hΛ, abs_sub_le_iff]
  constructor <;> linarith

include hπ0 hπ1 ha0 ha1 in
/-- **Transfer, unrooted coding.**  `|m^G_τ - m_τ(α)| ≤ Pr(|M| ≥ 3)` with `α = √(∑ a²)`. -/
theorem transfer_PU (τ : Finset (Fin n)) :
    |exG K π a (PUG τ) - ex K π (alpha a) (PU τ)| ≤ P3 K π (alpha a) :=
  transfer_of_lambda hπ0 hπ1 ha0 ha1 (lambdaG_PU τ)

include hπ0 hπ1 ha0 ha1 in
/-- **Transfer, rooted coding.**  `|m^G_τ - m_τ(α)| ≤ Pr(|M| ≥ 3)` with `α = √(∑ a²)`. -/
theorem transfer_PR (τ : Finset (Fin n)) :
    |exG K π a (PRG τ) - ex K π (alpha a) (PR τ)| ≤ P3 K π (alpha a) :=
  transfer_of_lambda hπ0 hπ1 ha0 ha1 (lambdaG_PR τ)

include hπ0 hπ1 ha0 ha1 in
/-- **Transfer at order `(∑ π)³`.**  In both codings the expected support with `k` attractive
readings differs from the one-reading expected support at `α = √(∑ a²)` by at most
`∑_{|S|=3} ∏_S π ≤ (∑ π)³ / 6`. -/
theorem transfer_cubic (τ : Finset (Fin n)) :
    |exG K π a (PUG τ) - ex K π (alpha a) (PU τ)| ≤ (∑ e ∈ K, π e) ^ 3 / 6 ∧
    |exG K π a (PRG τ) - ex K π (alpha a) (PR τ)| ≤ (∑ e ∈ K, π e) ^ 3 / 6 := by
  obtain ⟨h1, h2⟩ := P3_le (K := K) (α := alpha a) hπ0 hπ1
  exact ⟨(transfer_PU hπ0 hπ1 ha0 ha1 τ).trans (h1.trans h2),
    (transfer_PR hπ0 hπ1 ha0 ha1 τ).trans (h1.trans h2)⟩

end rates

/-! ### (4) The comparison of the codings at every order -/

/-- A cluster proposed in the rooted coding is a class of a reading, so its split is proposed in
the unrooted coding. -/
lemma propRG_propUG {M : Finset (Finset (Fin n))} {g : Finset (Fin n) → Option (Fin k)}
    {A : Finset (Fin n)} (h : PropRG M g A) : PropUG M g A :=
  ⟨h.1, h.2.choose, h.2.choose_spec.2⟩

/-- Outcome by outcome: the rooted coding proposes `C` or `Cᶜ` only when the unrooted coding
proposes `C | Cᶜ`. -/
lemma PRG_PUG (C : Finset (Fin n)) (M : Finset (Finset (Fin n)))
    (g : Finset (Fin n) → Option (Fin k)) :
    (PRG C M g → PUG C M g) ∧ (PRG Cᶜ M g → PUG C M g) :=
  ⟨fun h => Or.inl (propRG_propUG h), fun h => Or.inr (propRG_propUG h)⟩

/-- **Comparison of the codings, outcome by outcome, with the report's size conditions.**  If the
rooted coding proposes the cluster `C` and `C` is a non-trivial split side (two witnesses on each
side), the unrooted coding proposes the non-trivial split `C | Cᶜ`. -/
theorem PRG_PUG_nt {C : Finset (Fin n)} (hC : SplitNT C) {M : Finset (Finset (Fin n))}
    {g : Finset (Fin n) → Option (Fin k)} (h : PRG C M g) : PUG C M g ∧ SplitNT C :=
  ⟨(PRG_PUG C M g).1 h, hC⟩

/-- **Comparison of the codings at every order, `k` attractive readings.**  For every split
`τ = C | Cᶜ`, the exact expected support of each cluster `C`, `Cᶜ` in the rooted coding is at most
that of `τ` in the unrooted coding.  (Lean needs no size condition on `C`.) -/
theorem dominanceG {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {a : Fin k → ℝ}
    (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j ≤ 1)
    (C : Finset (Fin n)) :
    exG K π a (PRG C) ≤ exG K π a (PUG C) ∧ exG K π a (PRG Cᶜ) ≤ exG K π a (PUG C) :=
  ⟨exG_mono hπ0 hπ1 ha0 ha1 fun M g h => (PRG_PUG C M g).1 h,
    exG_mono hπ0 hπ1 ha0 ha1 fun M g h => (PRG_PUG C M g).2 h⟩

end Stemma.MultiAttraction
