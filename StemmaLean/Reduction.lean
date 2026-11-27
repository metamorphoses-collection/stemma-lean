/-
The reduction of Corollary 4.2 of the technical report (`cor:nphard`), in the operation-count model
used for Theorem 8.4.

The corollary says that MWIS restricted to split-conflict graphs is NP-hard when `n` is part of the
input, by reducing MWIS on general graphs (NP-hard, Karp 1972) through the gadget of Theorem 3.1.
Mathlib has no polynomial time or NP, so the formalisation proves everything about the reduction
except the complexity classes themselves:

* `reduction_mwis`: the reduction preserves weights.  With the weight `c v` put on the split `σ_v`
  of the gadget (and `0` on every other split), the independent sets of `H` and the compatible
  sets of splits correspond, with equal weights; a maximum-weight compatible set decodes to a
  maximum-weight independent set (`decode_optimal`).
* `instance_size`: the instance has `4|E| + 2|V| + 2` witnesses and `|V|` candidate splits.
* `encode_cost_le`: building it takes `|V| (4|E| + 2|V| + 2) ≤ 4 (|V| + |E| + 1)²` membership tests,
  and decoding `|V|`.  These costs are an abstract operation-count interface: `encodeCost` and
  `decodeCost` are stipulated (one unit per membership test), not derived from a machine model;
  the theorem bounds the stipulated count.  Machine-level polynomial time is `NPHard.lean`.
* `transfer`: any solver of maximum-weight compatible sets, with a cost `p(N, m)` on `N` witnesses
  and `m` candidates, yields a solver of MWIS on every graph whose cost is
  `p(4|E| + 2|V| + 2, |V|)` plus a quadratic; a polynomial `p` gives a polynomial cost
  (`transfer_poly`).  This is the content of "polynomial reduction".
* `every_graph_split_conflict`, `class_contains_all`: every finite graph is a split-conflict graph,
  so a class of graphs containing every split-conflict graph contains every graph (the second
  sentence of the corollary, before invoking `P ≠ NP`).

NP-hardness with Turing-machine polynomial time, from Karp's theorem as formalised in
`cslib-community/cslib-frontier`, is `NPHard.lean` (`CompatibleSplits_npHard`).
-/
import Mathlib
import StemmaLean.Universal

open Finset
open scoped Classical

namespace Stemma.Reduction

open Stemma.Universal

section graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The number of witnesses of the gadget. -/
noncomputable def N : ℕ := 4 * H.edgeFinset.card + 2 * Fintype.card V + 2

/-- The splits of the gadget (Theorem 4.1). -/
noncomputable def σ : V → Finset (Fin (N H)) := (universality H).choose

lemma σ_spec :
    (∀ v, 2 ≤ (σ H v).card ∧ 2 ≤ (σ H v)ᶜ.card) ∧
    (∀ u v, u ≠ v → σ H u ≠ σ H v ∧ σ H u ≠ (σ H v)ᶜ) ∧
    (∀ u v, u ≠ v → (¬ Compat (σ H u) (σ H v) ↔ H.Adj u v)) :=
  (universality H).choose_spec

lemma σ_inj : Function.Injective (σ H) := fun u v h => by
  by_contra huv; exact ((σ_spec H).2.1 u v huv).1 h

/-- The weights of the instance: `c v` on `σ_v`, `0` on every other split. -/
noncomputable def wt (c : V → ℕ) (A : Finset (Fin (N H))) : ℕ :=
  ∑ v ∈ univ.filter (fun v => σ H v = A), c v

/-- Decoding a set of splits: the vertices whose split it contains. -/
noncomputable def decode (S : Finset (Finset (Fin (N H)))) : Finset V :=
  univ.filter fun v => σ H v ∈ S

lemma weight_eq (c : V → ℕ) (S : Finset (Finset (Fin (N H)))) :
    weight (wt H c) S = ∑ v ∈ decode H S, c v := by
  unfold weight wt decode
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun v => σ H v ∈ S) (t := S) (g := σ H)
    (fun v hv => (mem_filter.mp hv).2)]
  refine sum_congr rfl fun A hA => ?_
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact ⟨h ▸ hA, h⟩
  · exact fun h => h.2

/-- A maximum-weight independent set. -/
def IsMWIS (c : V → ℕ) (I : Finset V) : Prop :=
  H.IsIndepSet (I : Set V) ∧ ∀ J : Finset V, H.IsIndepSet (J : Set V) →
    ∑ v ∈ J, c v ≤ ∑ v ∈ I, c v

/-- **Corollary 4.2, the reduction preserves weights.**  Independent sets of `H` give compatible
sets of splits of the same weight, and every compatible set of splits decodes to an independent
set of the same weight. -/
theorem reduction_mwis (c : V → ℕ) :
    (∀ I : Finset V, H.IsIndepSet (I : Set V) →
      PairwiseCompat (I.image (σ H)) ∧ weight (wt H c) (I.image (σ H)) = ∑ v ∈ I, c v) ∧
    (∀ S, PairwiseCompat S →
      H.IsIndepSet (decode H S : Set V) ∧ ∑ v ∈ decode H S, c v = weight (wt H c) S) := by
  obtain ⟨-, hdist, hconf⟩ := σ_spec H
  refine ⟨fun I hI => ⟨?_, ?_⟩, fun S hS => ⟨?_, (weight_eq H c S).symm⟩⟩
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    have huv : u ≠ v := fun h => hab (h ▸ rfl)
    by_contra h
    exact hI hu hv huv ((hconf u v huv).mp h)
  · rw [weight_eq]
    congr 1
    ext v
    simp only [decode, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨u, hu, h⟩; exact σ_inj H h ▸ hu
    · intro hv; exact ⟨v, hv, rfl⟩
  · intro u hu v hv huv hadj
    simp only [decode, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
    have hne : σ H u ≠ σ H v := fun h => huv (σ_inj H h)
    exact (hconf u v huv).mpr hadj (hS _ hu _ hv hne)

/-- **Corollary 4.2, decoding.**  A maximum-weight compatible set of splits for the weights of the
instance decodes to a maximum-weight independent set of `H`. -/
theorem decode_optimal (c : V → ℕ) {S : Finset (Finset (Fin (N H)))}
    (hS : IsOptimal (wt H c) S) : IsMWIS H c (decode H S) := by
  obtain ⟨h1, h2⟩ := reduction_mwis H c
  refine ⟨(h2 S hS.1).1, fun J hJ => ?_⟩
  obtain ⟨hc, hw⟩ := h1 J hJ
  rw [(h2 S hS.1).2, ← hw]
  exact hS.2 _ hc

/-- **Corollary 4.2, the size of the instance.**  `4|E| + 2|V| + 2` witnesses, and `|V|` candidate
splits carrying weight. -/
theorem instance_size (c : V → ℕ) :
    N H = 4 * H.edgeFinset.card + 2 * Fintype.card V + 2 ∧
    (univ.image (σ H)).card = Fintype.card V ∧
    ∀ A, A ∉ univ.image (σ H) → wt H c A = 0 := by
  refine ⟨rfl, ?_, fun A hA => ?_⟩
  · rw [card_image_of_injective _ (σ_inj H), card_univ]
  · unfold wt
    refine sum_eq_zero fun v hv => ?_
    exact absurd ((mem_filter.mp hv).2 ▸ mem_image_of_mem _ (mem_univ v)) hA

/-- The cost of building the instance, in an abstract operation-count interface: stipulated as one
unit per vertex and witness (a membership test), not derived from a machine model.  Turing-machine
polynomial time is proved separately (`NPHard.toSplits_polyTime`). -/
noncomputable def encodeCost : ℕ := Fintype.card V * N H

/-- The cost of decoding, in the same abstract interface: stipulated as one unit per vertex. -/
def decodeCost : ℕ := Fintype.card V

/-- **Corollary 4.2, the cost of the reduction.**  Building the instance takes
`|V| (4|E| + 2|V| + 2) ≤ 4 (|V| + |E| + 1)²` operations. -/
theorem encode_cost_le :
    encodeCost H ≤ 4 * (Fintype.card V + H.edgeFinset.card + 1) ^ 2 := by
  unfold encodeCost N
  nlinarith [Nat.zero_le (Fintype.card V), Nat.zero_le H.edgeFinset.card]

end graph

/-! ### Transfer of a solver -/

/-- A solver of the maximum-weight compatible set problem in the operation-count model: on `N`
witnesses and weights `w`, it returns an optimal compatible set, at a cost bounded by `cost N m`
when at most `m` splits carry weight. -/
structure Solver where
  solve : (N : ℕ) → (Finset (Fin N) → ℕ) → Finset (Finset (Fin N))
  correct : ∀ N w, IsOptimal w (solve N w)
  cost : ℕ → ℕ → ℕ

/-- **Corollary 4.2, transfer.**  Composing a solver with the reduction solves MWIS on every finite
graph: it returns a maximum-weight independent set, at a cost of at most
`cost(4|E| + 2|V| + 2, |V|) + 4 (|V| + |E| + 1)² + |V|`. -/
theorem transfer (S : Solver) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (c : V → ℕ) :
    IsMWIS H c (decode H (S.solve (N H) (wt H c))) ∧
    S.cost (N H) (Fintype.card V) + encodeCost H + decodeCost (V := V) ≤
      S.cost (4 * H.edgeFinset.card + 2 * Fintype.card V + 2) (Fintype.card V) +
        4 * (Fintype.card V + H.edgeFinset.card + 1) ^ 2 + Fintype.card V :=
  ⟨decode_optimal H c (S.correct _ _), by
    have := encode_cost_le H
    unfold decodeCost
    unfold N at *
    omega⟩

/-- **Corollary 4.2, polynomial transfer.**  If the solver costs at most `a (N + m)^k`, MWIS on a
graph with `|V| + |E| = s` is solved at a cost of at most `a (4 s + 2)^k + 4 (s + 1)² + s`:
a polynomial-cost solver for split-conflict instances gives a polynomial-cost solver of MWIS on all
graphs. -/
theorem transfer_poly (S : Solver) {a k : ℕ} (hS : ∀ N m, S.cost N m ≤ a * (N + m) ^ k)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : V → ℕ) :
    IsMWIS H c (decode H (S.solve (N H) (wt H c))) ∧
    S.cost (N H) (Fintype.card V) + encodeCost H + decodeCost (V := V) ≤
      a * (4 * (Fintype.card V + H.edgeFinset.card) + 2) ^ k +
        4 * (Fintype.card V + H.edgeFinset.card + 1) ^ 2 +
        (Fintype.card V + H.edgeFinset.card) := by
  obtain ⟨h1, h2⟩ := transfer S H c
  refine ⟨h1, h2.trans ?_⟩
  have hc := hS (4 * H.edgeFinset.card + 2 * Fintype.card V + 2) (Fintype.card V)
  have hpow : (4 * H.edgeFinset.card + 2 * Fintype.card V + 2 + Fintype.card V) ^ k ≤
      (4 * (Fintype.card V + H.edgeFinset.card) + 2) ^ k :=
    Nat.pow_le_pow_left (by omega) k
  have := Nat.mul_le_mul_left a hpow
  omega

/-! ### Every graph is a split-conflict graph -/

/-- `H` is the conflict graph of a family of distinct non-trivial full splits. -/
def IsSplitConflict {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (τ : V → Finset (Fin m)), (∀ v, 2 ≤ (τ v).card ∧ 2 ≤ (τ v)ᶜ.card) ∧
    (∀ u v, u ≠ v → τ u ≠ τ v ∧ τ u ≠ (τ v)ᶜ) ∧
    (∀ u v, u ≠ v → (¬ Compat (τ u) (τ v) ↔ H.Adj u v))

/-- Every finite simple graph is a split-conflict graph (Theorem 4.1). -/
theorem every_graph_split_conflict {V : Type*} [Fintype V] (H : SimpleGraph V) :
    IsSplitConflict H := by
  classical
  exact ⟨_, _, (universality H).choose_spec⟩

/-- **Corollary 4.2, second sentence, before `P ≠ NP`.**  A class of finite graphs that contains
every split-conflict graph contains every finite graph; so a class on which MWIS is solvable in
polynomial time cannot contain every split-conflict graph unless MWIS is so solvable on all graphs,
which is NP-hard (Karp 1972, not formalised). -/
theorem class_contains_all (𝒞 : ∀ {V : Type} [Fintype V], SimpleGraph V → Prop)
    (h : ∀ {V : Type} [Fintype V] (H : SimpleGraph V), IsSplitConflict H → 𝒞 H)
    {V : Type} [Fintype V] (H : SimpleGraph V) : 𝒞 H :=
  h H (every_graph_split_conflict H)

end Stemma.Reduction
