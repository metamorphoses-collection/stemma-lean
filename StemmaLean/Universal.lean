/-
Universality of split-conflict graphs (Theorem 4.1 of the technical report, `thm:universal`):
every finite simple graph `H = (V, E)` is the conflict graph of a family of distinct non-trivial
full splits on `4|E| + 2|V| + 2` witnesses.

This is the combinatorial core of Corollary 4.2 (`cor:nphard`): the gadget is correct.  The
reduction (weights, size, cost, transfer of a solver) is `Reduction.lean`.

Witnesses: two private witnesses per vertex, four witnesses `q_e^{ab}` (`a, b ∈ Bool`) per edge `e`
with its endpoints in a fixed order (`a` the coordinate of the first endpoint, `b` of the second),
and two auxiliary witnesses.  Side 1 of `σ_v` holds the private witnesses of `v` and every `q_e^{ab}`
with `e ∋ v` whose coordinate for `v` is `1`.
-/
import Mathlib
import StemmaLean.Basic

namespace Stemma.Universal

open Finset

/-- Compatibility of two full splits on any finite witness type, each given by one side (the same
four-intersection condition as `Stemma.Compat`). -/
def CompatG {α : Type*} [Fintype α] [DecidableEq α] (A C : Finset α) : Prop :=
  A ∩ C = ∅ ∨ A ∩ Cᶜ = ∅ ∨ Aᶜ ∩ C = ∅ ∨ Aᶜ ∩ Cᶜ = ∅

/-- Four witnesses, one in each of the four intersections, make two splits conflict. -/
lemma not_compatG {α : Type*} [Fintype α] [DecidableEq α] {A C : Finset α} {x y z t : α}
    (hx : x ∈ A ∧ x ∈ C) (hy : y ∈ A ∧ y ∉ C) (hz : z ∉ A ∧ z ∈ C) (ht : t ∉ A ∧ t ∉ C) :
    ¬ CompatG A C := by
  have ne : ∀ (X : Finset α) (w : α), w ∈ X → X ≠ ∅ := fun X w hw h => by
    rw [h] at hw; simp at hw
  unfold CompatG
  refine not_or.mpr ⟨ne _ x ?_, not_or.mpr ⟨ne _ y ?_, not_or.mpr ⟨ne _ z ?_, ne _ t ?_⟩⟩⟩ <;>
    simp [hx, hy, hz, ht]

section gadget

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A fixed order on the vertices (through an enumeration). -/
noncomputable def ord (v : V) : ℕ := (Fintype.equivFin V v : ℕ)

omit [DecidableEq V] in
lemma ord_inj : Function.Injective (ord (V := V)) := fun _ _ h =>
  (Fintype.equivFin V).injective (Fin.ext h)

/-- Edges of `H`, each with its endpoints in the fixed order. -/
abbrev Edge : Type _ := {p : V × V // ord p.1 < ord p.2 ∧ H.Adj p.1 p.2}

/-- The witnesses: private `(v, i)`, edge witnesses `(e, a, b)`, auxiliary `z_i`. -/
abbrev Wit : Type _ := (V × Bool) ⊕ (Edge H × Bool × Bool) ⊕ Bool

/-- Membership in side 1 of `σ_v`. -/
def inSide (v : V) : Wit H → Prop
  | .inl (x, _) => x = v
  | .inr (.inl (e, a, b)) => (e.1.1 = v ∧ a = true) ∨ (e.1.2 = v ∧ b = true)
  | .inr (.inr _) => False

/-- Side 1 of `σ_v`. -/
noncomputable def side (v : V) : Finset (Wit H) := by
  classical exact univ.filter (inSide H v)

lemma mem_side {v : V} {x : Wit H} : x ∈ side H v ↔ inSide H v x := by
  classical
  unfold side
  simp only [mem_filter, mem_univ, true_and]

lemma card_wit : Fintype.card (Wit H) = 4 * Fintype.card (Edge H) + 2 * Fintype.card V + 2 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

/-- The edges in fixed order are as many as the edges of `H`. -/
lemma card_edge : Fintype.card (Edge H) = H.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card]
  let g : Edge H → H.edgeSet := fun p => ⟨s(p.1.1, p.1.2), (SimpleGraph.mem_edgeSet H).mpr p.2.2⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨a, b⟩, hab, _⟩ ⟨⟨c, d⟩, hcd, _⟩ h
      simp only [g, Subtype.mk.injEq, Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd (hab.trans hcd) (lt_irrefl _)
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h x y =>
        have hxy : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp he
        have hne : ord x ≠ ord y := fun h => H.ne_of_adj hxy (ord_inj h)
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨⟨(x, y), h, hxy⟩, rfl⟩
        · refine ⟨⟨(y, x), h, hxy.symm⟩, ?_⟩
          simp only [g, Subtype.mk.injEq]; exact Sym2.eq_swap
  exact Fintype.card_of_bijective hg

/-- Adjacent vertices give conflicting splits. -/
lemma conflict_of_adj {u v : V} (huv : u ≠ v) (h : H.Adj u v) :
    ¬ CompatG (side H u) (side H v) := by
  have hne : ord u ≠ ord v := fun e => huv (ord_inj e)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e : Edge H := ⟨(u, v), hlt, h⟩
    apply not_compatG (x := .inr (.inl (e, true, true))) (y := .inr (.inl (e, true, false)))
      (z := .inr (.inl (e, false, true))) (t := .inr (.inl (e, false, false))) <;>
      simp [mem_side, inSide, e, huv, huv.symm]
  · let e : Edge H := ⟨(v, u), hlt, h.symm⟩
    apply not_compatG (x := .inr (.inl (e, true, true))) (y := .inr (.inl (e, false, true)))
      (z := .inr (.inl (e, true, false))) (t := .inr (.inl (e, false, false))) <;>
      simp [mem_side, inSide, e, huv, huv.symm]

/-- Non-adjacent distinct vertices give splits with disjoint sides 1, hence compatible. -/
lemma compat_of_not_adj {u v : V} (huv : u ≠ v) (h : ¬ H.Adj u v) :
    CompatG (side H u) (side H v) := by
  left
  ext x
  simp only [mem_inter, mem_side, notMem_empty, iff_false, not_and]
  rcases x with ⟨y, i⟩ | ⟨⟨⟨a, b⟩, hab, hadj⟩, p, q⟩ | z
  · simp only [inSide]; rintro rfl; exact huv
  · simp only [inSide]
    have hab' : a ≠ b := fun e => by rw [e] at hab; exact lt_irrefl _ hab
    rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) (⟨e, -⟩ | ⟨e, -⟩)
    · exact huv e
    · exact h (e ▸ hadj)
    · exact h (e ▸ hadj.symm)
    · exact huv e
  · simp [inSide]

lemma side_nontriv (v : V) : 2 ≤ (side H v).card ∧ 2 ≤ (side H v)ᶜ.card := by
  constructor
  · have hsub : ({.inl (v, false), .inl (v, true)} : Finset (Wit H)) ⊆ side H v := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [mem_side, inSide]
    have := card_le_card hsub
    rwa [card_pair (by simp)] at this
  · have hsub : ({.inr (.inr false), .inr (.inr true)} : Finset (Wit H)) ⊆ (side H v)ᶜ := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [mem_side, inSide]
    have := card_le_card hsub
    rwa [card_pair (by simp)] at this

lemma side_distinct {u v : V} (huv : u ≠ v) : side H u ≠ side H v ∧ side H u ≠ (side H v)ᶜ := by
  constructor
  · intro e
    have : (.inl (u, false) : Wit H) ∈ side H u := by simp [mem_side, inSide]
    rw [e, mem_side] at this
    exact huv this
  · intro e
    have : (.inr (.inr false) : Wit H) ∈ (side H v)ᶜ := by simp [mem_side, inSide]
    rw [← e, mem_side] at this
    exact this

end gadget

/-! ### Transport to the witnesses `Fin N` -/

section transport

variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (e : α ≃ Fin N)

lemma map_compl_equiv (s : Finset α) : (s.map e.toEmbedding)ᶜ = sᶜ.map e.toEmbedding := by
  ext y; simp [mem_map_equiv]

lemma compat_map (s t : Finset α) :
    Compat (s.map e.toEmbedding) (t.map e.toEmbedding) ↔ CompatG s t := by
  unfold Compat CompatG
  simp only [map_compl_equiv, ← map_inter, map_eq_empty]

end transport

/-- **Theorem 4.1 (`thm:universal`), universality.**  Every finite simple graph `H = (V, E)` is
the conflict graph of a family of distinct non-trivial full splits on `4|E| + 2|V| + 2`
witnesses: there are splits `σ v` (given by one side) on `Fin (4|E| + 2|V| + 2)`, non-trivial,
pairwise distinct as unordered bipartitions, with `σ u` and `σ v` in conflict exactly when `u` and
`v` are adjacent.  The report assumes `|V| ≥ 2`; the Lean statement does not need it. -/
theorem universality {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    ∃ σ : V → Finset (Fin (4 * H.edgeFinset.card + 2 * Fintype.card V + 2)),
      (∀ v, 2 ≤ (σ v).card ∧ 2 ≤ (σ v)ᶜ.card) ∧
      (∀ u v, u ≠ v → σ u ≠ σ v ∧ σ u ≠ (σ v)ᶜ) ∧
      (∀ u v, u ≠ v → (¬ Compat (σ u) (σ v) ↔ H.Adj u v)) := by
  have hcard : Fintype.card (Wit H) = 4 * H.edgeFinset.card + 2 * Fintype.card V + 2 := by
    rw [card_wit, card_edge]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun v => (side H v).map e.toEmbedding, fun v => ?_, fun u v huv => ?_,
    fun u v huv => ?_⟩
  · rw [map_compl_equiv, card_map, card_map]; exact side_nontriv H v
  · rw [map_compl_equiv, Ne, Ne, map_inj, map_inj]; exact side_distinct H huv
  · rw [compat_map]
    constructor
    · intro hc; by_contra ha; exact hc (compat_of_not_adj H huv ha)
    · exact conflict_of_adj H huv

end Stemma.Universal
