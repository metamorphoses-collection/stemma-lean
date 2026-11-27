/-
The crossing set: Proposition 9.2 of the technical report (`prop:crossing`).

Let `T` be a stemma, a tree labelled by the witnesses `Fin n`, and `τ = A | Aᶜ` a split.  The
edges of `T[A]`, the smallest subtree spanning (the labels of) `A`, are the edges on the paths
between two witnesses of `A` (`InSpan`).  The proposition says:

* an edge's split is in conflict with `τ` iff the edge lies in both `T[A]` and `T[Aᶜ]`
  (`crossing_iff`);
* these edges form a connected subtree (`crossing_path`: every edge of the path between two
  crossing edges crosses, so the path joins them inside the crossing set);
* they are internal (`crossing_internal`: both sides of a crossing edge have two witnesses);
* if `T` is binary and `τ ∉ Σ(T)`, there is at least one (`crossing_nonempty`).

The split of an edge `e` is recorded by its side containing a vertex `w` (`side T φ e w`); a
conflict holds for one side iff for the other, and `crossing_iff` holds for every `w`.  The
theorems need only that `T` is a tree with some labelling `φ`; non-emptiness uses the binary
stemmata of `BinaryTree.lean`.
-/
import Mathlib
import StemmaLean.BinaryTree

open Finset
open Phylogenetics.SplitsEquivalence
open scoped Classical

namespace Stemma.Crossing

open SimpleGraph Stemma.Splits Stemma.BinaryTree

variable {n : ℕ} {W : Type*} {T : SimpleGraph W} {φ : Fin n → W}

/-- The side of the split of the edge `e` that contains the vertex `w`: the witnesses reached from
`w` without `e`. -/
noncomputable def side (T : SimpleGraph W) (φ : Fin n → W) (e : Sym2 W) (w : W) :
    Finset (Fin n) :=
  univ.filter fun y => (T.deleteEdges {e}).Reachable w (φ y)

/-- `e` is an edge of `T[A]`: it lies on the path between two witnesses of `A`. -/
def InSpan (T : SimpleGraph W) (φ : Fin n → W) (A : Finset (Fin n)) (e : Sym2 W) : Prop :=
  ∃ a ∈ A, ∃ a' ∈ A, ∃ p : T.Walk (φ a) (φ a'), p.IsPath ∧ e ∈ p.edges

/-! ### Paths in a tree and deleted edges -/

lemma not_mem_of_walk_deleteEdges {e : Sym2 W} {u v : W} (q : (T.deleteEdges {e}).Walk u v) :
    e ∉ q.edges := by
  intro h
  have := q.edges_subset_edgeSet h
  rw [edgeSet_deleteEdges] at this
  exact this.2 rfl

/-- In a tree, an edge lies on the path between `u` and `v` iff deleting it separates them. -/
theorem mem_path_iff (hT : T.IsTree) {u v : W} (p : T.Walk u v) (hp : p.IsPath) (e : Sym2 W) :
    e ∈ p.edges ↔ ¬ (T.deleteEdges {e}).Reachable u v := by
  constructor
  · rintro he ⟨q⟩
    let q' := (q.mapLe (deleteEdges_le _)).bypass
    have hq' : q'.IsPath := Walk.bypass_isPath _
    have heq : (⟨p, hp⟩ : T.Path u v) = ⟨q', hq'⟩ := (hT.isAcyclic.subsingleton_path u v).elim _ _
    have : e ∈ q'.edges := by
      have := congrArg Subtype.val heq
      simp only at this
      rw [← this]; exact he
    have := Walk.edges_bypass_subset_edges _ this
    simp at this
    exact not_mem_of_walk_deleteEdges q this
  · intro h
    by_contra he
    exact h ⟨p.toDeleteEdges {e} fun e' he' h' => he (by
      rw [Set.mem_singleton_iff.mp h'] at he'; exact he')⟩

/-- Without an edge, a tree falls into the two classes of its ends: if `u` and `v` are separated,
everything is reached from one of them. -/
lemma reach_or (hT : T.IsTree) {e : Sym2 W} {u v : W}
    (huv : ¬ (T.deleteEdges {e}).Reachable u v) (w : W) :
    (T.deleteEdges {e}).Reachable u w ∨ (T.deleteEdges {e}).Reachable v w := by
  induction e using Sym2.ind with
  | h a b =>
    have h := reachable_deleteEdges_or hT.connected a b
    rcases h u with hu | hu <;> rcases h v with hv | hv <;> rcases h w with hw | hw
    · exact absurd (hu.symm.trans hv) huv
    · exact absurd (hu.symm.trans hv) huv
    · exact Or.inl (hu.symm.trans hw)
    · exact Or.inr (hv.symm.trans hw)
    · exact Or.inr (hv.symm.trans hw)
    · exact Or.inl (hu.symm.trans hw)
    · exact absurd (hu.symm.trans hv) huv
    · exact absurd (hu.symm.trans hv) huv

/-- Two vertices not reached from `w` are reached from each other. -/
lemma reach_of_not (hT : T.IsTree) {e : Sym2 W} {u v : W}
    (huv : ¬ (T.deleteEdges {e}).Reachable u v) {w x y : W}
    (hx : ¬ (T.deleteEdges {e}).Reachable w x) (hy : ¬ (T.deleteEdges {e}).Reachable w y) :
    (T.deleteEdges {e}).Reachable x y := by
  rcases reach_or hT huv x with h1 | h1 <;> rcases reach_or hT huv y with h2 | h2 <;>
    rcases reach_or hT huv w with h3 | h3
  all_goals first
    | exact h1.symm.trans h2
    | exact absurd (h3.symm.trans h1) hx
    | exact absurd (h3.symm.trans h2) hy

/-- Deleting an edge of a tree separates `x` from `y` iff exactly one of them is reached from `w`. -/
lemma sep_iff (hT : T.IsTree) {e : Sym2 W} (he : e ∈ T.edgeSet) (w x y : W) :
    ¬ (T.deleteEdges {e}).Reachable x y ↔
      ((T.deleteEdges {e}).Reachable w x ↔ ¬ (T.deleteEdges {e}).Reachable w y) := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : ¬ (T.deleteEdges {s(a, b)}).Reachable a b :=
      not_reachable_deleteEdges hT.isAcyclic he
    constructor
    · intro hxy
      by_cases hx : (T.deleteEdges {s(a, b)}).Reachable w x
      · exact ⟨fun _ hy => hxy (hx.symm.trans hy), fun _ => hx⟩
      · refine ⟨fun h => absurd h hx, fun hy => ?_⟩
        exact absurd (reach_of_not hT hab hx hy) hxy
    · intro h hxy
      by_cases hx : (T.deleteEdges {s(a, b)}).Reachable w x
      · exact h.mp hx (hx.trans hxy)
      · exact hx (by
          by_contra hy'
          have : ¬ ¬ (T.deleteEdges {s(a, b)}).Reachable w y := fun hy => hx (h.mpr hy)
          exact this (fun hy => hy' ((hy.trans hxy.symm))))

/-- `e` lies in `T[S]` iff it separates two witnesses of `S`. -/
lemma inSpan_iff (hT : T.IsTree) (S : Finset (Fin n)) (e : Sym2 W) :
    InSpan T φ S e ↔ ∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {e}).Reachable (φ a) (φ a') := by
  constructor
  · rintro ⟨a, ha, a', ha', p, hp, he⟩
    exact ⟨a, ha, a', ha', (mem_path_iff hT p hp e).mp he⟩
  · rintro ⟨a, ha, a', ha', h⟩
    obtain ⟨p, hp, -⟩ := hT.existsUnique_path (φ a) (φ a')
    exact ⟨a, ha, a', ha', p, hp, (mem_path_iff hT p hp e).mpr h⟩

lemma sep_exists_iff (hT : T.IsTree) {e : Sym2 W} (he : e ∈ T.edgeSet) (w : W)
    (S : Finset (Fin n)) :
    (∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {e}).Reachable (φ a) (φ a')) ↔
      S ∩ side T φ e w ≠ ∅ ∧ S ∩ (side T φ e w)ᶜ ≠ ∅ := by
  simp only [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, ha, a', ha', h⟩
    have h' := (sep_iff hT he w _ _).mp h
    by_cases hw : (T.deleteEdges {e}).Reachable w (φ a)
    · exact ⟨⟨a, by simp [side, ha, hw]⟩, ⟨a', by simp [side, ha', h'.mp hw]⟩⟩
    · have : (T.deleteEdges {e}).Reachable w (φ a') := by
        by_contra hc; exact hw (h'.mpr hc)
      exact ⟨⟨a', by simp [side, ha', this]⟩, ⟨a, by simp [side, ha, hw]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    simp only [side, mem_inter, mem_filter, mem_univ, true_and, mem_compl] at ha ha'
    exact ⟨a, ha.1, a', ha'.1, (sep_iff hT he w _ _).mpr ⟨fun _ => ha'.2, fun _ => ha.2⟩⟩

/-! ### The proposition -/

/-- **Proposition 9.2 (`prop:crossing`), first part.**  For an edge `e` of a stemma `T` and a
split `τ = A | Aᶜ`, the split of `e` (by either side) is in conflict with `τ` iff `e` lies in both
`T[A]` and `T[Aᶜ]`. -/
theorem crossing_iff (hT : T.IsTree) {e : Sym2 W} (he : e ∈ T.edgeSet) (A : Finset (Fin n))
    (w : W) :
    ¬ Compat A (side T φ e w) ↔ InSpan T φ A e ∧ InSpan T φ Aᶜ e := by
  rw [inSpan_iff hT, inSpan_iff hT, sep_exists_iff hT he w, sep_exists_iff hT he w]
  unfold Compat
  tauto

/-- **Proposition 9.2, internal edges.**  An edge whose split conflicts with `τ` has at least two
witnesses on each side, so it is not a pendant edge. -/
theorem crossing_internal {e : Sym2 W} {A : Finset (Fin n)} {w : W}
    (h : ¬ Compat A (side T φ e w)) :
    2 ≤ (side T φ e w).card ∧ 2 ≤ (side T φ e w)ᶜ.card := by
  unfold Compat at h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have two : ∀ P : Finset (Fin n), (A ∩ P).Nonempty → (Aᶜ ∩ P).Nonempty → 2 ≤ P.card := by
    intro P hA hB
    obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy⟩ := hB
    rw [mem_inter] at hx hy
    have hxy : x ≠ y := by rintro rfl; exact (mem_compl.mp hy.1) hx.1
    calc 2 = ({x, y} : Finset (Fin n)).card := (card_pair hxy).symm
      _ ≤ P.card := card_le_card (by
          intro z hz; rw [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          exacts [hx.2, hy.2])
  exact ⟨two _ h1 h3, two _ h2 h4⟩

/-- The convexity step, for one side `S` of `τ`: if `e` and `f` each separate two witnesses of
`S`, so does every edge `g` separating an end of `e` from an end of `f`. -/
lemma convex_one (hT : T.IsTree) {S : Finset (Fin n)} {e f g : Sym2 W}
    (hSe : ∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {e}).Reachable (φ a) (φ a'))
    (hSf : ∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {f}).Reachable (φ a) (φ a'))
    {u v : W} (hu : u ∈ e) (hv : v ∈ f) (hg : ¬ (T.deleteEdges {g}).Reachable u v) :
    ∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {g}).Reachable (φ a) (φ a') := by
  -- from each end, one witness of `S` is reached without `g`
  have side_hit : ∀ {e : Sym2 W} {u v : W}, u ∈ e →
      ¬ (T.deleteEdges {g}).Reachable u v →
      (∃ a ∈ S, ∃ a' ∈ S, ¬ (T.deleteEdges {e}).Reachable (φ a) (φ a')) →
      ∃ a ∈ S, (T.deleteEdges {g}).Reachable u (φ a) := by
    intro e u v hu huv ⟨a1, ha1, a2, ha2, h12⟩
    by_contra hno
    push Not at hno
    obtain ⟨q⟩ := reach_of_not hT huv (hno a1 ha1) (hno a2 ha2)
    have heq : e ∈ (q.mapLe (deleteEdges_le _)).edges := by
      by_contra hne
      exact h12 ⟨(q.mapLe (deleteEdges_le _)).toDeleteEdges {e} fun e' he' h' => hne (by
        rw [Set.mem_singleton_iff.mp h'] at he'; exact he')⟩
    simp at heq
    obtain ⟨u', rfl⟩ := Sym2.mem_iff_exists.mp hu
    have hsup := q.fst_mem_support_of_mem_edges heq
    exact hno a1 ha1 ⟨(q.takeUntil u hsup).reverse⟩
  obtain ⟨a, ha, hua⟩ := side_hit hu hg hSe
  obtain ⟨a', ha', hva'⟩ := side_hit hv (fun h => hg h.symm) hSf
  exact ⟨a, ha, a', ha', fun h => hg ((hua.trans h).trans hva'.symm)⟩

/-- **Proposition 9.2, connectedness.**  If the splits of two edges `e` and `f` conflict with
`τ`, so does the split of every edge on the path between an end of `e` and an end of `f`.  The
path therefore joins `e` to `f` inside the crossing set, which is a connected subtree. -/
theorem crossing_path (hT : T.IsTree) {A : Finset (Fin n)} {e f : Sym2 W}
    (he : InSpan T φ A e ∧ InSpan T φ Aᶜ e) (hf : InSpan T φ A f ∧ InSpan T φ Aᶜ f)
    {u v : W} (hu : u ∈ e) (hv : v ∈ f) (p : T.Walk u v) (hp : p.IsPath) {g : Sym2 W}
    (hg : g ∈ p.edges) :
    InSpan T φ A g ∧ InSpan T φ Aᶜ g := by
  have hsep := (mem_path_iff hT p hp g).mp hg
  simp only [inSpan_iff hT] at he hf ⊢
  exact ⟨convex_one hT he.1 hf.1 hu hv hsep, convex_one hT he.2 hf.2 hu hv hsep⟩

/-- **Proposition 9.2, non-emptiness.**  If `T` is a binary stemma and the non-trivial split
`τ = A | Aᶜ` (`A` its side away from `r`) is not a split of `T`, some edge of `T` crosses `τ`.
This is Lemma 3.3(ii): `Σ(T)` is a maximal compatible set. -/
theorem crossing_nonempty [Fintype W] (hn : 3 ≤ n) (r : Fin n) (hB : IsBinaryTree T φ)
    {A : Finset (Fin n)} (hA : IsSide r A) (hnot : A ∉ nsplits T φ r) :
    ∃ e ∈ T.edgeSet, InSpan T φ A e ∧ InSpan T φ Aᶜ e := by
  by_contra h
  push Not at h
  apply hnot
  refine maximal (binary_tree_splits hn r hB).1 hA fun σ hσ => ?_
  obtain ⟨e, he, x, hx⟩ := (mem_filter.mp hσ).2.2
  have hside : σ = side T φ e (φ x) := by
    apply coe_injective
    rw [hx]; ext y; simp [side, edgeSide]
  rw [hside]
  by_contra hc
  obtain ⟨h1, h2⟩ := (crossing_iff hB.isTree he A (φ x)).mp hc
  exact h e he h1 h2

end Stemma.Crossing
