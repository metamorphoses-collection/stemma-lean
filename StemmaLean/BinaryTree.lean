/-
A binary tree has exactly `n - 3` non-trivial splits: the first half of Lemma 3.3(ii) of the
technical report (`lem:facts`).

A binary stemma, as a Mathlib graph (`IsBinaryTree`): a tree whose leaves are labelled bijectively
by the `n` witnesses (every label has degree one, the labelling is injective) and whose unlabelled
vertices have degree three.  Its non-trivial splits form a system of exactly `n - 3` sides
(`Splits.IsBinary`), and its split system is that system with the trivial splits (`Buneman.fam`).

The proof counts vertices twice.  By the degree sum and `IsTree.card_edgeFinset`, the tree has
`2n - 2` vertices.  By uniqueness in the Splits Equivalence Theorem (`xTree_unique`, vendored), it
is isomorphic to the tree that the existence proof builds from its split system, whose vertices are
the sides away from `r` and one root: `|S| + (n - 1) + 1 + 1` of them, `S` the non-trivial sides
away from `r`.  So `|S| = n - 3`.  This avoids proving directly that distinct edges carry distinct
splits.

A related formalisation, with the same hypotheses on unrooted binary trees, is the
`UnrootedBinaryTree` structure of `facebookresearch/atlas-lean`; it is not used here.
-/
import Mathlib
import StemmaLean.Buneman
import StemmaLean.Rooted

open Finset
open Phylogenetics.SplitsEquivalence
open scoped Classical

namespace Stemma.BinaryTree

open Splits Buneman

variable {n : ℕ} {W : Type*} [Fintype W] {T : SimpleGraph W} {φ : Fin n → W}

/-- A binary stemma on the witnesses `Fin n`: a tree, with the witnesses labelling distinct
vertices of degree one, and every unlabelled vertex of degree three. -/
structure IsBinaryTree (T : SimpleGraph W) (φ : Fin n → W) : Prop where
  isTree : T.IsTree
  inj : Function.Injective φ
  leaf : ∀ x, T.degree (φ x) = 1
  inner : ∀ v, v ∉ Set.range φ → T.degree v = 3

lemma IsBinaryTree.isXTree (hB : IsBinaryTree T φ) : IsXTree T φ := by
  refine ⟨hB.isTree, fun v hv => ?_⟩
  by_contra h
  rw [SimpleGraph.ncard_neighborSet] at hv
  have := hB.inner v h
  omega

/-- A binary stemma on `n` leaves has `2n - 2` vertices. -/
lemma IsBinaryTree.card (hB : IsBinaryTree T φ) : Fintype.card W = 2 * n - 2 := by
  have hE := hB.isTree.card_edgeFinset
  have hS := T.sum_degrees_eq_twice_card_edges
  set R := univ.image φ
  have hR : R.card = n := by rw [card_image_of_injective _ hB.inj]; simp
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset W) (· ∈ R) (fun v => T.degree v)
  have h1 : ∑ v ∈ univ.filter (· ∈ R), T.degree v = n := by
    rw [filter_mem_eq_inter, univ_inter, sum_image fun x _ y _ h => hB.inj h]
    simp [hB.leaf]
  have h2 : ∑ v ∈ univ.filter (· ∉ R), T.degree v = 3 * (Fintype.card W - n) := by
    rw [sum_congr rfl fun v hv => hB.inner v (by
      simp only [mem_filter, mem_univ, true_and, R, mem_image, not_exists, not_and] at hv
      rintro ⟨x, rfl⟩; exact hv x rfl)]
    rw [sum_const, smul_eq_mul, mul_comm]
    congr 1
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, filter_mem_eq_inter,
      univ_inter, hR]
  have hn : n ≤ Fintype.card W := by
    have := card_le_univ R; rw [hR] at this; exact this
  have hcardE : T.edgeFinset.card = (Set.toFinset T.edgeSet).card := rfl
  omega

/-! ### The split system of an `X`-tree -/

/-- The split system of an `X`-tree is a split system: every side is non-empty, with non-empty
complement, which is again a side. -/
lemma splitSides_isSplitSystem (hX : IsXTree T φ) : IsSplitSystem (splitSides T φ) := by
  have hT := hX.isTree
  rintro A ⟨e, he, x, rfl⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hab : T.Adj a b := he
    have key : ∀ {u v : W}, T.Adj u v → (T.deleteEdges {s(u, v)}).Reachable u (φ x) →
        (edgeSide T φ s(u, v) x)ᶜ.Nonempty ∧ (edgeSide T φ s(u, v) x)ᶜ ∈ splitSides T φ := by
      intro u v huv hux
      have hside : edgeSide T φ s(u, v) x = sideOf T φ s(u, v) u :=
        (sideOf_eq_of_reachable hux).symm
      have hnr : ¬ (T.deleteEdges {s(u, v)}).Reachable u v := not_reachable_deleteEdges hT.2 huv
      have hc : (sideOf T φ s(u, v) u)ᶜ = sideOf T φ s(u, v) v := sideOf_compl hT huv hnr
      obtain ⟨y, hy⟩ := exists_label_branch hX huv
      rw [hside, hc]
      refine ⟨⟨y, hy⟩, s(u, v), huv, y, ?_⟩
      rw [edgeSide_eq_sideOf]; exact sideOf_eq_of_reachable hy
    refine ⟨⟨x, SimpleGraph.Reachable.refl _⟩, ?_⟩
    rcases reachable_deleteEdges_or hT.1 a b (φ x) with h | h
    · exact key hab h
    · have h' : (T.deleteEdges {s(b, a)}).Reachable b (φ x) := by rwa [Sym2.eq_swap]
      have := key hab.symm h'
      rwa [Sym2.eq_swap] at this

/-- The split system of an `X`-tree is pairwise compatible. -/
lemma splitSides_compatible (hX : IsXTree T φ) (hn : 0 < n) :
    PairwiseCompatible (splitSides T φ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨m, T', ⟨f⟩⟩ := exists_iso_fin T
  rw [← splitSides_map f]
  exact (exists_xTree_iff (splitSides_isSplitSystem (hX.map f))).mpr ⟨m, T', f ∘ φ, hX.map f, rfl⟩

/-! ### Binary trees -/

/-- The non-trivial splits of the tree, by their sides away from `r`. -/
noncomputable def nsplits (T : SimpleGraph W) (φ : Fin n → W) (r : Fin n) :
    Finset (Finset (Fin n)) :=
  univ.filter fun B => IsSide r B ∧ (B : Set (Fin n)) ∈ splitSides T φ

lemma nsplits_isSystem (hX : IsXTree T φ) (r : Fin n) : IsSystem r (nsplits T φ r) := by
  have hn : 0 < n := Fin.pos r
  refine ⟨fun B hB => (mem_filter.mp hB).2.1, fun a ha b hb _ => ?_⟩
  have ha' := (mem_filter.mp ha).2.2
  have hb' := (mem_filter.mp hb).2.2
  exact setCompat_coe.mp (splitSides_compatible hX hn _ ha' _ hb')

/-- A leaf edge carries the trivial split `{x}`. -/
lemma leaf_sides (hB : IsBinaryTree T φ) (x : Fin n) :
    ({x} : Set (Fin n)) ∈ splitSides T φ ∧ ({x}ᶜ : Set (Fin n)) ∈ splitSides T φ := by
  have hX := hB.isXTree
  have hT := hB.isTree
  obtain ⟨w, hw, huniq⟩ := (T.degree_eq_one_iff_existsUnique_adj).mp (hB.leaf x)
  have hside : edgeSide T φ s(φ x, w) x = {x} := by
    ext y
    simp only [edgeSide, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hyx
      have hne : φ x ≠ φ y := fun e => hyx (hB.inj e).symm
      obtain ⟨p⟩ := h
      obtain ⟨z, hadj, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
      rw [SimpleGraph.deleteEdges_adj] at hadj
      obtain ⟨hadj, hne'⟩ := hadj
      exact hne' (by rw [huniq _ hadj]; rfl)
    · rintro rfl; exact SimpleGraph.Reachable.refl _
  have hnr : ¬ (T.deleteEdges {s(φ x, w)}).Reachable (φ x) w := not_reachable_deleteEdges hT.2 hw
  have hc : (sideOf T φ s(φ x, w) (φ x))ᶜ = sideOf T φ s(φ x, w) w := sideOf_compl hT hw hnr
  obtain ⟨y, hy⟩ := exists_label_branch hX hw
  refine ⟨⟨s(φ x, w), hw, x, hside.symm⟩, ⟨s(φ x, w), hw, y, ?_⟩⟩
  rw [← hside, edgeSide_eq_sideOf, hc, edgeSide_eq_sideOf]
  exact sideOf_eq_of_reachable hy

/-- The split system of a binary stemma is its non-trivial splits with the trivial ones. -/
lemma splitSides_eq_fam (hB : IsBinaryTree T φ) (r : Fin n) :
    splitSides T φ = fam (nsplits T φ r) := by
  have hX := hB.isXTree
  have hSS := splitSides_isSplitSystem hX
  ext A
  constructor
  · intro hA
    obtain ⟨hne, hcne, hcA⟩ := hSS A hA
    set B : Finset (Fin n) := A.toFinset
    have hAB : A = (B : Set (Fin n)) := by simp [B]
    by_cases h1 : ∃ x, A = {x}
    · obtain ⟨x, rfl⟩ := h1; exact Or.inr ⟨x, Or.inl rfl⟩
    by_cases h2 : ∃ x, A = {x}ᶜ
    · obtain ⟨x, rfl⟩ := h2; exact Or.inr ⟨x, Or.inr rfl⟩
    push Not at h1 h2
    have hB2 : 2 ≤ B.card := by
      have hpos : 0 < B.card := card_pos.mpr (by simpa [B] using hne)
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.mp (show B.card = 1 by omega)
      exact h1 x (by rw [hAB, hx, coe_singleton])
    have hBc2 : 2 ≤ Bᶜ.card := by
      have hpos : 0 < Bᶜ.card := card_pos.mpr (by
        rw [← coe_nonempty, coe_compl, ← hAB]; exact hcne)
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.mp (show Bᶜ.card = 1 by omega)
      exact h2 x (by rw [hAB, ← compl_compl (B : Set (Fin n)), ← coe_compl, hx, coe_singleton])
    left
    by_cases hr : r ∈ B
    · refine ⟨Bᶜ, mem_filter.mpr ⟨mem_univ _, ⟨by simp [hr], hBc2,
        by rw [compl_compl]; exact hB2⟩, ?_⟩, Or.inr ?_⟩
      · rw [coe_compl, ← hAB]; exact hcA
      · rw [coe_compl, compl_compl, ← hAB]
    · exact ⟨B, mem_filter.mpr ⟨mem_univ _, ⟨hr, hB2, hBc2⟩, hAB ▸ hA⟩, Or.inl hAB⟩
  · rintro (⟨B, hB', rfl | rfl⟩ | ⟨x, rfl | rfl⟩)
    · exact (mem_filter.mp hB').2.2
    · exact (hSS _ (mem_filter.mp hB').2.2).2.2
    · exact (leaf_sides hB x).1
    · exact (leaf_sides hB x).2

/-- The sides away from `r` in `fam S`: the sides of `S`, the singletons other than `{r}`, and
`{r}ᶜ`. -/
lemma rooted_fam_eq {r : Fin n} {S : Finset (Finset (Fin n))} (hS : ∀ A ∈ S, IsSide r A) :
    rootedSides (fam S) r =
      ↑((S.image fun B : Finset (Fin n) => (B : Set (Fin n))) ∪
        ((univ.erase r).image fun x : Fin n => ({x} : Set (Fin n))) ∪ {({r}ᶜ : Set (Fin n))}) := by
  ext A
  simp only [rootedSides, fam, Set.mem_ofPred_eq, coe_union, coe_image, coe_singleton,
    Set.mem_union, Set.mem_image, mem_coe, coe_erase, Set.mem_diff, Set.mem_univ, true_and,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨(⟨B, hB, rfl | rfl⟩ | ⟨x, rfl | rfl⟩), hr⟩
    · exact Or.inl (Or.inl ⟨B, hB, rfl⟩)
    · exact absurd (by simpa using (hS B hB).1) hr
    · exact Or.inl (Or.inr ⟨x, ⟨mem_univ _, fun e => hr (e ▸ Set.mem_singleton x)⟩, rfl⟩)
    · have : x = r := by by_contra h; exact hr (by simpa [eq_comm] using h)
      rw [this]; exact Or.inr rfl
  · rintro ((⟨B, hB, rfl⟩ | ⟨x, hx, rfl⟩) | rfl)
    · exact ⟨Or.inl ⟨B, hB, Or.inl rfl⟩, by simpa using (hS B hB).1⟩
    · exact ⟨Or.inr ⟨x, Or.inl rfl⟩, fun h => hx.2 (Set.mem_singleton_iff.mp h).symm⟩
    · exact ⟨Or.inr ⟨r, Or.inr rfl⟩, by simp⟩

lemma card_rooted_fam (hn : 3 ≤ n) {r : Fin n} {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) : (rootedSides (fam S) r).ncard = S.card + n := by
  rw [rooted_fam_eq hS, Set.ncard_coe_finset]
  have hcoe : Function.Injective fun B : Finset (Fin n) => (B : Set (Fin n)) := coe_injective
  have hsing : Function.Injective fun x : Fin n => ({x} : Set (Fin n)) := Set.singleton_injective
  have d1 : Disjoint (S.image fun B : Finset (Fin n) => (B : Set (Fin n)))
      ((univ.erase r).image fun x : Fin n => ({x} : Set (Fin n))) := by
    rw [disjoint_left]
    rintro A hA hA'
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    obtain ⟨x, -, hx⟩ := mem_image.mp hA'
    have : B = {x} := coe_injective (by rw [coe_singleton]; exact hx.symm)
    have := (hS B hB).2.1; rw [‹B = {x}›] at this; simp at this
  have d2 : ({({r}ᶜ : Set (Fin n))} : Finset (Set (Fin n))) ∩
      ((S.image fun B : Finset (Fin n) => (B : Set (Fin n))) ∪
        ((univ.erase r).image fun x : Fin n => ({x} : Set (Fin n)))) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro A hA
    rw [mem_inter, mem_singleton] at hA
    obtain ⟨rfl, hA⟩ := hA
    rcases mem_union.mp hA with h | h
    · obtain ⟨B, hB, e⟩ := mem_image.mp h
      have hBc : Bᶜ = {r} := coe_injective (by rw [coe_compl, e, compl_compl, coe_singleton])
      have := (hS B hB).2.2; rw [hBc] at this; simp at this
    · obtain ⟨x, hx, e⟩ := mem_image.mp h
      -- `{x} = {r}ᶜ` would leave only two witnesses
      have hsub : (univ : Finset (Fin n)) ⊆ {x, r} := by
        intro y _
        by_cases hy : y = r
        · simp [hy]
        · have : y ∈ ({r}ᶜ : Set (Fin n)) := by simpa using hy
          rw [← e] at this; simp at this; simp [this]
      have := card_le_card hsub
      rw [card_univ, Fintype.card_fin] at this
      have := card_insert_le x ({r} : Finset (Fin n)); simp at this
      omega
  rw [card_union_of_disjoint (disjoint_iff_inter_eq_empty.mpr (by rw [inter_comm]; exact d2)),
    card_union_of_disjoint d1, card_image_of_injective _ hcoe, card_image_of_injective _ hsing,
    card_singleton, card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]
  omega

/-- **Lemma 3.3(ii) (`lem:facts`), first half.**  For `n ≥ 3`, the non-trivial splits of a binary
stemma form a system of exactly `n - 3` sides (`IsBinary`), and its split system is that system
with the trivial splits. -/
theorem binary_tree_splits (hn : 3 ≤ n) (r : Fin n) (hB : IsBinaryTree T φ) :
    IsBinary r (nsplits T φ r) ∧ splitSides T φ = fam (nsplits T φ r) := by
  have : Nonempty (Fin n) := ⟨r⟩
  have hX := hB.isXTree
  have hsys := nsplits_isSystem hX r
  have hfam := splitSides_eq_fam hB r
  refine ⟨⟨hsys, ?_⟩, hfam⟩
  -- the tree built from the split system, rooted at `r`
  have hF : IsSplitSystem (fam (nsplits T φ r)) := hfam ▸ splitSides_isSplitSystem hX
  have hc : PairwiseCompatible (fam (nsplits T φ r)) :=
    hfam ▸ splitSides_compatible hX (by omega)
  have hL := rootedSides_isLaminar hF hc r
  have hX' := lam_isXTree hL (fun A hA => hA.2)
  have hsplit := lam_splitSides hF hc r
  obtain ⟨f, -⟩ := xTree_unique hX hX' (hfam.trans hsplit.symm)
  -- count the vertices of both trees
  have hcardW : Nat.card W = 2 * n - 2 := by rw [Nat.card_eq_fintype_card]; exact hB.card
  have hiso : Nat.card W = Nat.card (LamNode (rootedSides (fam (nsplits T φ r)) r)) :=
    Nat.card_congr f.toEquiv
  have huniv : Set.univ ∉ rootedSides (fam (nsplits T φ r)) r := fun h => h.2 (Set.mem_univ r)
  have hnode : Nat.card (LamNode (rootedSides (fam (nsplits T φ r)) r)) =
      (rootedSides (fam (nsplits T φ r)) r).ncard + 1 := by
    have e : {A : Set (Fin n) | A ∈ rootedSides (fam (nsplits T φ r)) r ∨ A = Set.univ} =
        insert Set.univ (rootedSides (fam (nsplits T φ r)) r) := by
      ext A; simp [or_comm]
    rw [show Nat.card (LamNode (rootedSides (fam (nsplits T φ r)) r)) =
        Nat.card {A : Set (Fin n) | A ∈ rootedSides (fam (nsplits T φ r)) r ∨ A = Set.univ}
      from rfl, Nat.card_coe_set_eq, e, Set.ncard_insert_of_notMem huniv (Set.toFinite _)]
  have hcount := card_rooted_fam hn (fun A hA => (mem_filter.mp hA).2.1 :
    ∀ A ∈ nsplits T φ r, IsSide r A)
  omega

/-! ### The converse: a system of `n - 3` splits is the split system of a binary tree -/

/-- An `X`-tree whose split system is `fam S`, for `S` a set of non-trivial sides away from `r`, has
`|S| + n + 1` vertices: it is isomorphic to the tree built from its split system. -/
lemma card_of_fam (hn : 3 ≤ n) {r : Fin n} {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) (hX : IsXTree T φ) (hfam : splitSides T φ = fam S) :
    Nat.card W = S.card + n + 1 := by
  have : Nonempty (Fin n) := ⟨r⟩
  have hF : IsSplitSystem (fam S) := hfam ▸ splitSides_isSplitSystem hX
  have hc : PairwiseCompatible (fam S) := hfam ▸ splitSides_compatible hX (by omega)
  have hL := rootedSides_isLaminar hF hc r
  have hX' := lam_isXTree hL (fun A hA => hA.2)
  have hsplit := lam_splitSides hF hc r
  obtain ⟨f, -⟩ := xTree_unique hX hX' (hfam.trans hsplit.symm)
  have hiso : Nat.card W = Nat.card (LamNode (rootedSides (fam S) r)) := Nat.card_congr f.toEquiv
  have huniv : Set.univ ∉ rootedSides (fam S) r := fun h => h.2 (Set.mem_univ r)
  have hnode : Nat.card (LamNode (rootedSides (fam S) r)) = (rootedSides (fam S) r).ncard + 1 := by
    have e : {A : Set (Fin n) | A ∈ rootedSides (fam S) r ∨ A = Set.univ} =
        insert Set.univ (rootedSides (fam S) r) := by
      ext A; simp [or_comm]
    rw [show Nat.card (LamNode (rootedSides (fam S) r)) =
        Nat.card {A : Set (Fin n) | A ∈ rootedSides (fam S) r ∨ A = Set.univ} from rfl,
      Nat.card_coe_set_eq, e, Set.ncard_insert_of_notMem huniv (Set.toFinite _)]
  have hcount := card_rooted_fam hn hS
  omega

/-- In an `X`-tree whose split system contains every trivial split `{x}`, distinct witnesses label
distinct vertices. -/
lemma inj_of_singletons (hsing : ∀ x : Fin n, ({x} : Set (Fin n)) ∈ splitSides T φ) :
    Function.Injective φ := by
  intro x y hxy
  obtain ⟨e, -, z, hz⟩ := hsing x
  have hx : x ∈ edgeSide T φ e z := hz ▸ Set.mem_singleton x
  have hy : y ∈ edgeSide T φ e z := by
    simp only [edgeSide, Set.mem_ofPred_eq] at hx ⊢; rw [← hxy]; exact hx
  rw [← hz] at hy
  exact (Set.mem_singleton_iff.mp hy).symm

/-- **Lemma 3.3(ii) (`lem:facts`), converse.**  For `n ≥ 3`, if `S` is a system of exactly `n - 3`
sides away from `r` and `(T, φ)` is an `X`-tree whose split system is `S` with the trivial splits
(one exists by Buneman's theorem), then `(T, φ)` is a binary stemma: the labelling is injective,
every label has degree one and every unlabelled vertex degree three. -/
theorem isBinaryTree_of_fam (hn : 3 ≤ n) {r : Fin n} {S : Finset (Finset (Fin n))}
    (hS : IsBinary r S) (hX : IsXTree T φ) (hfam : splitSides T φ = fam S) :
    IsBinaryTree T φ := by
  have hT := hX.isTree
  have hV : Fintype.card W = 2 * n - 2 := by
    rw [← Nat.card_eq_fintype_card, card_of_fam hn hS.1.1 hX hfam, hS.2]; omega
  have hinj : Function.Injective φ := inj_of_singletons fun x => by
    rw [hfam]; exact Or.inr ⟨x, Or.inl rfl⟩
  -- every vertex has degree at least one (the tree has at least two vertices)
  have hpos : ∀ v, 1 ≤ T.degree v := by
    intro v
    obtain ⟨u, hu⟩ : ∃ u : W, u ≠ v := by
      by_contra h; push Not at h
      have : Fintype.card W ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
      omega
    obtain ⟨p⟩ := hT.1.preconnected v u
    obtain ⟨w, hadj, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hu.symm p
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    have hw := (T.mem_neighborFinset v w).mpr hadj
    rw [← T.card_neighborFinset_eq_degree, card_eq_zero] at h0
    rw [h0] at hw; simp at hw
  -- unlabelled vertices have degree at least three
  have hthree : ∀ v, v ∉ Set.range φ → 3 ≤ T.degree v := by
    intro v hv
    by_contra h
    exact hv (hX.labelled v (by rw [SimpleGraph.ncard_neighborSet]; omega))
  -- the degree sum forces equality everywhere
  have hE := hT.card_edgeFinset
  have hsum := T.sum_degrees_eq_twice_card_edges
  set R := univ.image φ
  have hR : R.card = n := by rw [card_image_of_injective _ hinj]; simp
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset W) (· ∈ R) (fun v => T.degree v)
  have hRf : univ.filter (· ∈ R) = R := by rw [filter_mem_eq_inter, univ_inter]
  have hcompl : (univ.filter (· ∉ R)).card = Fintype.card W - n := by
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, hRf, hR]
  have hnotR : ∀ v ∈ univ.filter (· ∉ R), v ∉ Set.range φ := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, R, mem_image, not_exists, not_and] at hv
    rintro ⟨x, rfl⟩; exact hv x rfl
  have hlow1 : n ≤ ∑ v ∈ univ.filter (· ∈ R), T.degree v := by
    rw [hRf]
    calc n = ∑ _v ∈ R, 1 := by simp [hR]
      _ ≤ _ := sum_le_sum fun v _ => hpos v
  have hlow3 : 3 * (Fintype.card W - n) ≤ ∑ v ∈ univ.filter (· ∉ R), T.degree v := by
    calc 3 * (Fintype.card W - n) = ∑ _v ∈ univ.filter (· ∉ R), 3 := by
          rw [sum_const, smul_eq_mul, hcompl, mul_comm]
      _ ≤ _ := sum_le_sum fun v hv => hthree v (hnotR v hv)
  have hcardE : T.edgeFinset.card = (Set.toFinset T.edgeSet).card := rfl
  have heq1 : ∑ v ∈ univ.filter (· ∈ R), T.degree v = n := by omega
  have heq3 : ∑ v ∈ univ.filter (· ∉ R), T.degree v = 3 * (Fintype.card W - n) := by omega
  refine ⟨hT, hinj, fun x => ?_, fun v hv => ?_⟩
  · -- a sum of terms at least one, equal to the number of terms
    by_contra hx
    have hlt : ∑ _v ∈ R, 1 < ∑ v ∈ R, T.degree v :=
      sum_lt_sum (fun v _ => hpos v) ⟨φ x, mem_image_of_mem φ (mem_univ x), by
        have := hpos (φ x); omega⟩
    rw [hRf] at heq1
    simp [hR] at hlt; omega
  · have hvR : v ∈ univ.filter (· ∉ R) := by
      simp only [mem_filter, mem_univ, true_and, R, mem_image, not_exists]
      exact fun x e => hv ⟨x, e⟩
    by_contra h3
    have hlt : ∑ _v ∈ univ.filter (· ∉ R), 3 < ∑ v ∈ univ.filter (· ∉ R), T.degree v :=
      sum_lt_sum (fun w hw => hthree w (hnotR w hw)) ⟨v, hvR, by
        have := hthree v hv; omega⟩
    rw [sum_const, smul_eq_mul, hcompl] at hlt
    omega

/-- **Binary stemmata are the systems of `n - 3` splits.**  For `n ≥ 3`, a set `S` of non-trivial
sides away from `r` is a system of exactly `n - 3` sides if and only if it is the set of
non-trivial splits of a binary stemma (a tree on `Fin m` with the witnesses as leaves and every
unlabelled vertex of degree three). -/
theorem isBinary_iff_binary_tree (hn : 3 ≤ n) (r : Fin n) {S : Finset (Finset (Fin n))}
    (hS : ∀ A ∈ S, IsSide r A) :
    IsBinary r S ↔ ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (φ : Fin n → Fin m),
      IsBinaryTree T φ ∧ splitSides T φ = fam S := by
  constructor
  · intro hB
    obtain ⟨m, T, φ, hX, hfam⟩ := (buneman (by omega) r hS).mp hB.1
    exact ⟨m, T, φ, isBinaryTree_of_fam hn hB hX hfam, hfam⟩
  · rintro ⟨m, T, φ, hBT, hfam⟩
    obtain ⟨hbin, hfam'⟩ := binary_tree_splits hn r hBT
    have hSeq : nsplits T φ r = S := by
      ext B
      simp only [nsplits, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hB, hmem⟩
        exact (nontrivial_splits_of_tree hS hfam B hB).mp hmem
      · intro hBS
        exact ⟨hS B hBS, (nontrivial_splits_of_tree hS hfam B (hS B hBS)).mpr hBS⟩
    rwa [hSeq] at hbin

/-- **Binary rooted stemmata are binary trees with an outgroup.**  For `n ≥ 2`, a family `F` of
proper clusters on `Fin n` is the cluster set of a binary rooted stemma (`Rooted.IsBinR`) if and
only if, with an outgroup `Fin.last n` added, its images are the non-trivial splits of a binary
stemma on `Fin (n + 1)` (a tree with the witnesses as leaves and every unlabelled vertex of degree
three; the root is the attachment point of the outgroup). -/
theorem isBinR_iff_rooted_tree (hn : 2 ≤ n) {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, Rooted.IsCluster A) :
    Rooted.IsBinR F ↔ ∃ (m : ℕ) (G : SimpleGraph (Fin m)) (ψ : Fin (n + 1) → Fin m),
      IsBinaryTree G ψ ∧ splitSides G ψ = fam (F.map Rooted.outg) :=
  (Rooted.isBinR_iff_outgroup F).trans (isBinary_iff_binary_tree (by omega) _ fun A' hA' => by
    obtain ⟨A, hA, rfl⟩ := mem_map.mp hA'
    exact ⟨Rooted.last_notMem_outg A, (Rooted.nontriv_outg A).mpr (hF A hA)⟩)

end Stemma.BinaryTree
