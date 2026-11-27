/-
NP-hardness: Corollary 4.2 of the technical report (`cor:nphard`), with Turing-machine
polynomial time.

The complexity classes, polynomial-time many-one reductions and the NP-hardness of Independent Set
(Karp's reduction from SAT, and Cook–Levin) are those of `cslib-community/cslib-frontier`
(Apache-2.0), built on `leanprover/cslib`: `ComputableInPolyTime` is computability by a multi-tape
Turing machine in polynomial time with respect to explicit encodings into `List Bool`.

The target problem (`CompatibleSplits`) is the decision version of the maximum compatible set
problem, unit weights: an instance lists the witnesses, the candidate splits (each by one side) and
a number `m`; it is a yes-instance when it is well-formed (every candidate side is a set of the
listed witnesses, with at least two witnesses on each side) and `m` distinct candidate splits are
pairwise compatible.  Malformed instances are no-instances.

The reduction (`toSplits`) is the gadget of Theorem 4.1 written with list operations on natural
numbers: the private witnesses of `v` are `8v` and `8v + 1`; the four witnesses of an edge `e` are
`8 ⟨e⟩ + 2, …, 8 ⟨e⟩ + 5`, `⟨e⟩` the Cantor pairing of its endpoints; the auxiliary witnesses are `6`
and `7`.  Side 1 of `σ_v` holds the private witnesses of `v`, `8⟨e⟩ + 4, 8⟨e⟩ + 5` for the edges
leaving `v`, and `8⟨e⟩ + 3, 8⟨e⟩ + 5` for the edges entering `v`.

* `toSplits_polyTime`: the reduction is computable in polynomial time (by `fun_prop`, from the
  certified list and binary arithmetic operations of `cslib-frontier`).
* `toSplits_wf`: the instance is well-formed (`WF`: every candidate side is a set of the listed
  witnesses, with at least two witnesses on each side).
* `toSplits_mem_iff`: a graph has an independent set of `m` declared vertices iff the instance has
  `m` distinct pairwise compatible candidate splits.
* `CompatibleSplits_npHard`: the problem is NP-hard.

The theorem `Reduction.lean` states in the operation-count model (weights preserved, transfer of a
solver) remains, for the weighted problem; this file gives the unit-weight decision problem
NP-hardness in the sense of Turing machines.
-/
import CslibFrontier.Computability.Complexity.Problems.IndependentSet
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryPair

open Cslib.Complexity Turing.MultiTapeTM

namespace Stemma.NPHard

/-- An instance of the compatible-splits problem: witnesses, candidate splits (each by one side),
and a target number. -/
@[ext]
structure SplitInstance where
  univ : List ℕ
  splits : List (List ℕ)
  m : ℕ
  deriving DecidableEq

enc_structure encSplitInstance : SplitInstance where
  univ : (encList encNat),
  splits : (encList (encList encNat)),
  m : encNat

attribute [fun_prop] encSplitInstance_univ_polyTime encSplitInstance_splits_polyTime
  encSplitInstance_m_polyTime encSplitInstance_mk_polyTime

/-! ### The gadget, as list operations -/

/-- The code of the edge witness `t ∈ {2,3,4,5}` of the edge `e`. -/
def ew (t : ℕ) (e : ℕ × ℕ) : ℕ := 8 * Nat.pair e.1 e.2 + t

/-- The two private witnesses of `v`. -/
def privs (v : ℕ) : List ℕ := [8 * v, 8 * v + 1]

/-- Edge witnesses on side 1 of `v` as first endpoint. -/
def edgeA (p : List (ℕ × ℕ) × ℕ) : List ℕ :=
  (p.1.filter fun e => decide (e.1 = p.2)).flatMap fun e => [ew 4 e, ew 5 e]

/-- Edge witnesses on side 1 of `v` as second endpoint. -/
def edgeB (p : List (ℕ × ℕ) × ℕ) : List ℕ :=
  (p.1.filter fun e => decide (e.2 = p.2)).flatMap fun e => [ew 3 e, ew 5 e]

/-- Side 1 of the split of `v`. -/
def side (p : List (ℕ × ℕ) × ℕ) : List ℕ := privs p.2 ++ edgeA p ++ edgeB p

/-- The four witnesses of an edge. -/
def ew4 (e : ℕ × ℕ) : List ℕ := [ew 2 e, ew 3 e, ew 4 e, ew 5 e]

/-- All witnesses. -/
def witnesses (G : Graph) : List ℕ :=
  (G.vertices.flatMap privs ++ G.edges.flatMap ew4) ++ [6, 7]

/-- The candidate splits, one for each declared vertex. -/
def splitsOf (G : Graph) : List (List ℕ) := G.vertices.map fun v => side (G.edges, v)

/-- The reduction from Independent Set. -/
def toSplits (x : IndependentSetInstance) : SplitInstance :=
  ⟨witnesses x.graph, splitsOf x.graph, x.m⟩

/-! ### Polynomial time -/

@[fun_prop] theorem ew_polyTime (t : ℕ) :
    ComputableInPolyTime (ew t) (encPair encNat encNat) encNat := by
  unfold ew; fun_prop

@[fun_prop] theorem privs_polyTime : ComputableInPolyTime privs encNat (encList encNat) := by
  unfold privs; fun_prop

@[fun_prop] theorem edgeA_polyTime :
    ComputableInPolyTime edgeA (encPair (encList (encPair encNat encNat)) encNat)
      (encList encNat) := by
  unfold edgeA; fun_prop

@[fun_prop] theorem edgeB_polyTime :
    ComputableInPolyTime edgeB (encPair (encList (encPair encNat encNat)) encNat)
      (encList encNat) := by
  unfold edgeB; fun_prop

@[fun_prop] theorem side_polyTime :
    ComputableInPolyTime side (encPair (encList (encPair encNat encNat)) encNat)
      (encList encNat) := by
  unfold side; fun_prop

@[fun_prop] theorem ew4_polyTime : ComputableInPolyTime ew4 (encPair encNat encNat)
    (encList encNat) := by
  unfold ew4; fun_prop

@[fun_prop] theorem witnesses_polyTime : ComputableInPolyTime witnesses encGraph
    (encList encNat) := by
  unfold witnesses; fun_prop

@[fun_prop] theorem splitsOf_polyTime : ComputableInPolyTime splitsOf encGraph
    (encList (encList encNat)) := by
  unfold splitsOf; fun_prop

/-- **The reduction is computable in polynomial time.** -/
@[fun_prop] theorem toSplits_polyTime :
    ComputableInPolyTime toSplits encIndependentSetInstance encSplitInstance := by
  unfold toSplits; fun_prop

/-! ### The problem -/

/-- Compatibility of the splits `A | U \ A` and `B | U \ B` of the witnesses `U`. -/
def CompatU (U A B : Finset ℕ) : Prop :=
  A ∩ B = ∅ ∨ A ∩ (U \ B) = ∅ ∨ (U \ A) ∩ B = ∅ ∨ (U \ A) ∩ (U \ B) = ∅

/-- A well-formed candidate split of the witnesses `U`, given by one side `l`: `l` is a set of
witnesses, and each side has at least two witnesses (a non-trivial split, as in the report). -/
def WFsplit (U l : List ℕ) : Prop :=
  l.toFinset ⊆ U.toFinset ∧ 2 ≤ l.toFinset.card ∧ 2 ≤ (U.toFinset \ l.toFinset).card

/-- A well-formed instance: every candidate is a well-formed split of the witnesses. -/
def WF (x : SplitInstance) : Prop := ∀ l ∈ x.splits, WFsplit x.univ l

/-- The instance has `m` distinct candidate splits that are pairwise compatible. -/
def HasCompatible (x : SplitInstance) : Prop :=
  ∃ S : Finset (Finset ℕ), S.card = x.m ∧ (∀ A ∈ S, ∃ l ∈ x.splits, l.toFinset = A) ∧
    ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ≠ x.univ.toFinset \ B ∧ CompatU x.univ.toFinset A B

/-- **Compatible splits**: the well-formed instances (`WF`: every candidate side is a set of the
listed witnesses, with at least two witnesses on each side) with `m` distinct candidate splits that
are pairwise compatible (`HasCompatible`).  This is the decision version of the maximum-weight
compatible set problem with unit weights, i.e. of MWIS on the split-conflict graph of the
candidates.  Malformed instances (a candidate outside the witnesses, or a trivial split) are
no-instances. -/
def CompatibleSplits : Set SplitInstance := {x | WF x ∧ HasCompatible x}

/-- A malformed instance (a candidate side `{99}` outside the witnesses
`{0, 1, 2, 3}`) is a no-instance. -/
theorem malformed_not_mem : (⟨[0, 1, 2, 3], [[99]], 1⟩ : SplitInstance) ∉ CompatibleSplits := by
  rintro ⟨h, -⟩
  have := (h [99] (by simp)).1 (by simp : 99 ∈ [99].toFinset)
  simp at this

/-! ### Reading the witnesses -/

lemma mem_side {E : List (ℕ × ℕ)} {v w : ℕ} :
    w ∈ side (E, v) ↔ w = 8 * v ∨ w = 8 * v + 1 ∨
      (∃ e ∈ E, e.1 = v ∧ (w = ew 4 e ∨ w = ew 5 e)) ∨
      (∃ e ∈ E, e.2 = v ∧ (w = ew 3 e ∨ w = ew 5 e)) := by
  simp only [side, privs, edgeA, edgeB, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq, List.not_mem_nil, or_false]
  aesop

/-- A witness on side 1 of `v` is a private witness of `v`, or an edge witness of an edge with
endpoint `v`, its residue saying which endpoint. -/
lemma classify {E : List (ℕ × ℕ)} {v w : ℕ} (h : w ∈ side (E, v)) :
    (w / 8 = v ∧ w % 8 ≤ 1) ∨ ∃ e ∈ E, w / 8 = Nat.pair e.1 e.2 ∧
      ((w % 8 = 4 ∧ e.1 = v) ∨ (w % 8 = 3 ∧ e.2 = v) ∨ (w % 8 = 5 ∧ (e.1 = v ∨ e.2 = v))) := by
  rcases mem_side.mp h with h | h | ⟨e, he, h1, h2⟩ | ⟨e, he, h1, h2⟩
  · left; omega
  · left; omega
  · right
    refine ⟨e, he, ?_⟩
    simp only [ew] at h2
    rcases h2 with h2 | h2
    · exact ⟨by omega, Or.inl ⟨by omega, h1⟩⟩
    · exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inl h1⟩)⟩
  · right
    refine ⟨e, he, ?_⟩
    simp only [ew] at h2
    rcases h2 with h2 | h2
    · exact ⟨by omega, Or.inr (Or.inl ⟨by omega, h1⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inr h1⟩)⟩

lemma pair_inj {e e' : ℕ × ℕ} (h : Nat.pair e.1 e.2 = Nat.pair e'.1 e'.2) : e = e' := by
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext h1 h2

/-- The finset of side 1 of `v`. -/
def sideF (E : List (ℕ × ℕ)) (v : ℕ) : Finset ℕ := (side (E, v)).toFinset

lemma mem_sideF {E : List (ℕ × ℕ)} {v w : ℕ} : w ∈ sideF E v ↔ w ∈ side (E, v) := by
  simp [sideF]

lemma priv_mem (E : List (ℕ × ℕ)) (v : ℕ) : 8 * v ∈ sideF E v :=
  mem_sideF.mpr (mem_side.mpr (Or.inl rfl))

lemma six_not_mem (E : List (ℕ × ℕ)) (v : ℕ) : 6 ∉ sideF E v := by
  intro h
  rcases classify (mem_sideF.mp h) with ⟨-, h⟩ | ⟨e, -, -, h⟩
  · omega
  · omega

lemma seven_not_mem (E : List (ℕ × ℕ)) (v : ℕ) : 7 ∉ sideF E v := by
  intro h
  rcases classify (mem_sideF.mp h) with ⟨-, h⟩ | ⟨e, -, -, h⟩
  · omega
  · omega

lemma sideF_inj {E : List (ℕ × ℕ)} {u v : ℕ} (h : sideF E u = sideF E v) : u = v := by
  have := priv_mem E u
  rw [h] at this
  rcases classify (mem_sideF.mp this) with ⟨h1, -⟩ | ⟨e, -, -, h2⟩
  · omega
  · omega

/-- Non-adjacent distinct vertices have disjoint sides. -/
lemma sideF_disjoint {G : Graph} {u v : ℕ} (huv : u ≠ v) (hna : ¬ G.toSimpleGraph.Adj u v) :
    sideF G.edges u ∩ sideF G.edges v = ∅ := by
  ext w
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro hu hv
  rcases classify (mem_sideF.mp hu) with ⟨h1, h2⟩ | ⟨e, he, h1, h2⟩ <;>
    rcases classify (mem_sideF.mp hv) with ⟨h3, h4⟩ | ⟨e', he', h3, h4⟩
  · omega
  · omega
  · omega
  · have hee : e = e' := pair_inj (h1.symm.trans h3)
    subst hee
    apply hna
    rw [Graph.toSimpleGraph_adj]
    refine ⟨huv, ?_⟩
    obtain ⟨a, b⟩ := e
    simp only at h2 h4
    have hu' : a = u ∨ b = u := by omega
    have hv' : a = v ∨ b = v := by omega
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact absurd rfl huv
    · exact Or.inl he
    · exact Or.inr he
    · exact absurd rfl huv

lemma side_sub {G : Graph} {v : ℕ} (hv : v ∈ G.vertices) :
    sideF G.edges v ⊆ (witnesses G).toFinset := by
  intro w hw
  simp only [witnesses, List.mem_toFinset, List.mem_append, List.mem_flatMap, privs, ew4,
    List.mem_cons, List.not_mem_nil, or_false]
  rcases mem_side.mp (mem_sideF.mp hw) with h | h | ⟨e, he, -, h⟩ | ⟨e, he, -, h⟩
  · exact Or.inl (Or.inl ⟨v, hv, Or.inl h⟩)
  · exact Or.inl (Or.inl ⟨v, hv, Or.inr h⟩)
  · exact Or.inl (Or.inr ⟨e, he, by tauto⟩)
  · exact Or.inl (Or.inr ⟨e, he, by tauto⟩)

/-- Adjacent vertices have conflicting splits. -/
lemma sideF_conflict {G : Graph} {u v : ℕ} (hadj : G.toSimpleGraph.Adj u v) :
    ¬ CompatU (witnesses G).toFinset (sideF G.edges u) (sideF G.edges v) := by
  obtain ⟨huv, he⟩ := Graph.toSimpleGraph_adj.mp hadj
  set U := (witnesses G).toFinset
  have inU : ∀ e ∈ G.edges, ∀ t, 2 ≤ t → t ≤ 5 → ew t e ∈ U := by
    intro e he t h1 h2
    simp only [U, witnesses, List.mem_toFinset, List.mem_append, List.mem_flatMap, ew4,
      List.mem_cons, List.not_mem_nil, or_false]
    refine Or.inl (Or.inr ⟨e, he, ?_⟩)
    interval_cases t <;> simp
  -- for an edge `e` from `a` to `b`, the witness `ew t e` lies on side `x` exactly as prescribed
  have notin : ∀ {e : ℕ × ℕ} {x t}, (t = 2 ∨ (t = 4 ∧ e.1 ≠ x) ∨ (t = 3 ∧ e.2 ≠ x)) →
      ew t e ∉ sideF G.edges x := by
    intro e x t ht h
    rcases classify (mem_sideF.mp h) with ⟨h1, h2⟩ | ⟨e', -, h1, h2⟩
    · simp only [ew] at h1 h2; omega
    · have h1' : Nat.pair e.1 e.2 = Nat.pair e'.1 e'.2 := by simp only [ew] at h1; omega
      have := pair_inj h1'
      subst this
      simp only [ew] at h2
      rcases ht with rfl | ⟨rfl, h3⟩ | ⟨rfl, h3⟩ <;> omega
  have mem1 : ∀ {e : ℕ × ℕ}, e ∈ G.edges → ew 4 e ∈ sideF G.edges e.1 ∧
      ew 5 e ∈ sideF G.edges e.1 := fun he =>
    ⟨mem_sideF.mpr (mem_side.mpr (Or.inr (Or.inr (Or.inl ⟨_, he, rfl, Or.inl rfl⟩)))),
      mem_sideF.mpr (mem_side.mpr (Or.inr (Or.inr (Or.inl ⟨_, he, rfl, Or.inr rfl⟩))))⟩
  have mem2 : ∀ {e : ℕ × ℕ}, e ∈ G.edges → ew 3 e ∈ sideF G.edges e.2 ∧
      ew 5 e ∈ sideF G.edges e.2 := fun he =>
    ⟨mem_sideF.mpr (mem_side.mpr (Or.inr (Or.inr (Or.inr ⟨_, he, rfl, Or.inl rfl⟩)))),
      mem_sideF.mpr (mem_side.mpr (Or.inr (Or.inr (Or.inr ⟨_, he, rfl, Or.inr rfl⟩))))⟩
  have ne : ∀ (X : Finset ℕ) (w : ℕ), w ∈ X → X ≠ ∅ := fun X w hw h => by
    rw [h] at hw; simp at hw
  unfold CompatU
  rcases he with he | he
  · -- the edge `(u, v)`
    obtain ⟨a4, a5⟩ := mem1 he
    obtain ⟨b3, b5⟩ := mem2 he
    simp only at a4 a5 b3 b5
    refine not_or.mpr ⟨ne _ (ew 5 (u, v)) ?_, not_or.mpr ⟨ne _ (ew 4 (u, v)) ?_,
      not_or.mpr ⟨ne _ (ew 3 (u, v)) ?_, ne _ (ew 2 (u, v)) ?_⟩⟩⟩
    · exact Finset.mem_inter.mpr ⟨a5, b5⟩
    · exact Finset.mem_inter.mpr ⟨a4, Finset.mem_sdiff.mpr ⟨inU _ he 4 (by norm_num) (by norm_num),
        notin (Or.inr (Or.inl ⟨rfl, huv⟩))⟩⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨inU _ he 3 (by norm_num) (by norm_num),
        notin (Or.inr (Or.inr ⟨rfl, Ne.symm huv⟩))⟩, b3⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨inU _ he 2 le_rfl (by norm_num),
        notin (Or.inl rfl)⟩, Finset.mem_sdiff.mpr ⟨inU _ he 2 le_rfl (by norm_num),
        notin (Or.inl rfl)⟩⟩
  · -- the edge `(v, u)`
    obtain ⟨a4, a5⟩ := mem1 he
    obtain ⟨b3, b5⟩ := mem2 he
    simp only at a4 a5 b3 b5
    refine not_or.mpr ⟨ne _ (ew 5 (v, u)) ?_, not_or.mpr ⟨ne _ (ew 3 (v, u)) ?_,
      not_or.mpr ⟨ne _ (ew 4 (v, u)) ?_, ne _ (ew 2 (v, u)) ?_⟩⟩⟩
    · exact Finset.mem_inter.mpr ⟨b5, a5⟩
    · exact Finset.mem_inter.mpr ⟨b3, Finset.mem_sdiff.mpr ⟨inU _ he 3 (by norm_num) (by norm_num),
        notin (Or.inr (Or.inr ⟨rfl, huv⟩))⟩⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨inU _ he 4 (by norm_num) (by norm_num),
        notin (Or.inr (Or.inl ⟨rfl, Ne.symm huv⟩))⟩, a4⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨inU _ he 2 le_rfl (by norm_num),
        notin (Or.inl rfl)⟩, Finset.mem_sdiff.mpr ⟨inU _ he 2 le_rfl (by norm_num),
        notin (Or.inl rfl)⟩⟩

lemma sideF_not_compl {G : Graph} (u v : ℕ) :
    sideF G.edges u ≠ (witnesses G).toFinset \ sideF G.edges v := by
  intro h
  have h6 : 6 ∈ (witnesses G).toFinset \ sideF G.edges v :=
    Finset.mem_sdiff.mpr ⟨by simp [witnesses], six_not_mem _ _⟩
  rw [← h] at h6
  exact six_not_mem _ _ h6

/-- **The reduction lands in the well-formed instances.**  Each candidate side holds the two
private witnesses of its vertex, and its complement the auxiliary witnesses `6` and `7`. -/
theorem toSplits_wf (x : IndependentSetInstance) : WF (toSplits x) := by
  intro l hl
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
  have hU : ∀ w, w ∈ [6, 7] → w ∈ (witnesses x.graph).toFinset := fun w hw => by
    simp only [witnesses, List.mem_toFinset, List.mem_append]; exact Or.inr hw
  refine ⟨side_sub hv, ?_, ?_⟩
  · have hsub : ({8 * v, 8 * v + 1} : Finset ℕ) ⊆ sideF x.graph.edges v := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact priv_mem _ _
      · rw [Finset.mem_singleton.mp hw]
        exact mem_sideF.mpr (mem_side.mpr (Or.inr (Or.inl rfl)))
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (by omega)] at this
    exact this
  · have hsub : ({6, 7} : Finset ℕ) ⊆ (witnesses x.graph).toFinset \ sideF x.graph.edges v := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_sdiff.mpr ⟨hU 6 (by simp), six_not_mem _ _⟩
      · rw [Finset.mem_singleton.mp hw]
        exact Finset.mem_sdiff.mpr ⟨hU 7 (by simp), seven_not_mem _ _⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (by omega)] at this
    exact this

/-- **The reduction is correct.**  A graph has an independent set of `m` declared vertices iff the
instance (always well-formed) has `m` distinct, pairwise compatible candidate splits. -/
theorem toSplits_mem_iff (x : IndependentSetInstance) :
    x ∈ IndependentSet ↔ toSplits x ∈ CompatibleSplits := by
  rw [show toSplits x ∈ CompatibleSplits ↔ HasCompatible (toSplits x) from
    and_iff_right (toSplits_wf x)]
  obtain ⟨G, m⟩ := x
  rw [mem_IndependentSet_iff_mk]
  simp only [toSplits, HasCompatible, splitsOf, List.mem_map]
  constructor
  · rintro ⟨S, hSV, hS⟩
    refine ⟨S.image (sideF G.edges), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ fun u v h => sideF_inj h]
      exact hS.card_eq
    · intro A hA
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
      exact ⟨side (G.edges, v), ⟨v, hSV v hv, rfl⟩, rfl⟩
    · intro A hA B hB hAB
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
      have huv : u ≠ v := fun h => hAB (h ▸ rfl)
      refine ⟨sideF_not_compl u v, Or.inl ?_⟩
      exact sideF_disjoint huv (hS.isIndepSet hu hv huv)
  · rintro ⟨F, hFm, hFs, hFc⟩
    set T := G.vertices.toFinset.filter fun v => sideF G.edges v ∈ F
    have himg : T.image (sideF G.edges) = F := by
      ext A
      simp only [Finset.mem_image, T, Finset.mem_filter, List.mem_toFinset]
      constructor
      · rintro ⟨v, ⟨-, hv⟩, rfl⟩; exact hv
      · intro hA
        obtain ⟨l, ⟨v, hv, rfl⟩, hl⟩ := hFs A hA
        have hl' : sideF G.edges v = A := hl
        exact ⟨v, ⟨hv, hl'.symm ▸ hA⟩, hl'⟩
    refine ⟨T, fun v hv => List.mem_toFinset.mp (Finset.mem_filter.mp hv).1, ?_, ?_⟩
    · intro u hu v hv huv hadj
      have hu' := (Finset.mem_filter.mp hu).2
      have hv' := (Finset.mem_filter.mp hv).2
      have hne : sideF G.edges u ≠ sideF G.edges v := fun h => huv (sideF_inj h)
      exact sideF_conflict hadj (hFc _ hu' _ hv' hne).2
    · rw [← hFm, ← himg, Finset.card_image_of_injective _ fun u v h => sideF_inj h]

/-- **Corollary 4.2 (`cor:nphard`).**  Independent Set reduces in polynomial time to the
compatible-splits problem. -/
theorem polyTimeReducible_IndependentSet_CompatibleSplits :
    PolyTimeReducible encIndependentSetInstance encSplitInstance IndependentSet
      CompatibleSplits :=
  ⟨toSplits, by fun_prop, toSplits_mem_iff⟩

/-- **Corollary 4.2 (`cor:nphard`).**  The maximum compatible set problem on split-conflict
instances (here its decision version, unit weights) is NP-hard, when the number of witnesses is
part of the input: Independent Set, NP-hard by Karp's theorem (in `cslib-frontier`), reduces to
it in polynomial time. -/
theorem CompatibleSplits_npHard : NPHard encSplitInstance CompatibleSplits :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_CompatibleSplits

end Stemma.NPHard
