/-
Five witnesses (Proposition 9.3 of the technical report, `prop:five`).

On five witnesses every non-trivial split has a side of two witnesses, so the ten non-trivial
splits are the ten pairs `{a, b}`, and two of them conflict exactly when the pairs share a witness:
the adjacency of the line graph of `K₅`.  On `n ≥ 5` witnesses the pairs inside five fixed
witnesses conflict by the same rule, so the conflict graph contains this graph as an induced
subgraph, and in particular an induced 4-cycle and an induced 5-cycle.

Mathlib has no notion of chordal or perfect graph; they are defined here for `SimpleGraph`
(`Chordal`: no induced cycle of length at least four, the usual equivalent of "every cycle of
length at least four has a chord"; `Perfect`: every induced subgraph has clique number equal to
its chromatic number).  The conflict graph of the non-trivial splits is `conflictGraph r`, on the
sides away from a reference witness `r` (one vertex per split), adjacent when distinct and in
conflict.  For every `n ≥ 5` it is neither chordal (`conflict_not_chordal`, from the induced
4-cycle) nor perfect (`conflict_not_perfect`, from the induced 5-cycle, of clique number `2` and
chromatic number `3`); on five witnesses its ten vertices are all the non-trivial splits.
The identification with Mathlib's `SimpleGraph.lineGraph ⊤` is not formalised: the line graph of
`K₅` appears here through its adjacency on pairs, "distinct and sharing a vertex".
-/
import Mathlib
import StemmaLean.Splits

open Finset

namespace Stemma.Five

open Splits

variable {n : ℕ}

/-- **Two pairs conflict iff they share a witness** (on `n ≥ 4` witnesses, distinct pairs). -/
theorem pair_conflict_iff (hn : 4 ≤ n) {A B : Finset (Fin n)} (hA : A.card = 2)
    (hB : B.card = 2) (hAB : A ≠ B) : ¬ Compat A B ↔ (A ∩ B).Nonempty := by
  constructor
  · intro hc
    by_contra h
    exact hc (Or.inl (not_nonempty_iff_eq_empty.mp h))
  · rintro ⟨x, hx⟩ hc
    have sub : ∀ X Y : Finset (Fin n), X ∩ Yᶜ = ∅ → X ⊆ Y := fun X Y h y hy => by
      by_contra hyY
      have : y ∈ X ∩ Yᶜ := by simp [hy, hyY]
      rw [h] at this; simp at this
    rcases hc with h | h | h | h
    · rw [h] at hx; simp at hx
    · exact hAB (eq_of_subset_of_card_le (sub A B h) (by omega))
    · rw [inter_comm] at h
      exact hAB (eq_of_subset_of_card_le (sub B A h) (by omega)).symm
    · have hU : A ∪ B = univ := by
        ext y; simp only [mem_union, mem_univ, iff_true]
        by_contra hy; push Not at hy
        have : y ∈ Aᶜ ∩ Bᶜ := by simp [hy.1, hy.2]
        rw [h] at this; simp at this
      have h1 := card_union_add_card_inter A B
      have h2 : 1 ≤ (A ∩ B).card := card_pos.mpr ⟨x, hx⟩
      rw [hU, card_univ, Fintype.card_fin] at h1
      omega

/-- A pair is a non-trivial split on `n ≥ 4` witnesses. -/
lemma pair_nontriv (hn : 4 ≤ n) {A : Finset (Fin n)} (hA : A.card = 2) : Nontriv A :=
  ⟨hA.ge, by rw [card_compl, Fintype.card_fin, hA]; omega⟩

/-- **Proposition 9.3 (`prop:five`), five witnesses: the splits are the pairs.**  Every
non-trivial split on five witnesses has a side with exactly two witnesses; distinct pairs give
distinct splits (as unordered bipartitions); there are ten pairs. -/
theorem five_splits_are_pairs :
    (∀ A : Finset (Fin 5), Nontriv A → A.card = 2 ∨ Aᶜ.card = 2) ∧
    (∀ A B : Finset (Fin 5), A.card = 2 → B.card = 2 → A ≠ B → A ≠ Bᶜ) ∧
    ((univ : Finset (Fin 5)).powersetCard 2).card = 10 := by
  refine ⟨fun A hA => ?_, fun A B hA hB _ e => ?_, by rw [card_powersetCard]; rfl⟩
  · have := hA.1; have := hA.2
    rw [card_compl, Fintype.card_fin] at this ⊢
    have := card_le_univ A; simp at this
    omega
  · have := congrArg card e
    rw [card_compl, Fintype.card_fin, hA, hB] at this
    omega

/-- **Proposition 9.3 (`prop:five`), five witnesses: the conflict graph is the line graph of
`K₅`.**  Two distinct pairs of witnesses conflict exactly when they share a witness. -/
theorem five_conflict_lineGraph {A B : Finset (Fin 5)} (hA : A.card = 2) (hB : B.card = 2)
    (hAB : A ≠ B) : ¬ Compat A B ↔ (A ∩ B).Nonempty :=
  pair_conflict_iff (by norm_num) hA hB hAB

/-- **Proposition 9.3 (`prop:five`), `n ≥ 5`: induced copy.**  Embedding five witnesses into `n`,
two distinct pairs of them conflict, as splits on `n` witnesses, exactly when they share a witness:
the conflict graph of all non-trivial splits on `n ≥ 5` witnesses contains the line graph of `K₅`
as an induced subgraph. -/
theorem induced_lineGraph (hn : 5 ≤ n) (e : Fin 5 ↪ Fin n) {A B : Finset (Fin 5)}
    (hA : A.card = 2) (hB : B.card = 2) (hAB : A ≠ B) :
    ¬ Compat (A.map e) (B.map e) ↔ (A ∩ B).Nonempty := by
  rw [pair_conflict_iff (by omega) (by simp [hA]) (by simp [hB])
    (fun h => hAB (map_injective e h)), ← map_inter, map_nonempty]

/-- The pair `{i, j}` among the first five witnesses. -/
def P (hn : 5 ≤ n) (i j : Fin 5) : Finset (Fin n) :=
  ({i, j} : Finset (Fin 5)).map (Fin.castLEEmb hn)

lemma P_conflict (hn : 5 ≤ n) {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i, j} : Finset (Fin 5)) ≠ {k, l}) :
    ¬ Compat (P hn i j) (P hn k l) ↔ (({i, j} : Finset (Fin 5)) ∩ {k, l}).Nonempty :=
  induced_lineGraph hn _ (card_pair hij) (card_pair hkl) hne

/-- **Proposition 9.3 (`prop:five`): an induced 4-cycle** `12, 23, 34, 41` (witnesses `0..3`):
consecutive pairs conflict, opposite pairs are compatible.  So the conflict graph is not chordal. -/
theorem induced_four_cycle (hn : 5 ≤ n) :
    let C : Fin 4 → Finset (Fin n) := ![P hn 0 1, P hn 1 2, P hn 2 3, P hn 3 0]
    (∀ i : Fin 4, ¬ Compat (C i) (C (i + 1))) ∧ (∀ i : Fin 4, Compat (C i) (C (i + 2))) := by
  intro C
  constructor <;> intro i <;> fin_cases i
  all_goals first
    | exact (P_conflict hn (by decide) (by decide) (by decide)).mpr (by decide)
    | exact not_not.mp ((P_conflict hn (by decide) (by decide) (by decide)).not.mpr
        (by decide))

/-- **Proposition 9.3 (`prop:five`): an induced 5-cycle** `12, 23, 34, 45, 51`: consecutive pairs
conflict, the others are compatible.  So the conflict graph is not perfect. -/
theorem induced_five_cycle (hn : 5 ≤ n) :
    let C : Fin 5 → Finset (Fin n) := ![P hn 0 1, P hn 1 2, P hn 2 3, P hn 3 4, P hn 4 0]
    (∀ i : Fin 5, ¬ Compat (C i) (C (i + 1))) ∧
      (∀ i : Fin 5, Compat (C i) (C (i + 2)) ∧ Compat (C i) (C (i + 3))) := by
  intro C
  refine ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩ <;> fin_cases i
  all_goals first
    | exact (P_conflict hn (by decide) (by decide) (by decide)).mpr (by decide)
    | exact not_not.mp ((P_conflict hn (by decide) (by decide) (by decide)).not.mpr
        (by decide))


/-! ### Chordal and perfect graphs -/

section graphs

variable {V : Type*} (G : SimpleGraph V)

/-- `f` is an induced cycle of length `m`: injective, and `f i`, `f j` are adjacent exactly when
`i`, `j` are consecutive modulo `m`. -/
def IsInducedCycle {m : ℕ} [NeZero m] (f : Fin m → V) : Prop :=
  Function.Injective f ∧ ∀ i j, G.Adj (f i) (f j) ↔ (j = i + 1 ∨ i = j + 1)

/-- A chordal graph: no induced cycle of length at least four (every cycle of length at least
four has a chord). -/
def Chordal : Prop := ∀ (m : ℕ) [NeZero m], 4 ≤ m → ∀ f : Fin m → V, ¬ IsInducedCycle G f

/-- A perfect graph: every induced subgraph has clique number equal to its chromatic number. -/
def Perfect : Prop :=
  ∀ s : Set V, ((G.induce s).cliqueNum : ℕ∞) = (G.induce s).chromaticNumber

variable {G}

/-- A graph with an induced 4-cycle is not chordal. -/
theorem not_chordal_of_four_cycle {f : Fin 4 → V} (h : IsInducedCycle G f) : ¬ Chordal G :=
  fun hc => hc 4 le_rfl f h

/-- A graph with an induced 5-cycle is not perfect: on the five vertices the clique number is at
most `2` and the graph is not `2`-colourable. -/
theorem not_perfect_of_five_cycle {f : Fin 5 → V} (h : IsInducedCycle G f) : ¬ Perfect G := by
  intro hP
  set s := Set.range f
  set H := G.induce s
  have hadj : ∀ i j, H.Adj ⟨f i, i, rfl⟩ ⟨f j, j, rfl⟩ ↔ (j = i + 1 ∨ i = j + 1) := fun i j => by
    simp only [H, SimpleGraph.comap_adj, Function.Embedding.subtype_apply]; exact h.2 i j
  -- the clique number is at most `2`
  have hcl : H.cliqueNum ≤ 2 := by
    obtain ⟨t, ht⟩ := H.exists_isNClique_cliqueNum
    by_contra hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      two_lt_card_iff.mp (by rw [ht.2]; omega : 2 < t.card)
    obtain ⟨i, hi⟩ := a.2; obtain ⟨j, hj⟩ := b.2; obtain ⟨l, hl⟩ := c.2
    have ea : a = ⟨f i, i, rfl⟩ := Subtype.ext hi.symm
    have eb : b = ⟨f j, j, rfl⟩ := Subtype.ext hj.symm
    have ec : c = ⟨f l, l, rfl⟩ := Subtype.ext hl.symm
    have h1 := ht.1 ha hb hab; have h2 := ht.1 ha hc hac; have h3 := ht.1 hb hc hbc
    rw [ea, eb, hadj] at h1; rw [ea, ec, hadj] at h2; rw [eb, ec, hadj] at h3
    have hij : i ≠ j := fun e => hab (by rw [ea, eb, e])
    have hil : i ≠ l := fun e => hac (by rw [ea, ec, e])
    have hjl : j ≠ l := fun e => hbc (by rw [eb, ec, e])
    have key : ∀ i j l : Fin 5, (j = i + 1 ∨ i = j + 1) → (l = i + 1 ∨ i = l + 1) →
        (l = j + 1 ∨ j = l + 1) → i ≠ j → i ≠ l → j ≠ l → False := by decide
    exact key i j l h1 h2 h3 hij hil hjl
  -- the graph is not `2`-colourable
  have hcol : ¬ H.Colorable 2 := by
    rintro ⟨C⟩
    have hv : ∀ i : Fin 5, C ⟨f i, i, rfl⟩ ≠ C ⟨f (i + 1), i + 1, rfl⟩ := fun i =>
      C.valid ((hadj i (i + 1)).mpr (Or.inl rfl))
    have key : ∀ g : Fin 5 → Fin 2, ¬ ∀ i, g i ≠ g (i + 1) := by decide
    exact key (fun i => C ⟨f i, i, rfl⟩) hv
  have e := hP s
  have hle : H.chromaticNumber ≤ (2 : ℕ) := by
    rw [← e]; exact_mod_cast hcl
  exact hcol (SimpleGraph.chromaticNumber_le_iff_colorable.mp hle)

end graphs

/-! ### The conflict graph of the non-trivial splits -/

/-- The conflict graph: one vertex per non-trivial split (its side away from `r`), two splits
adjacent when distinct and in conflict. -/
def conflictGraph (r : Fin n) : SimpleGraph {A : Finset (Fin n) // IsSide r A} where
  Adj A B := A ≠ B ∧ ¬ Compat A.1 B.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hc => h.2 (compat_symm hc)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The side of `A | Aᶜ` away from `r`. -/
def orient (r : Fin n) (A : Finset (Fin n)) : Finset (Fin n) := if r ∈ A then Aᶜ else A

lemma compat_compl_left {A C : Finset (Fin n)} : Compat Aᶜ C ↔ Compat A C := by
  unfold Compat; rw [compl_compl]; tauto

lemma compat_orient (r : Fin n) (A C : Finset (Fin n)) :
    Compat (orient r A) (orient r C) ↔ Compat A C := by
  unfold orient
  have hr : ∀ X Y : Finset (Fin n), Compat X Yᶜ ↔ Compat X Y := fun X Y =>
    ⟨fun h => compat_symm (compat_compl_left.mp (compat_symm h)),
      fun h => compat_symm (compat_compl_left.mpr (compat_symm h))⟩
  split_ifs
  · rw [compat_compl_left, hr]
  · rw [compat_compl_left]
  · rw [hr]
  · rfl

lemma isSide_orient (r : Fin n) {A : Finset (Fin n)} (hA : Nontriv A) : IsSide r (orient r A) := by
  unfold orient
  split_ifs with h
  · exact ⟨fun h' => (mem_compl.mp h') h, hA.2, by rw [compl_compl]; exact hA.1⟩
  · exact ⟨h, hA⟩

/-- The vertex of the conflict graph given by a pair among the first five witnesses. -/
def vx (hn : 5 ≤ n) (r : Fin n) (p : Finset (Fin 5)) (hp : p.card = 2) :
    {A : Finset (Fin n) // IsSide r A} :=
  ⟨orient r (p.map (Fin.castLEEmb hn)), isSide_orient r (pair_nontriv (by omega) (by simp [hp]))⟩

lemma vx_adj (hn : 5 ≤ n) (r : Fin n) {p q : Finset (Fin 5)} (hp : p.card = 2)
    (hq : q.card = 2) :
    (conflictGraph r).Adj (vx hn r p hp) (vx hn r q hq) ↔ p ≠ q ∧ (p ∩ q).Nonempty := by
  by_cases hpq : p = q
  · subst hpq; simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact (conflictGraph r).irrefl
  · have hc : ¬ Compat (vx hn r p hp).1 (vx hn r q hq).1 ↔ (p ∩ q).Nonempty := by
      simp only [vx]
      rw [compat_orient]; exact induced_lineGraph hn _ hp hq hpq
    constructor
    · rintro ⟨-, h⟩; exact ⟨hpq, hc.mp h⟩
    · rintro ⟨-, h⟩
      refine ⟨fun e => ?_, hc.mpr h⟩
      exact (hc.mpr h) (e ▸ compat_self _)

/-- Distinct pairs give distinct vertices. -/
lemma vx_inj (hn : 5 ≤ n) (r : Fin n) {p q : Finset (Fin 5)} (hp : p.card = 2)
    (hq : q.card = 2) (e : vx hn r p hp = vx hn r q hq) : p = q := by
  have e1 : orient r (p.map (Fin.castLEEmb hn)) = orient r (q.map (Fin.castLEEmb hn)) :=
    congrArg Subtype.val e
  have cp : (p.map (Fin.castLEEmb hn)).card = 2 := by simp [hp]
  have cq : (q.map (Fin.castLEEmb hn)).card = 2 := by simp [hq]
  have hcc : ∀ X : Finset (Fin n), X.card = 2 → Xᶜ.card = n - 2 := fun X hX => by
    rw [card_compl, Fintype.card_fin, hX]
  unfold orient at e1
  apply map_injective (Fin.castLEEmb hn)
  split_ifs at e1
  · exact compl_injective e1
  · have := hcc _ cp; rw [e1, cq] at this; omega
  · have := hcc _ cq; rw [← e1, cp] at this; omega
  · exact e1

/-- **Proposition 9.3 (`prop:five`): the conflict graph is not chordal**, for every `n ≥ 5`. -/
theorem conflict_not_chordal (hn : 5 ≤ n) (r : Fin n) : ¬ Chordal (conflictGraph r) := by
  let pr : Fin 4 → Finset (Fin 5) := ![{0, 1}, {1, 2}, {2, 3}, {3, 0}]
  have hpr : ∀ i, (pr i).card = 2 := by decide
  let f : Fin 4 → {A : Finset (Fin n) // IsSide r A} := fun i => vx hn r (pr i) (hpr i)
  have hadj : ∀ i j, (conflictGraph r).Adj (f i) (f j) ↔ (j = i + 1 ∨ i = j + 1) := by
    intro i j
    rw [vx_adj]
    revert i j; decide
  have hinj : Function.Injective f := fun i j e => by
    have key : ∀ i j : Fin 4, (![{0, 1}, {1, 2}, {2, 3}, {3, 0}] : Fin 4 → Finset (Fin 5)) i =
        ![{0, 1}, {1, 2}, {2, 3}, {3, 0}] j → i = j := by decide
    exact key i j (vx_inj hn r (hpr i) (hpr j) e)
  exact not_chordal_of_four_cycle ⟨hinj, hadj⟩

/-- **Proposition 9.3 (`prop:five`): the conflict graph is not perfect**, for every `n ≥ 5`. -/
theorem conflict_not_perfect (hn : 5 ≤ n) (r : Fin n) : ¬ Perfect (conflictGraph r) := by
  let pr : Fin 5 → Finset (Fin 5) := ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}]
  have hpr : ∀ i, (pr i).card = 2 := by decide
  let f : Fin 5 → {A : Finset (Fin n) // IsSide r A} := fun i => vx hn r (pr i) (hpr i)
  have hadj : ∀ i j, (conflictGraph r).Adj (f i) (f j) ↔ (j = i + 1 ∨ i = j + 1) := by
    intro i j
    rw [vx_adj]
    revert i j; decide
  have hinj : Function.Injective f := fun i j e => by
    have key : ∀ i j : Fin 5,
        (![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}] : Fin 5 → Finset (Fin 5)) i =
          ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}] j → i = j := by decide
    exact key i j (vx_inj hn r (hpr i) (hpr j) e)
  exact not_perfect_of_five_cycle ⟨hinj, hadj⟩


/-- On five witnesses the conflict graph has ten vertices: all the non-trivial splits. -/
theorem card_conflict_five :
    (univ.filter fun A : Finset (Fin 5) => 4 ∉ A ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card).card = 10 := by
  decide

end Stemma.Five
