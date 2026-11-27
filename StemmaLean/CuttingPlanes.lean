/-
Exact selection by cutting planes (Theorem 5.3 of the technical report, `thm:cutting`).

The candidates are a finite set `C` of partial splits with real weights `c`.  A master problem,
for a set `cuts` of families, maximises the weight over the subfamilies of `C` that are pairwise
overlap-compatible and contain no cut.  The procedure: solve the master problem; if its optimum
`S` is jointly completable, stop; otherwise add a non-completable `K ⊆ S` as a cut and repeat.

Lean proves: the master problem is a relaxation (every completable subfamily is feasible for
every set of valid cuts); a completable master optimum is a maximum-weight completable family;
every new cut is new; and every run of the procedure has at most `2^|C|` iterations, so it
terminates.  The solver and the search for a core `K` are abstract (any optimum, any core).
-/
import Mathlib
import StemmaLean.Cutting

open Finset
open scoped Classical

namespace Stemma.CuttingPlanes

open Cutting

variable {n : ℕ}

/-- Compatible full extensions restrict to overlap-compatible partial splits. -/
lemma overlapCompat_of_extends {s t : PSplit n} {A C : Finset (Fin n)} (hs : Extends s A)
    (ht : Extends t C) (h : Compat A C) : overlapCompat s t := by
  have side : s.side ⊆ A := fun x hx => by
    have : x ∈ A ∩ s.dom := hs ▸ hx; exact (mem_inter.mp this).1
  have other : s.other ⊆ Aᶜ := fun x hx => by
    rw [mem_compl]; intro hxA
    unfold PSplit.other at hx
    have : x ∈ A ∩ s.dom := mem_inter.mpr ⟨hxA, (mem_sdiff.mp hx).1⟩
    rw [hs] at this; exact (mem_sdiff.mp hx).2 this
  have side' : t.side ⊆ C := fun x hx => by
    have : x ∈ C ∩ t.dom := ht ▸ hx; exact (mem_inter.mp this).1
  have other' : t.other ⊆ Cᶜ := fun x hx => by
    rw [mem_compl]; intro hxC
    unfold PSplit.other at hx
    have : x ∈ C ∩ t.dom := mem_inter.mpr ⟨hxC, (mem_sdiff.mp hx).1⟩
    rw [ht] at this; exact (mem_sdiff.mp hx).2 this
  have emp : ∀ (X Y X' Y' W : Finset (Fin n)), X ⊆ X' → Y ⊆ Y' → X' ∩ Y' = ∅ →
      X ∩ Y ∩ W = ∅ := by
    intro X Y X' Y' W hX hY h
    rw [eq_empty_iff_forall_notMem]; intro x hx
    have : x ∈ X' ∩ Y' := mem_inter.mpr ⟨hX (mem_inter.mp (mem_inter.mp hx).1).1,
      hY (mem_inter.mp (mem_inter.mp hx).1).2⟩
    rw [h] at this; simp at this
  unfold overlapCompat
  rcases h with h | h | h | h
  · exact Or.inl (emp _ _ _ _ _ side side' h)
  · exact Or.inr (Or.inl (emp _ _ _ _ _ side other' h))
  · exact Or.inr (Or.inr (Or.inl (emp _ _ _ _ _ other side' h)))
  · exact Or.inr (Or.inr (Or.inr (emp _ _ _ _ _ other other' h)))

/-- Pairwise overlap-compatible. -/
def PairwiseOverlap (F : Finset (PSplit n)) : Prop := ∀ s ∈ F, ∀ t ∈ F, overlapCompat s t

/-- A jointly completable family is pairwise overlap-compatible. -/
lemma pairwiseOverlap_of_completable {F : Finset (PSplit n)} (h : JointlyCompletable F) :
    PairwiseOverlap F := by
  obtain ⟨ext, hext, hc⟩ := h
  exact fun s hs t ht => overlapCompat_of_extends (hext s hs) (hext t ht) (hc s hs t ht)

/-- Every subfamily of a jointly completable family is jointly completable. -/
lemma completable_mono {F G : Finset (PSplit n)} (hFG : F ⊆ G) (h : JointlyCompletable G) :
    JointlyCompletable F := by
  obtain ⟨ext, hext, hc⟩ := h
  exact ⟨ext, fun s hs => hext s (hFG hs), fun s hs t ht => hc s (hFG hs) t (hFG ht)⟩

/-- The weight of a family. -/
def weight (c : PSplit n → ℝ) (F : Finset (PSplit n)) : ℝ := ∑ s ∈ F, c s

/-- Feasible for the master problem with the given cuts. -/
def Feasible (C : Finset (PSplit n)) (cuts : Finset (Finset (PSplit n))) (F : Finset (PSplit n)) :
    Prop :=
  F ⊆ C ∧ PairwiseOverlap F ∧ ∀ K ∈ cuts, ¬ K ⊆ F

/-- An optimum of the master problem. -/
def IsMasterOpt (C : Finset (PSplit n)) (c : PSplit n → ℝ) (cuts : Finset (Finset (PSplit n)))
    (S : Finset (PSplit n)) : Prop :=
  Feasible C cuts S ∧ ∀ F, Feasible C cuts F → weight c F ≤ weight c S

/-- Valid cuts: none is jointly completable. -/
def ValidCuts (cuts : Finset (Finset (PSplit n))) : Prop := ∀ K ∈ cuts, ¬ JointlyCompletable K

/-- The master problem is a relaxation: with valid cuts, every jointly completable subfamily of
the candidates is feasible. -/
theorem relaxation {C : Finset (PSplit n)} {cuts : Finset (Finset (PSplit n))}
    (hv : ValidCuts cuts) {F : Finset (PSplit n)} (hFC : F ⊆ C) (hF : JointlyCompletable F) :
    Feasible C cuts F :=
  ⟨hFC, pairwiseOverlap_of_completable hF, fun K hK hKF => hv K hK (completable_mono hKF hF)⟩

/-- A master problem with valid cuts has an optimum (the empty family is feasible). -/
theorem exists_masterOpt (C : Finset (PSplit n)) (c : PSplit n → ℝ)
    {cuts : Finset (Finset (PSplit n))} (hv : ValidCuts cuts) : ∃ S, IsMasterOpt C c cuts S := by
  have hfeas : (C.powerset.filter (Feasible C cuts)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset C, relaxation hv (empty_subset C)
      ⟨fun _ => ∅, by simp, by simp⟩⟩⟩
  obtain ⟨S, hS, hmax⟩ := exists_max_image _ (weight c) hfeas
  rw [mem_filter] at hS
  exact ⟨S, hS.2, fun F hF => hmax F (mem_filter.mpr ⟨mem_powerset.mpr hF.1, hF⟩)⟩

/-- **Theorem 5.3 (`thm:cutting`), correctness.**  If the cuts are valid and an optimum `S` of the
master problem is jointly completable, then `S` is a maximum-weight jointly completable subfamily
of the candidates. -/
theorem cutting_correct {C : Finset (PSplit n)} {c : PSplit n → ℝ}
    {cuts : Finset (Finset (PSplit n))} (hv : ValidCuts cuts) {S : Finset (PSplit n)}
    (hS : IsMasterOpt C c cuts S) (hSc : JointlyCompletable S) :
    S ⊆ C ∧ JointlyCompletable S ∧
      ∀ F, F ⊆ C → JointlyCompletable F → weight c F ≤ weight c S :=
  ⟨hS.1.1, hSc, fun F hFC hF => hS.2 F (relaxation hv hFC hF)⟩

/-- A non-completable optimum gives a new valid cut (`K = S` always qualifies). -/
theorem new_cut {C : Finset (PSplit n)} {c : PSplit n → ℝ} {cuts : Finset (Finset (PSplit n))}
    (hv : ValidCuts cuts) {S K : Finset (PSplit n)} (hS : IsMasterOpt C c cuts S) (hKS : K ⊆ S)
    (hK : ¬ JointlyCompletable K) :
    K ∉ cuts ∧ K ∈ C.powerset ∧ ValidCuts (insert K cuts) := by
  refine ⟨fun hKc => hS.1.2.2 K hKc hKS, mem_powerset.mpr (hKS.trans hS.1.1), fun K' hK' => ?_⟩
  rw [mem_insert] at hK'
  rcases hK' with rfl | hK'
  · exact hK
  · exact hv K' hK'

/-- A run of the procedure for `N` iterations: cut sets `cuts i`, starting empty; at step `i < N`
the master optimum `S i` is not completable and the core `K i ⊆ S i` is added. -/
structure Run (C : Finset (PSplit n)) (c : PSplit n → ℝ) (N : ℕ) where
  cuts : ℕ → Finset (Finset (PSplit n))
  S : ℕ → Finset (PSplit n)
  K : ℕ → Finset (PSplit n)
  start : cuts 0 = ∅
  opt : ∀ i < N, IsMasterOpt C c (cuts i) (S i)
  sub : ∀ i < N, K i ⊆ S i
  core : ∀ i < N, ¬ JointlyCompletable (K i)
  step : ∀ i < N, cuts (i + 1) = insert (K i) (cuts i)

/-- **Theorem 5.3 (`thm:cutting`), termination.**  Every run has at most `2^|C|` iterations: the
cuts are distinct subfamilies of the candidates. -/
theorem cutting_terminates {C : Finset (PSplit n)} {c : PSplit n → ℝ} {N : ℕ} (R : Run C c N) :
    N ≤ 2 ^ C.card := by
  have inv : ∀ i ≤ N, ValidCuts (R.cuts i) ∧ (R.cuts i).card = i ∧ R.cuts i ⊆ C.powerset := by
    intro i
    induction i with
    | zero => intro _; rw [R.start]; exact ⟨fun K hK => by simp at hK, by simp, by simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨hv, hcard, hsub⟩ := ih (by omega)
      obtain ⟨hnew, hpow, hv'⟩ := new_cut hv (R.opt i (by omega)) (R.sub i (by omega))
        (R.core i (by omega))
      rw [R.step i (by omega)]
      exact ⟨hv', by rw [card_insert_of_notMem hnew, hcard], insert_subset hpow hsub⟩
  obtain ⟨-, hcard, hsub⟩ := inv N le_rfl
  have := card_le_card hsub
  rw [hcard, card_powerset] at this
  exact this

end Stemma.CuttingPlanes
