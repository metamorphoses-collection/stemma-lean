/-
The dynamic programme over subsets: Theorem 9.4 of the technical report (`thm:fpt`).

Fix a witness `x`.  A compatible set of non-trivial splits is a laminar family of sides avoiding
`x` (`compat_iff_laminar`).  For `C ⊆ Y = X \ {x}` the report sets `F(C)`, the maximum weight of a
laminar family of subsets of `C` that may include `C`, and `P(C)`, the maximum of `∑ F(Dᵢ)` over
partitions of `C`, and computes them by

  `F(C) = w(C) + max_{D ⊊ C, min C ∈ D} [F(D) + P(C \ D)]`,
  `P(C) = max_{D ⊆ C, min C ∈ D} [F(D) + P(C \ D)]`,  `P(∅) = 0`.

Formalised: the optimum over laminar families (`opt`) satisfies both recurrences, for any element
of `C` in place of `min C` (`opt_rec_F`, `opt_rec_P`); any functions satisfying them agree with it
(`dp_unique`), so the programme is correct whatever order it fills its table in; and, with the
candidate weights put on the sides away from `x` and `0` elsewhere, `F(Y)` is the maximum weight
of a compatible set of non-trivial splits (`dp_correct`).

The bound of `O(3ⁿ)` operations is `totalCost_le`, in a cost model that counts the additions and
comparisons the recurrences prescribe, each table entry computed once (as a tick counter would,
cf. `TimeM` in cslib): at most `5 · 3^{n-1}`.  It is not a bound for a machine model.  Weights are natural numbers, the report's unit
counts, so the report's `max(0, w(C))` is `w(C)`; an empty maximum is `0`, which is the value the
report's `F` takes on a singleton.  Laminar families consist of non-empty sets, so `∅` is never
counted.
-/
import Mathlib
import StemmaLean.Splits

open Finset

namespace Stemma.Dynamic

open Stemma.Splits

variable {n : ℕ}

/-- `L` is a laminar family of non-empty subsets of `C`. -/
def IsLam (C : Finset (Fin n)) (L : Finset (Finset (Fin n))) : Prop :=
  (∀ D ∈ L, D.Nonempty ∧ D ⊆ C) ∧ ∀ A ∈ L, ∀ B ∈ L, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

open scoped Classical in
/-- The laminar families of non-empty subsets of `C`. -/
noncomputable def fams (C : Finset (Fin n)) : Finset (Finset (Finset (Fin n))) :=
  C.powerset.powerset.filter (IsLam C)

/-- The maximum weight of a laminar family of non-empty subsets of `C` (the report's `F(C)`). -/
noncomputable def opt (w : Finset (Fin n) → ℕ) (C : Finset (Fin n)) : ℕ :=
  (fams C).sup (weight w)

lemma mem_fams {C : Finset (Fin n)} {L : Finset (Finset (Fin n))} :
    L ∈ fams C ↔ IsLam C L := by
  classical
  unfold fams
  rw [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨fun D hD => mem_powerset.mpr (h.1 D hD).2, h⟩⟩

lemma le_opt (w : Finset (Fin n) → ℕ) {C : Finset (Fin n)} {L : Finset (Finset (Fin n))}
    (h : IsLam C L) : weight w L ≤ opt w C :=
  le_sup (f := weight w) (mem_fams.mpr h)

lemma isLam_empty (C : Finset (Fin n)) : IsLam C ∅ := ⟨by simp, by simp⟩

lemma exists_opt (w : Finset (Fin n) → ℕ) (C : Finset (Fin n)) :
    ∃ L, IsLam C L ∧ weight w L = opt w C := by
  obtain ⟨L, hL, h⟩ := exists_mem_eq_sup (fams C) ⟨∅, mem_fams.mpr (isLam_empty C)⟩ (weight w)
  exact ⟨L, mem_fams.mp hL, h.symm⟩

lemma opt_empty (w : Finset (Fin n) → ℕ) : opt w ∅ = 0 := by
  obtain ⟨L, hL, h⟩ := exists_opt w ∅
  have : L = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro D hD
    obtain ⟨⟨y, hy⟩, hsub⟩ := hL.1 D hD
    exact notMem_empty y (hsub hy)
  rw [← h, this]; rfl

/-- Two laminar families on disjoint parts `D` and `C \ D` of `C` combine into one on `C`. -/
lemma isLam_union {C D : Finset (Fin n)} (hD : D ⊆ C) {L₁ L₂ : Finset (Finset (Fin n))}
    (h₁ : IsLam D L₁) (h₂ : IsLam (C \ D) L₂) :
    IsLam C (L₁ ∪ L₂) ∧ Disjoint L₁ L₂ := by
  have cross : ∀ A ∈ L₁, ∀ B ∈ L₂, Disjoint A B := fun A hA B hB =>
    disjoint_of_subset_left (h₁.1 A hA).2
      (disjoint_of_subset_right (h₂.1 B hB).2 disjoint_sdiff)
  refine ⟨⟨fun E hE => ?_, fun A hA B hB => ?_⟩, ?_⟩
  · rcases mem_union.mp hE with hE | hE
    · exact ⟨(h₁.1 E hE).1, (h₁.1 E hE).2.trans hD⟩
    · exact ⟨(h₂.1 E hE).1, (h₂.1 E hE).2.trans sdiff_subset⟩
  · rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
    · exact h₁.2 A hA B hB
    · exact Or.inl (cross A hA B hB)
    · exact Or.inl (cross B hB A hA).symm
    · exact h₂.2 A hA B hB
  · rw [disjoint_left]
    intro E h1 h2
    obtain ⟨y, hy⟩ := (h₁.1 E h1).1
    exact Finset.disjoint_left.mp (cross E h1 E h2) hy hy

lemma opt_add_le (w : Finset (Fin n) → ℕ) {C D : Finset (Fin n)} (hD : D ⊆ C) :
    opt w D + opt w (C \ D) ≤ opt w C := by
  obtain ⟨L₁, h₁, e₁⟩ := exists_opt w D
  obtain ⟨L₂, h₂, e₂⟩ := exists_opt w (C \ D)
  obtain ⟨hL, hdis⟩ := isLam_union hD h₁ h₂
  rw [← e₁, ← e₂]
  have := le_opt w hL
  unfold weight at this ⊢
  rwa [sum_union hdis] at this

/-- The candidates for the block containing `a`, in the recurrence for `F`. -/
noncomputable def blocksF (C : Finset (Fin n)) (a : Fin n) : Finset (Finset (Fin n)) :=
  C.powerset.filter fun D => D ≠ C ∧ a ∈ D

/-- The candidates for the block containing `a`, in the recurrence for `P`. -/
noncomputable def blocksP (C : Finset (Fin n)) (a : Fin n) : Finset (Finset (Fin n)) :=
  C.powerset.filter fun D => a ∈ D

/-- **The recurrence for `F`.**  For any `a ∈ C`,
`opt C = w C + max_{D ⊊ C, a ∈ D} (opt D + opt (C \ D))`. -/
theorem opt_rec_F (w : Finset (Fin n) → ℕ) {C : Finset (Fin n)} {a : Fin n} (ha : a ∈ C) :
    opt w C = w C + (blocksF C a).sup (fun D => opt w D + opt w (C \ D)) := by
  apply le_antisymm
  · -- an optimal family: its largest member through `a`, other than `C`, cuts it in two
    obtain ⟨L, hL, hw⟩ := exists_opt w C
    rw [← hw]
    set L' := L.erase C
    have hsplit : weight w L ≤ w C + weight w L' := by
      unfold weight
      by_cases hC : C ∈ L
      · rw [← add_sum_erase _ _ hC]
      · simp only [L', erase_eq_of_notMem hC]; omega
    have hL' : IsLam C L' :=
      ⟨fun D hD => hL.1 D (mem_of_mem_erase hD),
        fun A hA B hB => hL.2 A (mem_of_mem_erase hA) B (mem_of_mem_erase hB)⟩
    refine hsplit.trans (Nat.add_le_add_left ?_ _)
    -- the block `D` containing `a`
    obtain ⟨D, hDC, haD, hDne, hin, hout⟩ : ∃ D ⊆ C, a ∈ D ∧ (D ≠ C ∨ L' = ∅) ∧
        (∀ E ∈ L', a ∈ E → E ⊆ D) ∧ (∀ E ∈ L', ¬ E ⊆ D → Disjoint E D) := by
      by_cases hex : (L'.filter (a ∈ ·)).Nonempty
      · obtain ⟨M, hM, hmax⟩ := exists_max_image (L'.filter (a ∈ ·)) card hex
        rw [mem_filter] at hM
        have hMC : M ≠ C := ne_of_mem_erase hM.1
        have sub : ∀ E ∈ L', a ∈ E → E ⊆ M := by
          intro E hE haE
          rcases hL'.2 E hE M hM.1 with h | h | h
          · exact absurd hM.2 (Finset.disjoint_left.mp h haE)
          · exact h
          · rcases h.eq_or_ssubset with rfl | hss
            · exact subset_refl _
            · have := hmax E (mem_filter.mpr ⟨hE, haE⟩)
              exact absurd (card_lt_card hss) (not_lt.mpr this)
        refine ⟨M, (hL'.1 M hM.1).2, hM.2, Or.inl hMC, sub, fun E hE hEM => ?_⟩
        rcases hL'.2 E hE M hM.1 with h | h | h
        · exact h
        · exact absurd h hEM
        · exact absurd (sub E hE (h hM.2)) hEM
      · refine ⟨{a}, singleton_subset_iff.mpr ha, mem_singleton_self a, ?_, ?_, ?_⟩
        · by_cases hCa : ({a} : Finset (Fin n)) = C
          · right
            rw [eq_empty_iff_forall_notMem]
            intro E hE
            obtain ⟨⟨y, hy⟩, hsub⟩ := hL'.1 E hE
            have hya : y = a := by rw [← mem_singleton, hCa]; exact hsub hy
            exact hex ⟨E, mem_filter.mpr ⟨hE, hya ▸ hy⟩⟩
          · exact Or.inl hCa
        · intro E hE haE; exact absurd ⟨E, mem_filter.mpr ⟨hE, haE⟩⟩ hex
        · intro E hE _
          rw [disjoint_singleton_right]
          intro haE; exact hex ⟨E, mem_filter.mpr ⟨hE, haE⟩⟩
    rcases hDne with hDne | hempty
    · -- `L'` splits into the members inside `D` and those inside `C \ D`
      set L₁ := L'.filter (· ⊆ D)
      set L₂ := L'.filter (fun E => ¬ E ⊆ D)
      have h₁ : IsLam D L₁ :=
        ⟨fun E hE => ⟨(hL'.1 E (mem_filter.mp hE).1).1, (mem_filter.mp hE).2⟩,
          fun A hA B hB => hL'.2 A (mem_filter.mp hA).1 B (mem_filter.mp hB).1⟩
      have h₂ : IsLam (C \ D) L₂ := by
        refine ⟨fun E hE => ?_, fun A hA B hB => hL'.2 A (mem_filter.mp hA).1 B
          (mem_filter.mp hB).1⟩
        obtain ⟨hE', hnot⟩ := mem_filter.mp hE
        refine ⟨(hL'.1 E hE').1, fun y hy => mem_sdiff.mpr ⟨(hL'.1 E hE').2 hy, fun hyD =>
          Finset.disjoint_left.mp (hout E hE' hnot) hy hyD⟩⟩
      have hsum : weight w L' = weight w L₁ + weight w L₂ := by
        unfold weight; exact (sum_filter_add_sum_filter_not L' _ _).symm
      have hmem : D ∈ blocksF C a := mem_filter.mpr ⟨mem_powerset.mpr hDC, hDne, haD⟩
      rw [hsum]
      calc weight w L₁ + weight w L₂ ≤ opt w D + opt w (C \ D) :=
            Nat.add_le_add (le_opt w h₁) (le_opt w h₂)
        _ ≤ _ := le_sup (f := fun D => opt w D + opt w (C \ D)) hmem
    · rw [hempty]; exact Nat.zero_le _
  · -- `C` together with optimal families on `D` and `C \ D`
    rcases (blocksF C a).eq_empty_or_nonempty with hE | hne
    · rw [hE, sup_empty]
      have := le_opt w (L := {C}) ⟨fun D hD => by
          rw [mem_singleton.mp hD]; exact ⟨⟨a, ha⟩, subset_refl _⟩,
        fun A hA B hB => by
          rw [mem_singleton.mp hA, mem_singleton.mp hB]; exact Or.inr (Or.inl (subset_refl _))⟩
      simpa [weight] using this
    · obtain ⟨D, hD, hsup⟩ := exists_mem_eq_sup _ hne (fun D => opt w D + opt w (C \ D))
      rw [hsup]
      obtain ⟨hDC', hDne, haD⟩ := mem_filter.mp hD
      have hDC := mem_powerset.mp hDC'
      obtain ⟨L₁, h₁, e₁⟩ := exists_opt w D
      obtain ⟨L₂, h₂, e₂⟩ := exists_opt w (C \ D)
      obtain ⟨hL, hdis⟩ := isLam_union hDC h₁ h₂
      have hCnot : C ∉ L₁ ∪ L₂ := by
        intro hC
        rcases mem_union.mp hC with hC | hC
        · exact hDne (subset_antisymm hDC ((h₁.1 C hC).2))
        · exact (mem_sdiff.mp ((h₂.1 C hC).2 ha)).2 (haD)
      have hL' : IsLam C (insert C (L₁ ∪ L₂)) := by
        refine ⟨fun E hE => ?_, fun A hA B hB => ?_⟩
        · rcases mem_insert.mp hE with rfl | hE
          · exact ⟨⟨a, ha⟩, subset_refl _⟩
          · exact hL.1 E hE
        · rcases mem_insert.mp hA with hA' | hA' <;> rcases mem_insert.mp hB with hB' | hB'
          · rw [hA', hB']; exact Or.inr (Or.inl (subset_refl _))
          · rw [hA']; exact Or.inr (Or.inr (hL.1 B hB').2)
          · rw [hB']; exact Or.inr (Or.inl (hL.1 A hA').2)
          · exact hL.2 A hA' B hB'
      have := le_opt w hL'
      unfold weight at this
      rw [sum_insert hCnot, sum_union hdis] at this
      rw [← e₁, ← e₂]
      unfold weight
      omega

/-- **The recurrence for `P`.**  For any `a ∈ C`, `opt C = max_{D ⊆ C, a ∈ D} (opt D + opt (C \ D))`:
the maximum over partitions of `C` of the sum of the optima on the blocks is the optimum on `C`. -/
theorem opt_rec_P (w : Finset (Fin n) → ℕ) {C : Finset (Fin n)} {a : Fin n} (ha : a ∈ C) :
    opt w C = (blocksP C a).sup (fun D => opt w D + opt w (C \ D)) := by
  apply le_antisymm
  · have hC : C ∈ blocksP C a := mem_filter.mpr ⟨mem_powerset.mpr (subset_refl _), ha⟩
    have := le_sup (f := fun D => opt w D + opt w (C \ D)) hC
    simpa [opt_empty] using this
  · exact Finset.sup_le fun D hD => opt_add_le w (mem_powerset.mp (mem_filter.mp hD).1)

/-- **Theorem 9.4 (`thm:fpt`), the table.**  Any functions `F` and `P` satisfying the report's
recurrences, with `P(∅) = 0`, are the optima: `F(C) = P(C) = opt w C` for every non-empty `C`. -/
theorem dp_unique (w : Finset (Fin n) → ℕ) (F P : Finset (Fin n) → ℕ) (hP0 : P ∅ = 0)
    (hF : ∀ C (hC : C.Nonempty),
      F C = w C + (blocksF C (C.min' hC)).sup (fun D => F D + P (C \ D)))
    (hP : ∀ C (hC : C.Nonempty), P C = (blocksP C (C.min' hC)).sup (fun D => F D + P (C \ D))) :
    ∀ C : Finset (Fin n), C.Nonempty → F C = opt w C ∧ P C = opt w C := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro hC
    set a := C.min' hC
    have ha : a ∈ C := C.min'_mem hC
    -- on the smaller sets, `P` agrees with `opt`, also at `∅`
    have hPs : ∀ E ⊂ C, P E = opt w E := by
      intro E hE
      rcases E.eq_empty_or_nonempty with rfl | hne
      · rw [hP0, opt_empty]
      · exact (ih E hE hne).2
    have hrest : ∀ D ⊆ C, a ∈ D → C \ D ⊂ C := fun D hDC haD =>
      sdiff_ssubset hDC ⟨a, haD⟩
    have hFC : F C = opt w C := by
      rw [hF C hC, opt_rec_F w ha]
      congr 1
      refine sup_congr rfl fun D hD => ?_
      obtain ⟨hDC', hDne, haD⟩ := mem_filter.mp hD
      have hDC := mem_powerset.mp hDC'
      rw [(ih D (ssubset_of_subset_of_ne hDC hDne) ⟨a, haD⟩).1, hPs _ (hrest D hDC haD)]
    refine ⟨hFC, ?_⟩
    rw [hP C hC, opt_rec_P w ha]
    refine sup_congr rfl fun D hD => ?_
    obtain ⟨hDC', haD⟩ := mem_filter.mp hD
    have hDC := mem_powerset.mp hDC'
    rcases eq_or_ne D C with rfl | hDne
    · rw [hFC, sdiff_self, bot_eq_empty, hP0, opt_empty]
    · rw [(ih D (ssubset_of_subset_of_ne hDC hDne) ⟨a, haD⟩).1, hPs _ (hrest D hDC haD)]

open scoped Classical in
/-- **Theorem 9.4 (`thm:fpt`).**  Put the candidate weights `w` on the sides away from `x` and `0`
on every other subset.  If `F` and `P` satisfy the report's recurrences, then `F(X \ {x})` is the
maximum weight of a compatible set of non-trivial splits: it bounds every such set, and some such
set attains it. -/
theorem dp_correct (hn : 2 ≤ n) (x : Fin n) (w : Finset (Fin n) → ℕ)
    (F P : Finset (Fin n) → ℕ) (hP0 : P ∅ = 0)
    (hF : ∀ C (hC : C.Nonempty), F C = (if IsSide x C then w C else 0) +
      (blocksF C (C.min' hC)).sup (fun D => F D + P (C \ D)))
    (hP : ∀ C (hC : C.Nonempty), P C = (blocksP C (C.min' hC)).sup (fun D => F D + P (C \ D))) :
    (∀ S, IsSystem x S → weight w S ≤ F (univ.erase x)) ∧
      ∃ S, IsSystem x S ∧ weight w S = F (univ.erase x) := by
  set w' : Finset (Fin n) → ℕ := fun C => if IsSide x C then w C else 0
  have hY : (univ.erase x).Nonempty := by
    obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ x := by
      by_contra h
      push Not at h
      have : Fintype.card (Fin n) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
      rw [Fintype.card_fin] at this; omega
    exact ⟨y, mem_erase.mpr ⟨hy, mem_univ y⟩⟩
  rw [(dp_unique w' F P hP0 hF hP _ hY).1]
  have hw' : ∀ S : Finset (Finset (Fin n)), (∀ A ∈ S, IsSide x A) → weight w' S = weight w S :=
    fun S hS => sum_congr rfl fun A hA => by simp [w', hS A hA]
  constructor
  · intro S hS
    rw [← hw' S hS.1]
    refine le_opt w' ⟨fun A hA => ⟨?_, ?_⟩, fun A hA B hB => ?_⟩
    · exact card_pos.mp (by have := (hS.1 A hA).2.1; omega)
    · intro y hy
      exact mem_erase.mpr ⟨fun h => (hS.1 A hA).1 (h ▸ hy), mem_univ y⟩
    · by_cases hAB : A = B
      · subst hAB; exact Or.inr (Or.inl (subset_refl _))
      · exact (compat_iff_laminar (hS.1 A hA).1 (hS.1 B hB).1).mp (hS.2 A hA B hB hAB)
  · obtain ⟨L, hL, hopt⟩ := exists_opt w' (univ.erase x)
    refine ⟨L.filter (IsSide x), ⟨fun A hA => (mem_filter.mp hA).2, fun A hA B hB _ => ?_⟩, ?_⟩
    · obtain ⟨hA, hsA⟩ := mem_filter.mp hA
      obtain ⟨hB, hsB⟩ := mem_filter.mp hB
      exact (compat_iff_laminar hsA.1 hsB.1).mpr (hL.2 A hA B hB)
    · rw [← hw' _ (fun A hA => (mem_filter.mp hA).2), ← hopt]
      unfold weight
      rw [sum_filter]
      exact sum_congr rfl fun A _ => by
        by_cases h : IsSide x A
        · simp [w', h]
        · simp [w', h]

/-! ### The number of operations -/

/-- The arithmetic operations of the table entry for `C` (cost model in the style of a tick
counter): one addition for `w(C)`, and for each candidate block `D` of either recurrence one
addition `F(D) + P(C \ D)` and one comparison with the running maximum. -/
noncomputable def localCost (C : Finset (Fin n)) : ℕ :=
  if h : C.Nonempty then 1 + 2 * (blocksF C (C.min' h)).card + 2 * (blocksP C (C.min' h)).card
  else 0

/-- The operations of the whole table over the subsets of `Y`. -/
noncomputable def totalCost (Y : Finset (Fin n)) : ℕ := ∑ C ∈ Y.powerset, localCost C

/-- **Theorem 9.4, the operation count.**  Filling the table of the recurrences over the subsets
of `Y = X \ {x}`, each entry once, takes at most `5 · 3^{|Y|} = 5 · 3^{n-1}` arithmetic operations:
`O(3ⁿ)`, whatever the number of candidate splits. -/
theorem totalCost_le (Y : Finset (Fin n)) : totalCost Y ≤ 5 * 3 ^ Y.card := by
  have hloc : ∀ C : Finset (Fin n), localCost C ≤ 1 + 4 * 2 ^ C.card := by
    intro C
    unfold localCost
    split_ifs with h
    · have h1 : (blocksF C (C.min' h)).card ≤ 2 ^ C.card :=
        (card_filter_le _ _).trans (card_powerset C).le
      have h2 : (blocksP C (C.min' h)).card ≤ 2 ^ C.card :=
        (card_filter_le _ _).trans (card_powerset C).le
      omega
    · omega
  have h3 : ∑ C ∈ Y.powerset, 2 ^ C.card = 3 ^ Y.card := by
    have := Finset.sum_pow_mul_eq_add_pow (2 : ℕ) 1 Y
    simpa using this
  have h2 : ∑ C ∈ Y.powerset, 1 = 2 ^ Y.card := by
    rw [sum_const, card_powerset, smul_eq_mul, mul_one]
  have h23 : 2 ^ Y.card ≤ 3 ^ Y.card := Nat.pow_le_pow_left (by norm_num) _
  calc totalCost Y ≤ ∑ C ∈ Y.powerset, (1 + 4 * 2 ^ C.card) := sum_le_sum fun C _ => hloc C
    _ = 2 ^ Y.card + 4 * 3 ^ Y.card := by rw [sum_add_distrib, ← mul_sum, h2, h3]
    _ ≤ 5 * 3 ^ Y.card := by omega

end Stemma.Dynamic
