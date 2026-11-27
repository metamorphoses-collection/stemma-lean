/-
The coincidence null at a polytomy: Proposition 8.8 of the technical report (`prop:polytomynull`).

A vertex `v` of the rooted stemma has children with clades `Cs` (`k = |Cs| ≥ 3`), and
`C_v = ⋃ Cs` (`Vertex`).  For two children `C_i ≠ C_j`, the cluster `τ = C_i ∪ C_j` is false.
In the rooted coding of the attraction model (`Attraction.lean`):

* `pair_cases`: among outcomes with at most two innovations, only the pair of innovations on
  `C_i` and `C_j` (coincidence) and, when `k = 3` and `v` is not the root, the pair on `C_v` and
  the third child `C_l` (overwrite) propose `τ`;
* `lambda_null`: hence the two-innovation part is exactly
  `α² π_i π_j ∏_{g ≠ i,j} (1 - π_g) + [k = 3, v not the root] (1 - α²) π_v π_l ∏_{g ≠ v,l} (1 - π_g)`;
* `null_bound`: with `q_D` the probability that `D` is exactly the set of witnesses carrying a
  non-archetype reading and `s = ∑ π`, for `s ≤ 1`,
  `|m_τ - (α² q_{C_i} q_{C_j} + [k = 3, v not the root] (1 - α²) q_{C_v} q_{C_l})| ≤ 5 s³`,
  which is the report's `O(ε³)` with an explicit constant;
* `null_mixture`: with a random rate factor `ρ ∈ [0, ρ_max]` per unit, the two products are
  multiplied by `κ = E ρ² / (E ρ)²`, with a remainder bounded by a constant times
  `E ρ³ s³`.
-/
import Mathlib
import StemmaLean.Alpha

open Finset
open scoped Classical

namespace Stemma.PolytomyNull

open Stemma.Mechanisms Stemma.Attraction

variable {n : ℕ}

/-- The children `Cs` of a vertex in the rooted stemma with clades `K`: at least three, disjoint,
clades; every clade strictly inside their union lies inside one of them; every clade not inside
their union is disjoint from it or contains it. -/
structure Vertex (K Cs : Finset (Finset (Fin n))) : Prop where
  sub : Cs ⊆ K
  disj : ∀ c ∈ Cs, ∀ d ∈ Cs, c ≠ d → Disjoint c d
  three : 3 ≤ Cs.card
  maxl : ∀ D ∈ K, D ⊂ Cs.sup id → ∃ c ∈ Cs, D ⊆ c
  above : ∀ D ∈ K, ¬ D ⊆ Cs.sup id → Disjoint D (Cs.sup id) ∨ Cs.sup id ⊂ D

lemma le_sup' {Cs : Finset (Finset (Fin n))} {c : Finset (Fin n)} (hc : c ∈ Cs) :
    c ⊆ Cs.sup id := le_sup (f := id) hc

section vertex

variable {K Cs : Finset (Finset (Fin n))} (hV : Vertex K Cs) (hKne : ∀ e ∈ K, e.Nonempty)
  {ci cj : Finset (Fin n)} (hi : ci ∈ Cs) (hj : cj ∈ Cs) (hij : ci ≠ cj)
include hV hKne hi hj hij

/-- A third child. -/
lemma exists_third : ∃ c ∈ Cs, c ≠ ci ∧ c ≠ cj := by
  by_contra h
  push Not at h
  have : Cs ⊆ {ci, cj} := fun c hc => by
    by_cases h1 : c = ci
    · simp [h1]
    · simp [h c hc h1]
  have := card_le_card this
  have := card_le_two (a := ci) (b := cj)
  have := hV.three
  omega

/-- A child meeting `τ = C_i ∪ C_j` is `C_i` or `C_j`. -/
lemma child_of_meet {c : Finset (Fin n)} (hc : c ∈ Cs) {x : Fin n} (hx : x ∈ c)
    (hxτ : x ∈ ci ∪ cj) : c = ci ∨ c = cj := by
  by_contra h
  push Not at h
  rcases mem_union.mp hxτ with h1 | h1
  · exact disjoint_left.mp (hV.disj c hc ci hi h.1) hx h1
  · exact disjoint_left.mp (hV.disj c hc cj hj h.2) hx h1

/-- `τ` lies in no child. -/
lemma not_sub_child {c : Finset (Fin n)} (hc : c ∈ Cs) : ¬ ci ∪ cj ⊆ c := by
  intro h
  obtain ⟨x, hx⟩ := hKne ci (hV.sub hi)
  obtain ⟨y, hy⟩ := hKne cj (hV.sub hj)
  have hci : c = ci := by
    rcases child_of_meet hV hKne hi hj hij hc (h (mem_union_left _ hx)) (mem_union_left _ hx)
      with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ h (mem_union_left _ hx)) (disjoint_left.mp (hV.disj ci hi cj hj hij) hx)
  exact disjoint_left.mp (hV.disj ci hi cj hj hij) (hci ▸ h (mem_union_right _ hy)) hy

lemma tau_ssub : ci ∪ cj ⊂ Cs.sup id := by
  refine ssubset_of_subset_of_ne (union_subset (le_sup' hi) (le_sup' hj)) fun h => ?_
  obtain ⟨c, hc, h1, h2⟩ := exists_third hV hKne hi hj hij
  obtain ⟨x, hx⟩ := hKne c (hV.sub hc)
  have : x ∈ ci ∪ cj := h ▸ le_sup' hc hx
  rcases child_of_meet hV hKne hi hj hij hc hx this with h3 | h3
  · exact h1 h3
  · exact h2 h3

/-- `τ` is not a clade. -/
lemma tau_notMem : ci ∪ cj ∉ K := by
  intro h
  obtain ⟨c, hc, hsub⟩ := hV.maxl _ h (tau_ssub hV hKne hi hj hij)
  exact not_sub_child hV hKne hi hj hij hc hsub

/-- A clade inside `τ` lies in `C_i` or in `C_j`. -/
lemma clade_in_tau {e : Finset (Fin n)} (he : e ∈ K) (heτ : e ⊆ ci ∪ cj) :
    e ⊆ ci ∨ e ⊆ cj := by
  have hlt : e ⊂ Cs.sup id := lt_of_le_of_lt heτ (tau_ssub hV hKne hi hj hij)
  obtain ⟨c, hc, hec⟩ := hV.maxl e he hlt
  obtain ⟨x, hx⟩ := hKne e he
  rcases child_of_meet hV hKne hi hj hij hc (hec hx) (heτ hx) with rfl | rfl
  · exact Or.inl hec
  · exact Or.inr hec

/-- Two disjoint clades whose union is `τ` are `C_i` and `C_j`. -/
lemma union_eq_tau {e f : Finset (Fin n)} (he : e ∈ K) (hf : f ∈ K) (hd : Disjoint e f)
    (h : e ∪ f = ci ∪ cj) : ({e, f} : Finset (Finset (Fin n))) = {ci, cj} := by
  have dij := hV.disj ci hi cj hj hij
  have hne := hKne
  have key : ∀ {a b : Finset (Fin n)}, a ⊆ ci → b ⊆ cj → a ∪ b = ci ∪ cj → a = ci ∧ b = cj := by
    intro a b ha hb hab
    constructor
    · refine subset_antisymm ha fun x hx => ?_
      have : x ∈ a ∪ b := hab ▸ mem_union_left _ hx
      rcases mem_union.mp this with h1 | h1
      · exact h1
      · exact absurd (hb h1) (disjoint_left.mp dij hx)
    · refine subset_antisymm hb fun x hx => ?_
      have : x ∈ a ∪ b := hab ▸ mem_union_right _ hx
      rcases mem_union.mp this with h1 | h1
      · exact absurd (ha h1) (disjoint_right.mp dij hx)
      · exact h1
  have same : ∀ {a b c : Finset (Fin n)}, (c = ci ∨ c = cj) → a ⊆ c → b ⊆ c →
      a ∪ b = ci ∪ cj → False := by
    intro a b c hc ha hb hab
    obtain ⟨x, hx⟩ := hKne ci (hV.sub hi)
    obtain ⟨y, hy⟩ := hKne cj (hV.sub hj)
    have hx' : x ∈ c := union_subset ha hb (hab ▸ mem_union_left _ hx)
    have hy' : y ∈ c := union_subset ha hb (hab ▸ mem_union_right _ hy)
    rcases hc with rfl | rfl
    · exact disjoint_left.mp dij hy' hy
    · exact disjoint_left.mp dij hx hx'
  rcases clade_in_tau hV hKne hi hj hij he (h ▸ subset_union_left) with h1 | h1 <;>
  rcases clade_in_tau hV hKne hi hj hij hf (h ▸ subset_union_right) with h2 | h2
  · exact (same (Or.inl rfl) h1 h2 h).elim
  · obtain ⟨rfl, rfl⟩ := key h1 h2 h; rfl
  · obtain ⟨rfl, rfl⟩ := key h2 h1 (by rw [union_comm]; exact h); exact pair_comm _ _
  · exact (same (Or.inr rfl) h1 h2 h).elim

/-- A clade minus a sub-clade equal to `τ`: the clade is `C_v`, the sub-clade the third child,
`k = 3`, and `C_v` is a clade (so `v` is not the root). -/
lemma sdiff_eq_tau {e f : Finset (Fin n)} (he : e ∈ K) (hf : f ∈ K) (hfe : f ⊂ e)
    (h : e \ f = ci ∪ cj) :
    e = Cs.sup id ∧ f ∈ Cs ∧ f ≠ ci ∧ f ≠ cj ∧ Cs.card = 3 := by
  have hτe : ci ∪ cj ⊆ e := h ▸ sdiff_subset
  have hfeq : f = e \ (ci ∪ cj) := by
    ext x; constructor
    · intro hx; exact mem_sdiff.mpr ⟨hfe.1 hx, fun h' => (mem_sdiff.mp (h ▸ h')).2 hx⟩
    · intro hx
      obtain ⟨h1, h2⟩ := mem_sdiff.mp hx
      by_contra h3; exact h2 (h ▸ mem_sdiff.mpr ⟨h1, h3⟩)
  obtain ⟨c3, hc3, h31, h32⟩ := exists_third hV hKne hi hj hij
  obtain ⟨z, hz⟩ := hKne c3 (hV.sub hc3)
  have hz_notτ : z ∉ ci ∪ cj := fun h' => by
    rcases child_of_meet hV hKne hi hj hij hc3 hz h' with h1 | h1
    · exact h31 h1
    · exact h32 h1
  obtain ⟨y, hy⟩ := hKne ci (hV.sub hi)
  by_cases heV : e ⊆ Cs.sup id
  · rcases heV.eq_or_ssubset with heq | hlt
    · -- `e = C_v`
      refine ⟨heq, ?_⟩
      have hflt : f ⊂ Cs.sup id := heq ▸ hfe
      obtain ⟨c, hc, hfc⟩ := hV.maxl f hf hflt
      -- every other child lies in `f`, hence in `c`
      have hin : ∀ d ∈ Cs, d ≠ ci → d ≠ cj → d = c := by
        intro d hd h1 h2
        obtain ⟨w, hw⟩ := hKne d (hV.sub hd)
        have hwτ : w ∉ ci ∪ cj := fun h' => by
          rcases child_of_meet hV hKne hi hj hij hd hw h' with h3 | h3
          · exact h1 h3
          · exact h2 h3
        have hwf : w ∈ f := hfeq ▸ mem_sdiff.mpr ⟨heq ▸ le_sup' hd hw, hwτ⟩
        by_contra hdc
        exact disjoint_left.mp (hV.disj d hd c hc hdc) hw (hfc hwf)
      have hc3c := hin c3 hc3 h31 h32
      subst hc3c
      have hfc' : f = c3 := by
        refine subset_antisymm hfc fun w hw => ?_
        have hwτ : w ∉ ci ∪ cj := fun h' => by
          rcases child_of_meet hV hKne hi hj hij hc3 hw h' with h3 | h3
          · exact h31 h3
          · exact h32 h3
        exact hfeq ▸ mem_sdiff.mpr ⟨heq ▸ le_sup' hc3 hw, hwτ⟩
      subst hfc'
      refine ⟨hc3, h31, h32, ?_⟩
      have hsub : Cs ⊆ {ci, cj, f} := fun d hd => by
        by_cases h1 : d = ci
        · simp [h1]
        by_cases h2 : d = cj
        · simp [h2]
        simp [hin d hd h1 h2]
      have := card_le_card hsub
      have := card_le_three (a := ci) (b := cj) (c := f)
      have := hV.three
      omega
    · obtain ⟨c, hc, hec⟩ := hV.maxl e he hlt
      exact absurd (hτe.trans hec) (not_sub_child hV hKne hi hj hij hc)
  · rcases hV.above e he heV with hd | hlt
    · exact absurd (le_sup' hi hy) (disjoint_left.mp hd (hτe (mem_union_left _ hy)))
    · exfalso
      obtain ⟨w, hwe, hwV⟩ := not_subset.mp heV
      have hwf : w ∈ f := hfeq ▸ mem_sdiff.mpr ⟨hwe,
        fun h' => hwV (union_subset (le_sup' hi) (le_sup' hj) h')⟩
      have hzf : z ∈ f := hfeq ▸ mem_sdiff.mpr ⟨hlt.1 (le_sup' hc3 hz), hz_notτ⟩
      have hfV : ¬ f ⊆ Cs.sup id := fun h' => hwV (h' hwf)
      rcases hV.above f hf hfV with hd | hlt'
      · exact disjoint_left.mp hd hzf (le_sup' hc3 hz)
      · have : y ∈ f := hlt'.1 (le_sup' hi hy)
        exact (mem_sdiff.mp (hfeq ▸ this)).2 (mem_union_left _ hy)

/-- **Proposition 8.8, the outcomes.**  With at most two innovations, the rooted coding proposes
`τ` only for the pair `C_i`, `C_j`, or, when `k = 3` and `C_v` is a clade, the pair `C_v`, `C_l`. -/
theorem pair_cases (hK : Laminar K) {M : Finset (Finset (Fin n))} (hM : M ⊆ K)
    (h2 : M.card ≤ 2) (att : Finset (Fin n) → Bool) (h : PR (ci ∪ cj) M att) :
    M = {ci, cj} ∨ ∃ c ∈ Cs, c ≠ ci ∧ c ≠ cj ∧ Cs.card = 3 ∧ Cs.sup id ∈ K ∧
      M = {Cs.sup id, c} := by
  have hnot := tau_notMem hV hKne hi hj hij
  rcases Nat.lt_or_ge M.card 1 with h0 | h0
  · rw [card_eq_zero.mp (by omega : M.card = 0)] at h
    exact absurd h ((single att (e := ∅) (ci ∪ cj)).2.1)
  rcases Nat.lt_or_ge M.card 2 with h1 | h1
  · obtain ⟨e, rfl⟩ := card_eq_one.mp (by omega : M.card = 1)
    have := (single att (e := e) (ci ∪ cj)).2.2.2 h
    exact absurd (this ▸ hM (mem_singleton_self e)) hnot
  obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp (by omega : M.card = 2)
  have he : e ∈ K := hM (by simp)
  have hf : f ∈ K := hM (by simp)
  rcases hK e he f hf hef with hd | hfe | hef'
  · left
    rcases (retention_coincidence att hd (hKne e he) (hKne f hf)).2.2.2 _ h with h3 | h3 | h3
    · exact absurd (h3 ▸ he) hnot
    · exact absurd (h3 ▸ hf) hnot
    · exact union_eq_tau hV hKne hi hj hij he hf hd h3.symm
  · rcases (overwrite att hfe (hKne f hf)).2.2.2 _ h with h3 | h3 | h3
    · exact absurd (h3 ▸ hf) hnot
    · exact absurd (h3 ▸ he) hnot
    · obtain ⟨rfl, hfC, h4, h5, h6⟩ := sdiff_eq_tau hV hKne hi hj hij he hf hfe h3.symm
      exact Or.inr ⟨f, hfC, h4, h5, h6, he, rfl⟩
  · rw [pair_comm] at h ⊢
    rcases (overwrite att hef' (hKne e he)).2.2.2 _ h with h3 | h3 | h3
    · exact absurd (h3 ▸ he) hnot
    · exact absurd (h3 ▸ hf) hnot
    · obtain ⟨rfl, heC, h4, h5, h6⟩ := sdiff_eq_tau hV hKne hi hj hij hf he hef' h3.symm
      exact Or.inr ⟨e, heC, h4, h5, h6, hf, rfl⟩

/-- With three children, `C_v \ C_l = τ`. -/
lemma sdiff_third {c : Finset (Fin n)} (hc : c ∈ Cs) (h1 : c ≠ ci) (h2 : c ≠ cj)
    (h3 : Cs.card = 3) : Cs.sup id \ c = ci ∪ cj := by
  have hCs : Cs = {ci, cj, c} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro d hd; simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
    · rw [h3, card_insert_of_notMem (by simp [hij, Ne.symm h1]), card_pair (Ne.symm h2)]
  have hdi := hV.disj c hc ci hi h1
  have hdj := hV.disj c hc cj hj h2
  rw [hCs]
  simp only [sup_insert, sup_singleton, id]
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨h | h | h, hx⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hx
  · rintro (h | h)
    · exact ⟨Or.inl h, fun h' => disjoint_left.mp hdi h' h⟩
    · exact ⟨Or.inr (Or.inl h), fun h' => disjoint_left.mp hdj h' h⟩

lemma child_ne_top {c : Finset (Fin n)} (hc : c ∈ Cs) (hci : c ≠ ci) : c ≠ Cs.sup id := by
  intro h
  obtain ⟨x, hx⟩ := hKne ci (hV.sub hi)
  exact disjoint_left.mp (hV.disj c hc ci hi hci) (h ▸ le_sup' hi hx) hx

lemma top_ne_child {c : Finset (Fin n)} (hc : c ∈ Cs) : Cs.sup id ≠ c := by
  intro h
  obtain ⟨d, hd, h1, h2⟩ := exists_third hV hKne hi hj hij
  by_cases hci : c = ci
  · subst hci
    exact child_ne_top hV hKne hj hi (Ne.symm hij) hi hij h.symm
  · exact child_ne_top hV hKne hi hj hij hc hci h.symm

/-- **Proposition 8.8, the two-innovation part.**  In the rooted coding,
`Λ_τ = α² π_i π_j ∏_{g ≠ i,j} (1 - π_g) + [k = 3, C_v a clade] (1 - α²) π_v π_l ∏_{g ≠ v,l} (1 - π_g)`,
the second term summed over the third child `C_l` (there is exactly one when `k = 3`). -/
theorem lambda_null (hK : Laminar K) (π : Finset (Fin n) → ℝ) (α : ℝ) :
    ex K π α (fun M att => PR (ci ∪ cj) M att ∧ M.card ≤ 2) =
      α ^ 2 * (π ci * π cj * ∏ g ∈ K \ {ci, cj}, (1 - π g)) +
      ∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then
          (1 - α ^ 2) * (π (Cs.sup id) * π c * ∏ g ∈ K \ {Cs.sup id, c}, (1 - π g)) else 0) := by
  have hnot := tau_notMem hV hKne hi hj hij
  rw [lambda_eq hK π α _ (classDet_PR _)]
  have t0 : ¬ PR (ci ∪ cj) ∅ (attOf ∅) := (single (attOf ∅) (e := ∅) (ci ∪ cj)).2.1
  have t1 : ∀ e ∈ K, ¬ PR (ci ∪ cj) {e} (attOf ∅) := fun e he h =>
    hnot ((single (attOf ∅) (e := e) (ci ∪ cj)).2.2.2 h ▸ he)
  rw [if_neg t0, zero_mul, zero_add,
    sum_eq_zero fun e he => by rw [if_neg (t1 e he), mul_zero], zero_add]
  set F : Finset (Finset (Fin n)) → ℝ := fun S =>
    (∏ e ∈ S, π e) * omega (PR (ci ∪ cj)) α S * ∏ g ∈ K \ S, (1 - π g)
  set A : Finset (Finset (Fin n)) := {ci, cj}
  set cond : Prop := Cs.card = 3 ∧ Cs.sup id ∈ K
  set B : Finset (Finset (Finset (Fin n))) :=
    if cond then (Cs.filter fun c => c ≠ ci ∧ c ≠ cj).image (fun c => {Cs.sup id, c}) else ∅
  have hciK := hV.sub hi
  have hcjK := hV.sub hj
  have hAK : A ∈ K.powersetCard 2 :=
    mem_powersetCard.mpr ⟨insert_subset hciK (singleton_subset_iff.mpr hcjK), card_pair hij⟩
  have hBK : B ⊆ K.powersetCard 2 := by
    intro S hS
    simp only [B] at hS
    split_ifs at hS with hc
    · obtain ⟨c, hc', rfl⟩ := mem_image.mp hS
      obtain ⟨hcC, -⟩ := mem_filter.mp hc'
      exact mem_powersetCard.mpr ⟨insert_subset hc.2 (singleton_subset_iff.mpr (hV.sub hcC)),
        card_pair (top_ne_child hV hKne hi hj hij hcC)⟩
    · exact absurd hS (notMem_empty _)
  have hAB : A ∉ B := by
    simp only [B]
    split_ifs
    · intro h
      obtain ⟨c, -, hc⟩ := mem_image.mp h
      have : Cs.sup id ∈ A := hc ▸ mem_insert_self _ _
      simp only [A, mem_insert, mem_singleton] at this
      rcases this with h1 | h1
      · exact child_ne_top hV hKne hj hi (Ne.symm hij) hi hij h1.symm
      · exact child_ne_top hV hKne hi hj hij hj (Ne.symm hij) h1.symm
    · exact notMem_empty _
  have hzero : ∀ S ∈ K.powersetCard 2, S ∉ insert A B → F S = 0 := by
    intro S hS hSn
    obtain ⟨hSK, hS2⟩ := mem_powersetCard.mp hS
    have hnp : ∀ att, ¬ PR (ci ∪ cj) S att := by
      intro att h
      rcases pair_cases hV hKne hi hj hij hK hSK hS2.le att h with h1 | ⟨c, hc, h1, h2, h3, h4, h5⟩
      · exact hSn (h1 ▸ mem_insert_self _ _)
      · apply hSn
        refine mem_insert_of_mem ?_
        simp only [B, cond, if_pos (And.intro h3 h4)]
        exact mem_image.mpr ⟨c, mem_filter.mpr ⟨hc, h1, h2⟩, h5.symm⟩
    simp only [F, omega, if_neg (hnp _)]
    ring
  rw [← sum_subset (insert_subset hAK hBK) hzero, sum_insert hAB]
  have hFA : F A = α ^ 2 * (π ci * π cj * ∏ g ∈ K \ {ci, cj}, (1 - π g)) := by
    simp only [F, A]
    rw [omega_coincidence (hV.disj ci hi cj hj hij) (hKne ci hciK) (hKne cj hcjK), prod_pair hij]
    ring
  rw [hFA]
  congr 1
  by_cases hc : cond
  · simp only [B, if_pos hc]
    rw [sum_image]
    · refine sum_congr rfl fun c hc' => ?_
      obtain ⟨hcC, h1, h2⟩ := mem_filter.mp hc'
      rw [if_pos hc]
      simp only [F]
      have hsd := sdiff_third hV hKne hi hj hij hcC h1 h2 hc.1
      have hss : c ⊂ Cs.sup id :=
        ssubset_of_subset_of_ne (le_sup' hcC) (child_ne_top hV hKne hi hj hij hcC h1)
      rw [← hsd, omega_overwrite_rooted hss (hKne c (hV.sub hcC)),
        prod_pair (top_ne_child hV hKne hi hj hij hcC)]
      ring
    · intro c hc1 c' hc2 h
      have hc1' := (mem_filter.mp hc1).1
      have h' : ({Cs.sup id, c} : Finset (Finset (Fin n))) = {Cs.sup id, c'} := h
      have : c ∈ ({Cs.sup id, c'} : Finset (Finset (Fin n))) := h' ▸ mem_insert_of_mem
        (mem_singleton_self c)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h3 | h3
      · exact absurd h3.symm (top_ne_child hV hKne hi hj hij hc1')
      · exact h3
  · simp only [B, if_neg hc, sum_empty]
    exact (sum_eq_zero fun c _ => if_neg hc).symm

end vertex

/-! ### Bounds for the rates -/

section gen

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)

/-- The probability of at least `k` innovations. -/
noncomputable def Pk (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  ex K π α fun M _ => k ≤ M.card

include hπ0 hπ1 in
/-- `Pr(|M| ≥ k) ≤ e_k`. -/
lemma Pk_le (k : ℕ) : Pk K π α k ≤ esymm K π k := by
  have hx : ∀ M, 0 ≤ (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) := fun M =>
    mul_nonneg (prod_nonneg fun e _ => hπ0 e) (prod_nonneg fun g _ => by linarith [hπ1 g])
  have hP : Pk K π α k = ∑ M ∈ K.powerset,
      (if k ≤ M.card then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) := by
    unfold Pk ex
    refine sum_congr rfl fun M _ => ?_
    by_cases h : k ≤ M.card
    · simp only [h, if_true, mul_one]; exact sum_wt_A M
    · simp [h]
  rw [hP]
  calc ∑ M ∈ K.powerset, (if k ≤ M.card then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0)
      ≤ ∑ M ∈ K.powerset, ∑ S ∈ K.powersetCard k,
          (if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0) := by
        refine sum_le_sum fun M hM => ?_
        split_ifs with h
        · obtain ⟨S, hSM, hS⟩ := exists_subset_card_eq h
          have hSK : S ∈ K.powersetCard k :=
            mem_powersetCard.mpr ⟨hSM.trans (mem_powerset.mp hM), hS⟩
          refine le_trans ?_ (single_le_sum (f := fun S =>
            if S ⊆ M then (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g) else 0)
            (fun S _ => by split_ifs <;> first | exact hx M | exact le_rfl) hSK)
          rw [if_pos hSM]
        · exact sum_nonneg fun S _ => by split_ifs <;> first | exact hx M | exact le_rfl
    _ = ∑ S ∈ K.powersetCard k, ∏ e ∈ S, π e := by
        rw [sum_comm]
        exact sum_congr rfl fun S hS => sum_superset (mem_powersetCard.mp hS).1

include hπ0 hπ1 in
/-- `1 - ∏ (1 - π) ≤ ∑ π`. -/
lemma one_sub_prod_le (T : Finset (Finset (Fin n))) :
    1 - ∏ g ∈ T, (1 - π g) ≤ ∑ g ∈ T, π g := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have h0 : 0 ≤ ∏ g ∈ T, (1 - π g) := prod_nonneg fun g _ => by linarith [hπ1 g]
    have h1 : ∏ g ∈ T, (1 - π g) ≤ 1 :=
      prod_le_one₀ (fun g _ => by linarith [hπ1 g]) fun g _ => by linarith [hπ0 g]
    nlinarith [hπ0 a, hπ1 a]

include hπ0 hπ1 hα0 hα1 in
lemma ex_nonneg (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) :
    0 ≤ ex K π α P :=
  sum_nonneg fun M _ => sum_nonneg fun A _ =>
    mul_nonneg (wt_nonneg hπ0 hπ1 hα0 hα1 M A) (by split_ifs <;> norm_num)

include hπ0 hπ1 hα0 hα1 in
lemma ex_le_one (P : Finset (Finset (Fin n)) → (Finset (Fin n) → Bool) → Prop) :
    ex K π α P ≤ 1 := by
  calc ex K π α P ≤ ex K π α (fun _ _ => True) := ex_mono hπ0 hπ1 hα0 hα1 fun _ _ _ => trivial
    _ = 1 := by
      unfold ex
      simp only [if_true, mul_one]
      rw [sum_congr rfl fun M _ => sum_wt_A M, sum_prod_ite]
      exact prod_eq_one fun e _ => by ring

/-- The witnesses carrying a non-archetype reading. -/
noncomputable def nonorig (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) :
    Finset (Fin n) :=
  univ.filter fun x => read M att x ≠ .orig

/-- `q_D`: the probability that `D` is exactly the set of witnesses carrying a non-archetype
reading. -/
noncomputable def q (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (α : ℝ)
    (D : Finset (Fin n)) : ℝ :=
  ex K π α fun M att => nonorig M att = D

include hπ0 hπ1 hα0 hα1 in
/-- For a non-empty clade `D`, `|q_D - π_D| ≤ (3/2) s²`, `s = ∑ π`. -/
lemma q_bound {D : Finset (Fin n)} (hD : D ∈ K) (hDne : D.Nonempty) :
    |q K π α D - π D| ≤ 3 / 2 * (∑ g ∈ K, π g) ^ 2 := by
  set s := ∑ g ∈ K, π g
  have hs0 : 0 ≤ s := sum_nonneg fun g _ => hπ0 g
  have hDs : π D ≤ s := single_le_sum (fun g _ => hπ0 g) hD
  -- the outcomes with at most one innovation
  have h1 : ex K π α (fun M att => nonorig M att = D ∧ M.card ≤ 1) =
      π D * ∏ g ∈ K \ {D}, (1 - π g) := by
    have : ex K π α (fun M att => nonorig M att = D ∧ M.card ≤ 1) =
        ex K π α (fun M att => True ∧ M = {D}) := by
      refine Alpha.ex_congr fun M hM A _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨trivial, ?_⟩
        rcases Nat.lt_or_ge M.card 1 with h0 | h0
        · rw [card_eq_zero.mp (by omega : M.card = 0)] at h1
          have : nonorig (∅ : Finset (Finset (Fin n))) (attOf A) = ∅ := by
            ext x; simp [nonorig, read_of_none]
          rw [this] at h1
          exact absurd h1.symm hDne.ne_empty
        · obtain ⟨e, rfl⟩ := card_eq_one.mp (by omega : M.card = 1)
          have : nonorig {e} (attOf A) = e := by
            ext x
            simp only [nonorig, mem_filter, mem_univ, true_and]
            by_cases hx : x ∈ e
            · rw [read_of_lowest ⟨mem_singleton_self e, hx,
                fun D' hD' _ => (mem_singleton.mp hD') ▸ le_rfl⟩]
              simp only [hx, iff_true]; split_ifs <;> simp
            · rw [read_of_none (by simpa using hx)]; simp [hx]
          rw [this] at h1; rw [h1]
      · rintro ⟨-, rfl⟩
        refine ⟨?_, by simp⟩
        ext x
        simp only [nonorig, mem_filter, mem_univ, true_and]
        by_cases hx : x ∈ D
        · rw [read_of_lowest ⟨mem_singleton_self D, hx,
            fun D' hD' _ => (mem_singleton.mp hD') ▸ le_rfl⟩]
          simp only [hx, iff_true]; split_ifs <;> simp
        · rw [read_of_none (by simpa using hx)]; simp [hx]
    rw [this, Alpha.ex_eq_single π α _ (singleton_subset_iff.mpr hD)]
    simp only [true_and, if_true, mul_one]
    rw [sum_wt_A, prod_singleton]
  have hsplit := ex_add (K := K) (π := π) (α := α) (fun M att => nonorig M att = D)
    (fun M _ => M.card ≤ 1)
  have hrest0 : 0 ≤ ex K π α (fun M att => nonorig M att = D ∧ ¬ M.card ≤ 1) :=
    ex_nonneg hπ0 hπ1 hα0 hα1 _
  have hrest1 : ex K π α (fun M att => nonorig M att = D ∧ ¬ M.card ≤ 1) ≤ esymm K π 2 :=
    (ex_mono hπ0 hπ1 hα0 hα1 fun M att h => (by omega : 2 ≤ M.card)).trans
      (Pk_le hπ0 hπ1 (α := α) 2)
  have he2 := (esymm_le K hπ0).1
  have hprod1 : 1 - ∏ g ∈ K \ {D}, (1 - π g) ≤ s :=
    (one_sub_prod_le hπ0 hπ1 _).trans (sum_le_sum_of_subset_of_nonneg sdiff_subset
      fun g _ _ => hπ0 g)
  have hprod0 : ∏ g ∈ K \ {D}, (1 - π g) ≤ 1 :=
    prod_le_one₀ (fun g _ => by linarith [hπ1 g]) fun g _ => by linarith [hπ0 g]
  unfold q
  rw [hsplit, h1, abs_le]
  have hD0 := hπ0 D
  constructor <;> nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hprod0)]

end gen

/-! ### The second-order null -/

/-- `|q_a q_b - p_a p_b| ≤ (21/4) s³` when each `q` is within `(3/2) s²` of its `p ∈ [0, s]`,
`s ≤ 1`. -/
lemma prod_err {qa qb pa pb s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 ≤ pa) (hb0 : 0 ≤ pb)
    (has : pa ≤ s) (hbs : pb ≤ s) (hqa : |qa - pa| ≤ 3 / 2 * s ^ 2)
    (hqb : |qb - pb| ≤ 3 / 2 * s ^ 2) : |qa * qb - pa * pb| ≤ 21 / 4 * s ^ 3 := by
  have e : qa * qb - pa * pb = qa * (qb - pb) + pb * (qa - pa) := by ring
  have hqa' : |qa| ≤ 5 / 2 * s := by
    have := abs_sub_abs_le_abs_sub qa pa
    rw [abs_of_nonneg ha0] at this
    nlinarith
  rw [e]
  calc |qa * (qb - pb) + pb * (qa - pa)| ≤ |qa| * |qb - pb| + pb * |qa - pa| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hb0]
    _ ≤ 5 / 2 * s * (3 / 2 * s ^ 2) + s * (3 / 2 * s ^ 2) := by
        gcongr
    _ = 21 / 4 * s ^ 3 := by ring

/-- `|a p Π - a p| ≤ a s² s` for `0 ≤ a`, `0 ≤ p ≤ s²`, `0 ≤ Π ≤ 1`, `1 - Π ≤ s`. -/
lemma term_err {a p P s : ℝ} (ha : 0 ≤ a) (hp0 : 0 ≤ p) (hps : p ≤ s ^ 2) (hP1 : P ≤ 1)
    (hPs : 1 - P ≤ s) : |a * (p * P) - a * p| ≤ a * s ^ 3 := by
  have e : a * (p * P) - a * p = -(a * (p * (1 - P))) := by ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg ha (mul_nonneg hp0 (by linarith)))]
  have : p * (1 - P) ≤ s ^ 2 * s :=
    mul_le_mul hps hPs (by linarith) (le_trans hp0 hps)
  calc a * (p * (1 - P)) ≤ a * (s ^ 2 * s) := mul_le_mul_of_nonneg_left this ha
    _ = a * s ^ 3 := by ring

section null

variable {K Cs : Finset (Finset (Fin n))} (hV : Vertex K Cs) (hKne : ∀ e ∈ K, e.Nonempty)
  (hK : Laminar K) {ci cj : Finset (Fin n)} (hi : ci ∈ Cs) (hj : cj ∈ Cs) (hij : ci ≠ cj)
  {π : Finset (Fin n) → ℝ} {α : ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
include hV hKne hK hi hj hij hπ0 hπ1 hα0 hα1

/-- With three children, exactly one is neither `C_i` nor `C_j`. -/
lemma third_unique (h3 : Cs.card = 3) : ∃ cl, Cs.filter (fun c => c ≠ ci ∧ c ≠ cj) = {cl} := by
  apply card_eq_one.mp
  have hsplit := card_filter_add_card_filter_not (s := Cs) (fun c => c ≠ ci ∧ c ≠ cj)
  have hneg : Cs.filter (fun c => ¬ (c ≠ ci ∧ c ≠ cj)) = {ci, cj} := by
    ext c
    simp only [mem_filter, not_and_or, not_not, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, h | h⟩ <;> simp [h]
    · rintro (rfl | rfl)
      · exact ⟨hi, Or.inl rfl⟩
      · exact ⟨hj, Or.inr rfl⟩
  rw [hneg, card_pair hij, h3] at hsplit
  omega

omit hπ0 hπ1 hα0 hα1 in
/-- The leading term with the rates: `α² π_i π_j + [k = 3, C_v a clade] (1 - α²) π_v π_l`. -/
noncomputable def lead (Cs : Finset (Finset (Fin n))) (K : Finset (Finset (Fin n)))
    (ci cj : Finset (Fin n)) (α : ℝ) (f : Finset (Fin n) → ℝ) : ℝ :=
  α ^ 2 * (f ci * f cj) + ∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
    (if Cs.card = 3 ∧ Cs.sup id ∈ K then (1 - α ^ 2) * (f (Cs.sup id) * f c) else 0)

/-- **Proposition 8.8, with the rates.**  `|m_τ - (α² π_i π_j + [k = 3, v not the root]
(1 - α²) π_v π_l)| ≤ (7/6) s³`. -/
theorem m_bound :
    |ex K π α (PR (ci ∪ cj)) - lead Cs K ci cj α π| ≤ 7 / 6 * (∑ g ∈ K, π g) ^ 3 := by
  set s := ∑ g ∈ K, π g
  have hs0 : 0 ≤ s := sum_nonneg fun g _ => hπ0 g
  have hle : ∀ {D}, D ∈ K → π D ≤ s := fun hD => single_le_sum (fun g _ => hπ0 g) hD
  obtain ⟨hsplit, hR0, hR1⟩ := ex_split hπ0 hπ1 hα0 hα1 (K := K) (PR (ci ∪ cj))
  have hP3 := P3_le hπ0 hπ1 (K := K) (α := α)
  rw [hsplit, lambda_null hV hKne hi hj hij hK π α]
  have hone : ∀ T : Finset (Finset (Fin n)), 1 - ∏ g ∈ K \ T, (1 - π g) ≤ s := fun T =>
    (one_sub_prod_le hπ0 hπ1 _).trans (sum_le_sum_of_subset_of_nonneg sdiff_subset
      fun g _ _ => hπ0 g)
  have hle1 : ∀ T : Finset (Finset (Fin n)), ∏ g ∈ K \ T, (1 - π g) ≤ 1 := fun T =>
    prod_le_one₀ (fun g _ => by linarith [hπ1 g]) fun g _ => by linarith [hπ0 g]
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hpij : π ci * π cj ≤ s ^ 2 := by
    have := hle (hV.sub hi); have := hle (hV.sub hj); have := hπ0 ci; have := hπ0 cj; nlinarith
  have hpij0 : 0 ≤ π ci * π cj := mul_nonneg (hπ0 _) (hπ0 _)
  -- the first term
  have t1 : |α ^ 2 * (π ci * π cj * ∏ g ∈ K \ {ci, cj}, (1 - π g)) - α ^ 2 * (π ci * π cj)| ≤
      α ^ 2 * s ^ 3 := by
    exact term_err ha0 hpij0 hpij (hle1 _) (hone _)
  -- the second term
  have t2 : |(∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then
          (1 - α ^ 2) * (π (Cs.sup id) * π c * ∏ g ∈ K \ {Cs.sup id, c}, (1 - π g)) else 0)) -
      ∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then (1 - α ^ 2) * (π (Cs.sup id) * π c) else 0)| ≤
      (1 - α ^ 2) * s ^ 3 := by
    by_cases hc : Cs.card = 3 ∧ Cs.sup id ∈ K
    · obtain ⟨cl, hcl⟩ := third_unique hV hKne hK hi hj hij hπ0 hπ1 hα0 hα1 hc.1
      rw [hcl, sum_singleton, sum_singleton, if_pos hc, if_pos hc]
      have hclC : cl ∈ Cs := (mem_filter.mp (hcl ▸ mem_singleton_self cl)).1
      have h1 := hle hc.2; have h2 := hle (hV.sub hclC)
      have h3 := hπ0 (Cs.sup id); have h4 := hπ0 cl
      have hp : π (Cs.sup id) * π cl ≤ s ^ 2 := by nlinarith
      have hp0 : 0 ≤ π (Cs.sup id) * π cl := mul_nonneg h3 h4
      exact term_err (by linarith) hp0 hp (hle1 _) (hone _)
    · simp only [if_neg hc, sum_const_zero, sub_zero, abs_zero]
      exact mul_nonneg (by linarith) (pow_nonneg hs0 3)
  unfold lead
  have e : α ^ 2 * (π ci * π cj * ∏ g ∈ K \ {ci, cj}, (1 - π g)) +
      (∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then
          (1 - α ^ 2) * (π (Cs.sup id) * π c * ∏ g ∈ K \ {Cs.sup id, c}, (1 - π g)) else 0)) +
      ex K π α (fun M att => PR (ci ∪ cj) M att ∧ ¬ M.card ≤ 2) -
      (α ^ 2 * (π ci * π cj) + ∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then (1 - α ^ 2) * (π (Cs.sup id) * π c) else 0)) =
      (α ^ 2 * (π ci * π cj * ∏ g ∈ K \ {ci, cj}, (1 - π g)) - α ^ 2 * (π ci * π cj)) +
      ((∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then
          (1 - α ^ 2) * (π (Cs.sup id) * π c * ∏ g ∈ K \ {Cs.sup id, c}, (1 - π g)) else 0)) -
      ∑ c ∈ Cs.filter (fun c => c ≠ ci ∧ c ≠ cj),
        (if Cs.card = 3 ∧ Cs.sup id ∈ K then (1 - α ^ 2) * (π (Cs.sup id) * π c) else 0)) +
      ex K π α (fun M att => PR (ci ∪ cj) M att ∧ ¬ M.card ≤ 2) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) le_rfl).trans ?_
  rw [abs_of_nonneg hR0]
  nlinarith [pow_nonneg hs0 3]

/-- **Proposition 8.8 (`prop:polytomynull`).**  For `s = ∑ π ≤ 1`, in the rooted coding,
`|m_τ - (α² q_{C_i} q_{C_j} + [k = 3, v not the root] (1 - α²) q_{C_v} q_{C_l})| ≤ 7 s³`. -/
theorem null_bound (hs1 : ∑ g ∈ K, π g ≤ 1) :
    |ex K π α (PR (ci ∪ cj)) - lead Cs K ci cj α (q K π α)| ≤ 7 * (∑ g ∈ K, π g) ^ 3 := by
  set s := ∑ g ∈ K, π g
  have hs0 : 0 ≤ s := sum_nonneg fun g _ => hπ0 g
  have hle : ∀ {D}, D ∈ K → π D ≤ s := fun hD => single_le_sum (fun g _ => hπ0 g) hD
  have hm := m_bound hV hKne hK hi hj hij hπ0 hπ1 hα0 hα1
  have hq : ∀ {D}, D ∈ K → |q K π α D - π D| ≤ 3 / 2 * s ^ 2 := fun hD =>
    q_bound hπ0 hπ1 hα0 hα1 hD (hKne _ hD)
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hdiff : |lead Cs K ci cj α π - lead Cs K ci cj α (q K π α)| ≤ 21 / 4 * s ^ 3 := by
    have p1 := prod_err hs0 hs1 (hπ0 ci) (hπ0 cj) (hle (hV.sub hi)) (hle (hV.sub hj))
      (hq (hV.sub hi)) (hq (hV.sub hj))
    unfold lead
    by_cases hc : Cs.card = 3 ∧ Cs.sup id ∈ K
    · obtain ⟨cl, hcl⟩ := third_unique hV hKne hK hi hj hij hπ0 hπ1 hα0 hα1 hc.1
      rw [hcl, sum_singleton, sum_singleton, if_pos hc, if_pos hc]
      have hclC : cl ∈ Cs := (mem_filter.mp (hcl ▸ mem_singleton_self cl)).1
      have p2 := prod_err hs0 hs1 (hπ0 (Cs.sup id)) (hπ0 cl) (hle hc.2) (hle (hV.sub hclC))
        (hq hc.2) (hq (hV.sub hclC))
      have e : α ^ 2 * (π ci * π cj) + (1 - α ^ 2) * (π (Cs.sup id) * π cl) -
          (α ^ 2 * (q K π α ci * q K π α cj) +
            (1 - α ^ 2) * (q K π α (Cs.sup id) * q K π α cl)) =
          -(α ^ 2 * (q K π α ci * q K π α cj - π ci * π cj)) -
            (1 - α ^ 2) * (q K π α (Cs.sup id) * q K π α cl - π (Cs.sup id) * π cl) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (by linarith : 0 ≤ 1 - α ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left p1 ha0,
        mul_le_mul_of_nonneg_left p2 (by linarith : 0 ≤ 1 - α ^ 2)]
    · simp only [if_neg hc, sum_const_zero, add_zero]
      rw [← mul_sub, abs_mul, abs_of_nonneg ha0, abs_sub_comm]
      nlinarith [mul_le_mul_of_nonneg_left p1 ha0, pow_nonneg hs0 3]
  calc |ex K π α (PR (ci ∪ cj)) - lead Cs K ci cj α (q K π α)|
      ≤ |ex K π α (PR (ci ∪ cj)) - lead Cs K ci cj α π| +
        |lead Cs K ci cj α π - lead Cs K ci cj α (q K π α)| := abs_sub_le _ _ _
    _ ≤ 7 / 6 * s ^ 3 + 21 / 4 * s ^ 3 := add_le_add hm hdiff
    _ ≤ 7 * s ^ 3 := by nlinarith [pow_nonneg hs0 3]

end null

end Stemma.PolytomyNull
