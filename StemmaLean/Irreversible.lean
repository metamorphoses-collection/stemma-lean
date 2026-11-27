/-
The irreversible model: Proposition 8.9 (`prop:modelbounds`, support bounds) and Corollary 8.10
(`cor:modelglobal`, a sufficient condition) of the technical report.

A rooted stemma is given by the clades `K` of its edges, a laminar family (`Attraction.Laminar`);
the root subdivides an edge or sits at a vertex, so the clades of the two halves of a subdivided
edge are both in `K`.  A unit has an original reading `0` and one alternative `1`.  Independently
for each edge `e ∈ K`, a potential innovation is marked with probability `π e`; a witness reads `1`
if some edge above it is marked.  The witnesses reading `1` form `ones M = ⋃ {C_e : e ∈ M}` for
the set `M` of marked edges, of probability `pM K π M = ∏_M π · ∏_{K \ M} (1 - π)`, and the unit
proposes the split `ones M | X \ ones M` if it is non-trivial (`Proposes`).  The expected support
`suppI` is the sum over the `2^|K|` mark sets.

This is the model of the report's Definition (irreversible model) stated directly, not as the
`α = 1` case of `Attraction.lean`: with one alternative reading the outcome is the mark set alone.

Formalised:
* `suppI_edge_ge` (first bound of Proposition 8.9): for an edge `e` with `C_e` non-trivial,
  `m_{σ_e} ≥ π_e ∏_{f : C_f ⊄ C_e} (1 - π_f)`, the probability, computed exactly, that `e` is
  marked and no edge outside `C_e` is;
* `false_mass_le` (second bound): for any set of false splits, no two of them complementary,
  `∑ m_τ ≤ ∑_{{e,f} : C_e ∩ C_f = ∅} π_e π_f`; a false split needs two marked edges with
  disjoint clades (`proposes_pair`), and a unit proposes at most one split;
  `false_mass_sides` is the report's form, the sum over all false splits by their sides away
  from a reference witness;
* `model_global` (Corollary 8.10): if `T` is binary, every split of `T` is the split of an edge and
  every non-trivial edge split is in `T`, and `π_e ∏_{f ∈ K} (1 - π_f) ≥ c > D` for every edge with
  non-trivial clade (`D` the sum over disjoint pairs), then global separation holds for `m`, `T` is
  the unique solution for `m`, and the margin inequality holds with `γ = c - D > 0`;
  `model_consistency` adds the units (Theorem 7.4(a)).
-/
import Mathlib
import StemmaLean.Attraction
import StemmaLean.Consistency

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace Stemma.Irreversible

open Stemma.Splits Stemma.Attraction

variable {n : ℕ}

/-- The witnesses reading the alternative: the union of the clades of the marked edges. -/
def ones (M : Finset (Finset (Fin n))) : Finset (Fin n) := M.biUnion id

/-- The probability that the marked edges are exactly `M ⊆ K`. -/
noncomputable def pM (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ)
    (M : Finset (Finset (Fin n))) : ℝ :=
  (∏ e ∈ M, π e) * ∏ g ∈ K \ M, (1 - π g)

/-- The unit with marked edges `M` proposes the split `τ | τᶜ`: `ones M` is non-trivial and is
one of its sides. -/
def Proposes (M : Finset (Finset (Fin n))) (τ : Finset (Fin n)) : Prop :=
  Nontriv (ones M) ∧ (ones M = τ ∨ ones M = τᶜ)

/-- The expected support of the split `τ | τᶜ` in the irreversible model. -/
noncomputable def suppI (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ)
    (τ : Finset (Fin n)) : ℝ :=
  ∑ M ∈ K.powerset, pM K π M * if Proposes M τ then 1 else 0

/-- The unordered pairs of edges with disjoint clades. -/
noncomputable def disjPairs (K : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  (K.powersetCard 2).filter fun S => ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f

/-- `∑_{{e,f} : C_e ∩ C_f = ∅} π_e π_f`, over unordered pairs. -/
noncomputable def D (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S ∈ disjPairs K, ∏ e ∈ S, π e

lemma mem_ones {M : Finset (Finset (Fin n))} {x : Fin n} : x ∈ ones M ↔ ∃ e ∈ M, x ∈ e := by
  simp [ones]

lemma suppI_compl (K : Finset (Finset (Fin n))) (π : Finset (Fin n) → ℝ) (τ : Finset (Fin n)) :
    suppI K π τᶜ = suppI K π τ := by
  unfold suppI Proposes
  refine sum_congr rfl fun M _ => ?_
  rw [compl_compl, or_comm]

section rates

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1)

include hπ0 hπ1 in
lemma pM_nonneg (M : Finset (Finset (Fin n))) : 0 ≤ pM K π M :=
  mul_nonneg (prod_nonneg fun e _ => hπ0 e) (prod_nonneg fun g _ => by linarith [hπ1 g])

include hπ0 hπ1 in
lemma suppI_nonneg (τ : Finset (Fin n)) : 0 ≤ suppI K π τ :=
  sum_nonneg fun M _ => mul_nonneg (pM_nonneg hπ0 hπ1 M) (by split_ifs <;> norm_num)

/-- The probability that `e ∈ K` is marked and every marked edge lies inside `C_e` is
`π_e ∏_{f : C_f ⊄ C_e} (1 - π_f)`. -/
lemma prob_inside {e : Finset (Fin n)} (he : e ∈ K) :
    ∑ M ∈ K.powerset, pM K π M * (if e ∈ M ∧ ∀ f ∈ M, f ⊆ e then 1 else 0) =
      π e * ∏ f ∈ K.filter (fun f => ¬ f ⊆ e), (1 - π f) := by
  set a : Finset (Fin n) → ℝ := fun g => if g ⊆ e then π g else 0
  set c : Finset (Fin n) → ℝ := fun g => if g = e then 0 else 1 - π g
  have hterm : ∀ M ∈ K.powerset, pM K π M * (if e ∈ M ∧ ∀ f ∈ M, f ⊆ e then 1 else 0) =
      (∏ g ∈ M, a g) * ∏ g ∈ K \ M, c g := by
    intro M hM
    have hMK := mem_powerset.mp hM
    by_cases h : e ∈ M ∧ ∀ f ∈ M, f ⊆ e
    · rw [if_pos h, mul_one, pM]
      congr 1
      · exact prod_congr rfl fun g hg => by simp [a, h.2 g hg]
      · exact prod_congr rfl fun g hg => by
          have : g ≠ e := fun hge => (mem_sdiff.mp hg).2 (hge ▸ h.1)
          simp [c, this]
    · rw [if_neg h, mul_zero]
      rcases not_and_or.mp h with h1 | h1
      · rw [prod_eq_zero (i := e) (mem_sdiff.mpr ⟨he, h1⟩) (by simp [c]), mul_zero]
      · push Not at h1
        obtain ⟨f, hf, hfe⟩ := h1
        rw [prod_eq_zero (i := f) hf (by simp [a, hfe]), zero_mul]
  rw [sum_congr rfl hterm, sum_prod_ite K a c]
  have hpt : ∀ g ∈ K, a g + c g =
      (if g = e then π g else 1) * (if ¬ g ⊆ e then 1 - π g else 1) := by
    intro g _
    by_cases hge : g = e
    · subst hge; simp [a, c]
    · by_cases hsub : g ⊆ e
      · simp [a, c, hge, hsub]
      · simp [a, c, hge, hsub]
  rw [prod_congr rfl hpt, prod_mul_distrib, prod_ite_eq' K e, if_pos he, ← prod_filter]

include hπ0 hπ1 in
/-- **Proposition 8.9 (`prop:modelbounds`), first bound.**  Under the irreversible model, for
every edge `e` with `C_e` non-trivial, `m_{σ_e} ≥ π_e ∏_{f : C_f ⊄ C_e} (1 - π_f)`. -/
theorem suppI_edge_ge {e : Finset (Fin n)} (he : e ∈ K) (hnt : Nontriv e) :
    π e * ∏ f ∈ K.filter (fun f => ¬ f ⊆ e), (1 - π f) ≤ suppI K π e := by
  rw [← prob_inside he]
  refine sum_le_sum fun M hM => mul_le_mul_of_nonneg_left ?_ (pM_nonneg hπ0 hπ1 M)
  by_cases h : e ∈ M ∧ ∀ f ∈ M, f ⊆ e
  · have hY : ones M = e := by
      ext x
      rw [mem_ones]
      exact ⟨fun ⟨f, hf, hx⟩ => h.2 f hf hx, fun hx => ⟨e, h.1, hx⟩⟩
    have : Proposes M e := ⟨hY ▸ hnt, Or.inl hY⟩
    rw [if_pos h, if_pos this]
  · rw [if_neg h]; split_ifs <;> norm_num

end rates

/-- Without two marked edges of disjoint clades, the marked edges form a chain and `ones M` is the
largest marked clade, or empty. -/
lemma chain_ones {K M : Finset (Finset (Fin n))} (hK : Attraction.Laminar K) (hMK : M ⊆ K)
    (hno : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ Disjoint e f) :
    ones M = ∅ ∨ ∃ e ∈ M, ones M = e := by
  rcases M.eq_empty_or_nonempty with rfl | hne
  · left; simp [ones]
  · right
    obtain ⟨e, he, hmax⟩ := exists_max_image M card hne
    refine ⟨e, he, ?_⟩
    ext x
    rw [mem_ones]
    refine ⟨fun ⟨f, hf, hx⟩ => ?_, fun hx => ⟨e, he, hx⟩⟩
    by_cases hfe : f = e
    · exact hfe ▸ hx
    · rcases hK f (hMK hf) e (hMK he) hfe with hd | hsub | hsub
      · exact absurd hd (hno f hf e he hfe)
      · exact absurd (card_lt_card hsub) (not_lt.mpr (hmax f hf))
      · exact hsub.1 hx

/-- A split that is not the split of an edge is proposed only when two edges with disjoint
clades are marked. -/
lemma proposes_pair {K M : Finset (Finset (Fin n))} (hK : Attraction.Laminar K) (hMK : M ⊆ K)
    {τ : Finset (Fin n)} (hτ : ∀ e ∈ K, e ≠ τ ∧ e ≠ τᶜ) (hP : Proposes M τ) :
    ∃ S ∈ disjPairs K, S ⊆ M := by
  by_contra hno
  have hno' : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ Disjoint e f := by
    intro e he f hf hef hd
    apply hno
    refine ⟨{e, f}, mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset (hMK he) (singleton_subset_iff.mpr (hMK hf)), card_pair hef⟩, ?_⟩,
      insert_subset he (singleton_subset_iff.mpr hf)⟩
    intro x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hd
    · exact hd.symm
    · exact absurd rfl hxy
  obtain ⟨hnt, hside⟩ := hP
  rcases chain_ones hK hMK hno' with h | ⟨e, he, h⟩
  · rw [h] at hnt; have := hnt.1; simp at this
  · rw [h] at hside
    rcases hside with h1 | h1
    · exact (hτ e (hMK he)).1 h1
    · exact (hτ e (hMK he)).2 h1

section rates2

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1)

include hπ0 hπ1 in
/-- The probability that two edges with disjoint clades are marked is at most `D`. -/
lemma pair_prob_le :
    ∑ M ∈ K.powerset, pM K π M * (if ∃ S ∈ disjPairs K, S ⊆ M then 1 else 0) ≤ D K π := by
  have hp := pM_nonneg (K := K) hπ0 hπ1
  calc ∑ M ∈ K.powerset, pM K π M * (if ∃ S ∈ disjPairs K, S ⊆ M then 1 else 0)
      ≤ ∑ M ∈ K.powerset, ∑ S ∈ disjPairs K, (if S ⊆ M then pM K π M else 0) := by
        refine sum_le_sum fun M _ => ?_
        split_ifs with h
        · obtain ⟨S₀, hS₀, hS₀M⟩ := h
          rw [mul_one]
          refine le_trans ?_ (single_le_sum (f := fun S => if S ⊆ M then pM K π M else 0)
            (fun S _ => by split_ifs <;> first | exact hp M | exact le_rfl) hS₀)
          rw [if_pos hS₀M]
        · rw [mul_zero]
          exact sum_nonneg fun S _ => by split_ifs <;> first | exact hp M | exact le_rfl
    _ = ∑ S ∈ disjPairs K, ∏ e ∈ S, π e := by
        rw [sum_comm]
        refine sum_congr rfl fun S hS => ?_
        have hSK : S ⊆ K := (mem_powersetCard.mp (mem_filter.mp hS).1).1
        exact sum_superset (π := π) hSK
    _ = D K π := rfl

include hπ0 in
lemma D_nonneg : 0 ≤ D K π := sum_nonneg fun _ _ => prod_nonneg fun e _ => hπ0 e

include hπ0 hπ1 in
/-- A split that is not the split of an edge has support at most `D`. -/
theorem suppI_false_le (hK : Attraction.Laminar K) {τ : Finset (Fin n)}
    (hτ : ∀ e ∈ K, e ≠ τ ∧ e ≠ τᶜ) : suppI K π τ ≤ D K π := by
  refine le_trans (sum_le_sum fun M hM => mul_le_mul_of_nonneg_left ?_ (pM_nonneg hπ0 hπ1 M))
    (pair_prob_le hπ0 hπ1)
  by_cases hP : Proposes M τ
  · rw [if_pos hP, if_pos (proposes_pair hK (mem_powerset.mp hM) hτ hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num

include hπ0 hπ1 in
/-- **Proposition 8.9 (`prop:modelbounds`), second bound.**  Under the irreversible model, for any
set `Fs` of splits none of which is the split of an edge, and no two of which are complementary
(each split counted once), `∑_{τ ∈ Fs} m_τ ≤ ∑_{{e,f} : C_e ∩ C_f = ∅} π_e π_f`. -/
theorem false_mass_le (hK : Attraction.Laminar K) (Fs : Finset (Finset (Fin n)))
    (hFs : ∀ τ ∈ Fs, ∀ e ∈ K, e ≠ τ ∧ e ≠ τᶜ) (hc : ∀ τ ∈ Fs, τᶜ ∉ Fs) :
    ∑ τ ∈ Fs, suppI K π τ ≤ D K π := by
  have hswap : ∑ τ ∈ Fs, suppI K π τ =
      ∑ M ∈ K.powerset, pM K π M * ((Fs.filter fun τ => Proposes M τ).card : ℝ) := by
    unfold suppI
    rw [sum_comm]
    refine sum_congr rfl fun M _ => ?_
    rw [← mul_sum, sum_boole]
  rw [hswap]
  refine le_trans (sum_le_sum fun M hM => mul_le_mul_of_nonneg_left ?_ (pM_nonneg hπ0 hπ1 M))
    (pair_prob_le hπ0 hπ1)
  have hle1 : (Fs.filter fun τ => Proposes M τ).card ≤ 1 := by
    refine card_le_one.mpr fun x hx y hy => ?_
    obtain ⟨hxF, -, hx⟩ := (by simpa using hx : x ∈ Fs ∧ Proposes M x)
    obtain ⟨hyF, -, hy⟩ := (by simpa using hy : y ∈ Fs ∧ Proposes M y)
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hx.symm.trans hy
    · exact absurd (show xᶜ ∈ Fs by rw [← hx, hy, compl_compl]; exact hyF) (hc x hxF)
    · exact absurd (show xᶜ ∈ Fs by rw [← hx, hy]; exact hyF) (hc x hxF)
    · exact compl_injective (hx.symm.trans hy)
  by_cases hex : ∃ S ∈ disjPairs K, S ⊆ M
  · rw [if_pos hex]; exact_mod_cast hle1
  · rw [if_neg hex]
    have : (Fs.filter fun τ => Proposes M τ) = ∅ := by
      refine filter_eq_empty_iff.mpr fun τ hτ hP => hex ?_
      exact proposes_pair hK (mem_powerset.mp hM) (hFs τ hτ) hP
    rw [this, card_empty]; norm_num

include hπ0 hπ1 in
/-- **Proposition 8.9, second bound, in the report's form.**  Let `T` contain the split of every
edge with non-trivial clade, by its side away from `r`.  The total expected support of the false
splits, each counted once by its side away from `r`, is at most
`∑_{{e,f} : C_e ∩ C_f = ∅} π_e π_f`. -/
theorem false_mass_sides (hK : Attraction.Laminar K) (r : Fin n) (T : Finset (Finset (Fin n)))
    (hKT : ∀ e ∈ K, Nontriv e → away r e ∈ T) :
    ∑ τ ∈ univ.filter (fun τ => IsSide r τ ∧ τ ∉ T), suppI K π τ ≤ D K π := by
  refine false_mass_le hπ0 hπ1 hK _ (fun τ hτ e he => ?_) (fun τ hτ hτc => ?_)
  · obtain ⟨⟨hr, hnt⟩, hτT⟩ := (by simpa using hτ : IsSide r τ ∧ τ ∉ T)
    constructor
    · rintro rfl
      exact hτT (by simpa [away, hr] using hKT e he hnt)
    · rintro rfl
      have hr' : r ∈ τᶜ := mem_compl.mpr hr
      exact hτT (by simpa [away, hr'] using hKT τᶜ he (nontriv_compl.mpr hnt))
  · obtain ⟨⟨hr, -⟩, -⟩ := (by simpa using hτ : IsSide r τ ∧ τ ∉ T)
    obtain ⟨⟨hr', -⟩, -⟩ := (by simpa using hτc : IsSide r τᶜ ∧ τᶜ ∉ T)
    exact hr' (mem_compl.mpr hr)

end rates2

/-! ### Corollary 8.10, a sufficient condition -/

section global

variable {K : Finset (Finset (Fin n))} {π : Finset (Fin n) → ℝ}
  (hπ0 : ∀ e, 0 ≤ π e) (hπ1 : ∀ e, π e ≤ 1)

include hπ0 hπ1 in
/-- **Corollary 8.10 (`cor:modelglobal`), a sufficient condition.**  Let `T` be binary, with every
split of `T` the split of some edge (`hTK`; when the root subdivides an internal edge, either half
will do) and the split of every edge with non-trivial clade in `T` (`hKT`, by its side away from
`r`).  If `π_e ∏_{f ∈ K} (1 - π_f) ≥ c` for every edge with non-trivial clade and
`c > ∑_{{e,f} : C_e ∩ C_f = ∅} π_e π_f` (in the report `c` is the minimum), then global separation
holds for `m`, `T` is the unique solution of the problem for `m`, and the margin inequality holds
with `γ = c - D > 0`. -/
theorem model_global (hK : Attraction.Laminar K) (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : IsBinary r T) (hKT : ∀ e ∈ K, Nontriv e → away r e ∈ T)
    (hTK : ∀ σ ∈ T, ∃ e ∈ K, e = σ ∨ e = σᶜ) (c : ℝ)
    (hc : ∀ e ∈ K, Nontriv e → c ≤ π e * ∏ f ∈ K, (1 - π f)) (hD : D K π < c) :
    (∀ σ ∈ T, ∀ τ, IsSide r τ → τ ∉ T → suppI K π τ < suppI K π σ) ∧
      IsUniqueSolution r (suppI K π) T ∧ 0 < c - D K π ∧
      ∀ S, IsSystem r S → S ≠ T →
        (c - D K π) * (T \ S).card ≤ ∑ σ ∈ T \ S, suppI K π σ - ∑ σ ∈ S \ T, suppI K π σ := by
  -- true splits: at least `c`
  have htrue : ∀ σ ∈ T, c ≤ suppI K π σ := by
    intro σ hσ
    obtain ⟨e, he, hes⟩ := hTK σ hσ
    have hnt : Nontriv e := by
      rcases hes with rfl | rfl
      · exact (hT.1.1 e hσ).2
      · exact nontriv_compl.mpr (hT.1.1 σ hσ).2
    have hsupp : suppI K π e = suppI K π σ := by
      rcases hes with rfl | rfl
      · rfl
      · exact suppI_compl K π σ
    have hfilt : ∏ f ∈ K, (1 - π f) ≤ ∏ f ∈ K.filter (fun f => ¬ f ⊆ e), (1 - π f) := by
      rw [← prod_filter_mul_prod_filter_not K (fun f => ¬ f ⊆ e)]
      exact mul_le_of_le_one_right (prod_nonneg fun f _ => by linarith [hπ1 f])
        (prod_le_one₀ (fun f _ => by linarith [hπ1 f]) fun f _ => by linarith [hπ0 f])
    calc c ≤ π e * ∏ f ∈ K, (1 - π f) := hc e he hnt
      _ ≤ π e * ∏ f ∈ K.filter (fun f => ¬ f ⊆ e), (1 - π f) :=
          mul_le_mul_of_nonneg_left hfilt (hπ0 e)
      _ ≤ suppI K π e := suppI_edge_ge hπ0 hπ1 he hnt
      _ = suppI K π σ := hsupp
  -- false splits: at most `D`
  have hfalse : ∀ τ, IsSide r τ → τ ∉ T → suppI K π τ ≤ D K π := by
    intro τ ⟨hr, hnt⟩ hτT
    refine suppI_false_le hπ0 hπ1 hK fun e he => ⟨?_, ?_⟩
    · rintro rfl
      exact hτT (by simpa [away, hr] using hKT e he hnt)
    · rintro rfl
      have hr' : r ∈ τᶜ := mem_compl.mpr hr
      exact hτT (by simpa [away, hr'] using hKT τᶜ he (nontriv_compl.mpr hnt))
  have hglob : ∀ σ ∈ T, ∀ τ, IsSide r τ → τ ∉ T → suppI K π τ < suppI K π σ :=
    fun σ hσ τ hτ hτT => by linarith [htrue σ hσ, hfalse τ hτ hτT]
  have hD0 := D_nonneg (K := K) hπ0
  refine ⟨hglob, global_separation hT _ (fun A _ => suppI_nonneg hπ0 hπ1 A) hglob,
    by linarith, fun S hS hne => ?_⟩
  obtain ⟨-, hcard, -⟩ := displacement_matching hT hS hne
  have h1 : (T \ S).card * c ≤ ∑ σ ∈ T \ S, suppI K π σ := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun σ hσ => htrue σ (mem_sdiff.mp hσ).1
  have h2 : ∑ σ ∈ S \ T, suppI K π σ ≤ (S \ T).card * D K π := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun σ hσ => hfalse σ (hS.1 σ (mem_sdiff.mp hσ).1) (mem_sdiff.mp hσ).2
  have h3 : ((S \ T).card : ℝ) ≤ (T \ S).card := by exact_mod_cast hcard
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

include hπ0 hπ1 in
/-- **Corollary 8.10 (`cor:modelglobal`), the estimator is consistent.**  Under the hypotheses of
`model_global`, for units with the expected supports of the irreversible model (independent for
each split, `[0,1]`-valued, splits outside `R` never proposed), the probability that some other
compatible set of splits is at least as heavy as `T` is at most `2 |R| exp(-L (c - D)²/2)`
(Theorem 7.4(a) with `γ = c - D`). -/
theorem model_consistency (hK : Attraction.Laminar K) (r : Fin n) (T : Finset (Finset (Fin n)))
    (hT : IsBinary r T) (hKT : ∀ e ∈ K, Nontriv e → away r e ∈ T)
    (hTK : ∀ σ ∈ T, ∃ e ∈ K, e = σ ∨ e = σᶜ) (c : ℝ)
    (hc : ∀ e ∈ K, Nontriv e → c ≤ π e * ∏ f ∈ K, (1 - π f)) (hD : D K π < c)
    {L : ℕ} (hL : 0 < L) (Y : Finset (Fin n) → Fin L → Ω → ℝ)
    (hmeas : ∀ σ u, Measurable (Y σ u)) (hb : ∀ σ u ω, Y σ u ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : ∀ σ, iIndepFun (Y σ) μ) (hmean : ∀ σ u, μ[Y σ u] = suppI K π σ)
    (R : Finset (Finset (Fin n))) (hR : ∀ σ ∉ R, ∀ u ω, Y σ u ω = 0)
    (hmR : ∀ σ ∉ R, suppI K π σ = 0) :
    μ.real {ω | ∃ S, IsSystem r S ∧ S ≠ T ∧
        ∑ σ ∈ T, (∑ u, Y σ u ω) / L ≤ ∑ σ ∈ S, (∑ u, Y σ u ω) / L} ≤
      2 * R.card * Real.exp (-L * (c - D K π) ^ 2 / 2) := by
  obtain ⟨-, -, hγ, hgap⟩ := model_global hπ0 hπ1 hK r T hT hKT hTK c hc hD
  exact Consistency.consistency r T hT _ _ hγ hgap hL Y hmeas hb hind hmean R hR hmR

end global

end Stemma.Irreversible
