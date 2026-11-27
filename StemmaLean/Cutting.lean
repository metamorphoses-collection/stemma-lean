/-
Consistency of the cutting-plane estimator (Theorem 7.14 of the technical report,
`thm:cuttingconsistency`), parts (a) and (b).

A binary stemma is its split system (`Splits.IsBinary`).  It *displays* a partial split `s` (on
the witnesses `s.dom`) if one of its splits restricts to `s`: one side of the split meets `s.dom`
exactly in `s.side` (`Extends`, from `PartialSplits.lean`), or the other side does.

Part (a) needs, in one direction, that every pairwise compatible set of non-trivial splits is
contained in the split system of a binary stemma: resolving the vertices of degree above three of
the tree that Buneman's theorem gives.  Here it is the hypothesis `Resolvable r`, which
`Resolve.lean` proves (`resolvable`), giving the unconditional `completable_iff_displayed'`; the
other direction is proved outright.

Part (b) is proved from Mathlib's strong law of large numbers (`strong_law_ae`, Etemadi's form,
which needs only pairwise independence), for all of the finitely many binary stemmata at once.
Lean proves the almost-sure statement (eventually, along almost every infinite sequence of units)
and derives the report's statement in probability from it.
-/
import Mathlib
import StemmaLean.Size

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped Classical

namespace Stemma.Cutting

open Splits

variable {n : ℕ}

/-! ### Display, joint completability, part (a) -/

/-- The full split with side `σ` restricts to the partial split `s`. -/
def Restricts (σ : Finset (Fin n)) (s : PSplit n) : Prop := Extends s σ ∨ Extends s σᶜ

/-- The split system `T` displays the partial split `s`: some split of `T` restricts to `s`. -/
def Displays (T : Finset (Finset (Fin n))) (s : PSplit n) : Prop := ∃ σ ∈ T, Restricts σ s

/-- A non-trivial partial split: at least two witnesses on each side. -/
def NontrivP (s : PSplit n) : Prop := 2 ≤ s.side.card ∧ 2 ≤ s.other.card

/-- A family of partial splits is jointly completable: each extends to a full split, and the
extensions are pairwise compatible. -/
def JointlyCompletable (P : Finset (PSplit n)) : Prop :=
  ∃ ext : PSplit n → Finset (Fin n), (∀ s ∈ P, Extends s (ext s)) ∧
    ∀ s ∈ P, ∀ t ∈ P, Compat (ext s) (ext t)

/-- Every pairwise compatible set of non-trivial splits lies in the split system of a binary
stemma (Buneman's theorem, Prop. 2.2, and the resolution of polytomies; not formalised). -/
def Resolvable (r : Fin n) : Prop := ∀ S, IsSystem r S → ∃ T, IsBinary r T ∧ S ⊆ T

lemma compat_compl_right {A C : Finset (Fin n)} : Compat A Cᶜ ↔ Compat A C :=
  ⟨fun h => compat_symm (compat_compl_left.mp (compat_symm h)),
    fun h => compat_symm (compat_compl_left.mpr (compat_symm h))⟩

/-- Displayed by a binary stemma implies jointly completable (no hypothesis needed). -/
theorem completable_of_displayed {r : Fin n} {T : Finset (Finset (Fin n))} (hT : IsBinary r T)
    (P : Finset (PSplit n)) (hd : ∀ s ∈ P, Displays T s) : JointlyCompletable P := by
  choose! σ hσT hσ using hd
  refine ⟨fun s => if Extends s (σ s) then σ s else (σ s)ᶜ, fun s hs => ?_, fun s hs t ht => ?_⟩
  · simp only; split_ifs with h
    · exact h
    · exact (hσ s hs).resolve_left h
  · have hst : Compat (σ s) (σ t) := by
      by_cases e : σ s = σ t
      · rw [e]; exact compat_self _
      · exact hT.1.2 _ (hσT s hs) _ (hσT t ht) e
    simp only
    split_ifs
    · exact hst
    · exact compat_compl_right.mpr hst
    · exact compat_compl_left.mpr hst
    · exact compat_compl_left.mpr (compat_compl_right.mpr hst)

/-- **Theorem 7.14(a) (`thm:cuttingconsistency`).**  A family of non-trivial partial splits is
jointly completable if and only if some binary stemma displays every member.  The direction
"completable ⇒ displayed" uses the hypothesis `Resolvable r` (Buneman's theorem and the resolution
of polytomies, not formalised); the converse needs no hypothesis (`completable_of_displayed`). -/
theorem completable_iff_displayed (r : Fin n) (hres : Resolvable r) (P : Finset (PSplit n))
    (hP : ∀ s ∈ P, NontrivP s) :
    JointlyCompletable P ↔ ∃ T, IsBinary r T ∧ ∀ s ∈ P, Displays T s := by
  constructor
  · rintro ⟨ext, hext, hc⟩
    set S := P.image (fun s => away r (ext s))
    have hnt : ∀ s ∈ P, Nontriv (ext s) := fun s hs =>
      Size.nontriv_of_extends (hext s hs) (hP s hs).1 (hP s hs).2
    have hS : IsSystem r S := by
      refine ⟨fun A hA => ?_, fun a ha b hb _ => ?_⟩
      · simp only [S, mem_image] at hA; obtain ⟨s, hs, rfl⟩ := hA; exact isSide_away (hnt s hs)
      · simp only [S, mem_image] at ha hb
        obtain ⟨s, hs, rfl⟩ := ha; obtain ⟨t, ht, rfl⟩ := hb
        rw [compat_away]; exact compat_symm (compat_away.mpr (compat_symm (hc s hs t ht)))
    obtain ⟨T, hT, hST⟩ := hres S hS
    refine ⟨T, hT, fun s hs => ⟨away r (ext s), hST (mem_image_of_mem _ hs), ?_⟩⟩
    unfold Restricts away
    split_ifs
    · right; rw [compl_compl]; exact hext s hs
    · left; exact hext s hs
  · rintro ⟨T, hT, hd⟩
    exact completable_of_displayed hT P hd

/-- **Theorem 7.14(a), the estimator.**  With weights `c ≥ 0` on a finite set `O` of observed
non-trivial partial splits, every jointly completable subfamily weighs at most the display weight
`W T = ∑_{s ∈ O displayed by T} c s` of some binary stemma `T` (under `Resolvable r`), and the
observed splits displayed by any binary stemma form a jointly completable family of weight `W T`.
So the maximum-weight completable family is the set of observed splits displayed by a maximiser
of `W`. -/
theorem estimator_is_display_max (r : Fin n) (hres : Resolvable r) (O : Finset (PSplit n))
    (hO : ∀ s ∈ O, NontrivP s) (c : PSplit n → ℝ) (hc : ∀ s, 0 ≤ c s) :
    (∀ F ⊆ O, JointlyCompletable F →
      ∃ T, IsBinary r T ∧ ∑ s ∈ F, c s ≤ ∑ s ∈ O.filter (Displays T), c s) ∧
    (∀ T, IsBinary r T → JointlyCompletable (O.filter (Displays T))) := by
  refine ⟨fun F hF hJ => ?_, fun T hT => completable_of_displayed hT _ fun s hs =>
    (mem_filter.mp hs).2⟩
  obtain ⟨T, hT, hd⟩ := (completable_iff_displayed r hres F fun s hs => hO s (hF hs)).mp hJ
  refine ⟨T, hT, sum_le_sum_of_subset_of_nonneg (fun s hs => mem_filter.mpr ⟨hF hs, hd s hs⟩)
    fun s _ _ => hc s⟩

/-! ### Part (b): consistency, from the strong law -/

instance : Countable (PSplit n) := by
  refine Function.Injective.countable (f := fun s : PSplit n => (s.dom, s.side)) ?_
  rintro ⟨d, s, h⟩ ⟨d', s', h'⟩ e
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace (Finset (PSplit n))] [MeasurableSingletonClass (Finset (PSplit n))]

/-- The number of partial splits proposed by unit `u` that `T` displays. -/
noncomputable def X (P : ℕ → Ω → Finset (PSplit n)) (T : Finset (Finset (Fin n))) (u : ℕ)
    (ω : Ω) : ℝ := ((P u ω).filter (Displays T)).card

/-- The display weight of `T` on the first `L` units: `W(T) = ∑_{u < L} |P_u displayed by T|`. -/
noncomputable def W (P : ℕ → Ω → Finset (PSplit n)) (L : ℕ) (T : Finset (Finset (Fin n)))
    (ω : Ω) : ℝ := ∑ u ∈ range L, X P T u ω

/-- The expected number of partial splits proposed by a unit that `T` displays. -/
noncomputable def M (μ : Measure Ω) (P : ℕ → Ω → Finset (PSplit n))
    (T : Finset (Finset (Fin n))) : ℝ := μ[X P T 0]

lemma measurable_X {P : ℕ → Ω → Finset (PSplit n)} (hP : ∀ u, Measurable (P u))
    (T : Finset (Finset (Fin n))) (u : ℕ) : Measurable (X P T u) :=
  (measurable_of_countable (fun F : Finset (PSplit n) => ((F.filter (Displays T)).card : ℝ))).comp
    (hP u)

lemma measurable_W {P : ℕ → Ω → Finset (PSplit n)} (hP : ∀ u, Measurable (P u)) (L : ℕ)
    (T : Finset (Finset (Fin n))) : Measurable (W P L T) := by
  unfold W
  exact Finset.measurable_sum (range L) fun u _ => measurable_X hP T u

/-- Strong law, for every `T` at once: almost surely `W(T)/L → M(T)` for all `T`. -/
lemma strong_law_all (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B) :
    ∀ᵐ ω ∂μ, ∀ T : Finset (Finset (Fin n)),
      Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * W P L T ω) atTop (𝓝 (M μ P T)) := by
  rw [ae_all_iff]
  intro T
  have g : Measurable (fun F : Finset (PSplit n) => ((F.filter (Displays T)).card : ℝ)) :=
    measurable_of_countable _
  have hint : Integrable (X P T 0) μ := by
    refine Integrable.of_bound (C := B) (measurable_X hP T 0).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    unfold X
    exact_mod_cast (card_filter_le _ _).trans (hB 0 ω)
  have H := strong_law_ae (μ := μ) (fun u => X P T u) hint
    (fun i j hij => (hindep hij).comp g g) (fun u => (hident u).comp g)
  filter_upwards [H] with ω hω
  simpa [W, M, smul_eq_mul] using hω

/-- From an almost-sure eventual event to probability tending to one. -/
lemma prob_tendsto_of_ae_eventually {G : ℕ → Set Ω} (hG : ∀ L, MeasurableSet (G L))
    (h : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ω ∈ G L) : Tendsto (fun L => μ (G L)ᶜ) atTop (𝓝 0) := by
  set Bs : ℕ → Set Ω := fun L => ⋃ L' ≥ L, (G L')ᶜ
  have hBm : ∀ L, NullMeasurableSet (Bs L) μ := fun L =>
    (MeasurableSet.biUnion (Set.to_countable _) fun L' _ => (hG L').compl).nullMeasurableSet
  have hanti : Antitone Bs := fun L L' hLL' x hx => by
    simp only [Bs, Set.mem_iUnion] at hx ⊢
    obtain ⟨L'', h1, h2⟩ := hx; exact ⟨L'', hLL'.trans h1, h2⟩
  have hlim := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top _ _⟩
  have hnull : μ (⋂ L, Bs L) = 0 := by
    rw [← nonpos_iff_eq_zero]
    refine (measure_mono_null ?_ (ae_iff.mp h)).le
    intro ω hω
    simp only [Bs, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff] at hω
    simp only [Set.mem_ofPred_eq, eventually_atTop, not_exists, not_forall]
    intro L; obtain ⟨L', h1, h2⟩ := hω L; exact ⟨L', h1, h2⟩
  rw [hnull] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun L => measure_mono fun ω hω => ?_
  simp only [Bs, Set.mem_iUnion]; exact ⟨L, le_rfl, hω⟩

/-- **Theorem 7.14(b) (`thm:cuttingconsistency`), first case.**  Units `P u` (the partial splits
proposed by unit `u`, at most `B` of them) are pairwise independent and identically distributed.
If the binary `T` is the unique maximum of `M` over binary stemmata, then almost surely, for all
large `L`, `T` is the unique maximiser of the display weight `W`, and no other binary stemma
displays every observed partial split that `T` displays (the selected family is displayed by `T`
alone); and the probability that `T` is not the unique maximiser tends to `0`. -/
theorem cutting_consistent (r : Fin n) {T : Finset (Finset (Fin n))}
    (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B)
    (hmax : ∀ T', IsBinary r T' → T' ≠ T → M μ P T' < M μ P T) :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ T', IsBinary r T' → T' ≠ T →
      W P L T' ω < W P L T ω ∧
        ∃ u ∈ range L, ∃ s ∈ P u ω, Displays T s ∧ ¬ Displays T' s) ∧
    Tendsto (fun L => μ {ω | ∀ T', IsBinary r T' → T' ≠ T → W P L T' ω < W P L T ω}ᶜ) atTop
      (𝓝 0) := by
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, ∀ T', IsBinary r T' → T' ≠ T →
      W P L T' ω < W P L T ω := by
    filter_upwards [strong_law_all P hP hindep hident hB] with ω hω
    have : ∀ T' ∈ (univ.filter fun T' => IsBinary r T' ∧ T' ≠ T),
        ∀ᶠ L in atTop, W P L T' ω < W P L T ω := by
      intro T' hT'
      simp only [mem_filter, mem_univ, true_and] at hT'
      have hd := (hω T).sub (hω T')
      have hev := hd.eventually (lt_mem_nhds (sub_pos.mpr (hmax T' hT'.1 hT'.2)))
      filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
      rw [← mul_sub] at hL
      have := (mul_pos_iff_of_pos_left (inv_pos.mpr hLpos)).mp hL
      linarith
    filter_upwards [(eventually_all_finset _).mpr this] with L hL T' h1 h2
    exact hL T' (by simp [h1, h2])
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with ω hω
    filter_upwards [hω] with L hL T' h1 h2
    refine ⟨hL T' h1 h2, ?_⟩
    by_contra hno
    push Not at hno
    have hle : W P L T ω ≤ W P L T' ω := by
      unfold W X
      refine sum_le_sum fun u hu => ?_
      exact_mod_cast card_le_card fun s hs => by
        rw [mem_filter] at hs ⊢; exact ⟨hs.1, hno u hu s hs.1 hs.2⟩
    linarith [hL T' h1 h2]
  · have hmeasG : ∀ L, MeasurableSet
        {ω | ∀ T', IsBinary r T' → T' ≠ T → W P L T' ω < W P L T ω} := by
      intro L
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun T' => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ => measurableSet_lt (measurable_W hP L T') (measurable_W hP L T)
    exact prob_tendsto_of_ae_eventually hmeasG hae

/-- **Theorem 7.14(b), second case.**  If some binary `T'` has `M(T') > M(T)`, then almost surely,
for all large `L`, `W(T) < W(T')`, so `T` is not selected; and the probability that `T` is a
maximiser of `W` (`W(T') ≤ W(T)`) tends to `0`. -/
theorem cutting_inconsistent (P : ℕ → Ω → Finset (PSplit n)) (hP : ∀ u, Measurable (P u))
    (hindep : Pairwise fun i j => IndepFun (P i) (P j) μ)
    (hident : ∀ u, IdentDistrib (P u) (P 0) μ μ) {B : ℕ} (hB : ∀ u ω, (P u ω).card ≤ B)
    {T T' : Finset (Finset (Fin n))} (hlt : M μ P T < M μ P T') :
    (∀ᵐ ω ∂μ, ∀ᶠ L in atTop, W P L T ω < W P L T' ω) ∧
    Tendsto (fun L => μ {ω | W P L T' ω ≤ W P L T ω}) atTop (𝓝 0) := by
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ L in atTop, W P L T ω < W P L T' ω := by
    filter_upwards [strong_law_all P hP hindep hident hB] with ω hω
    have hd := (hω T').sub (hω T)
    have hev := hd.eventually (lt_mem_nhds (sub_pos.mpr hlt))
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
    rw [← mul_sub] at hL
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr hLpos)).mp hL
    linarith
  refine ⟨hae, ?_⟩
  have := prob_tendsto_of_ae_eventually (μ := μ)
    (G := fun L => {ω | W P L T ω < W P L T' ω})
    (fun L => measurableSet_lt (measurable_W hP L T) (measurable_W hP L T')) hae
  refine this.congr fun L => ?_
  congr 1; ext ω; simp

end Stemma.Cutting
