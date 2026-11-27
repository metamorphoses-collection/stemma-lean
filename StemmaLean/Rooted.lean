/-
The rooted analogue (Proposition 6.10 of the technical report, `prop:rooted`): Lemma 6.1 and
Theorems 6.2, 6.3 for clusters.

A rooted stemma is represented by its proper clusters: subsets of the witnesses `Fin n` of size
between `2` and `n - 1`, pairwise laminar (disjoint or nested).  A binary rooted stemma is a
laminar family of exactly `n - 2` proper clusters (`IsBinR`).  The tree side goes through an
outgroup: `isBinR_iff_outgroup` shows that `IsBinR T` holds exactly when the images of `T` on
`Fin (n + 1)` form a binary split system away from the new witness, and
`BinaryTree.isBinR_iff_rooted_tree` turns this into binary trees.  Fact (i), at most `n - 2` proper
clusters, is proved from `Splits.laminar_card`; positivity of true supports uses a crossing
cluster `{a, c}` with `a ∈ C`, `c ∉ C` (not the report's child-and-sibling construction).
The proofs are those of `Splits.lean` with laminarity in place of compatibility.
-/
import Mathlib
import StemmaLean.Splits

namespace Stemma.Rooted

open Finset Splits

variable {n : ℕ}

/-- Two clusters are compatible when laminar: disjoint or nested. -/
def Lam (A C : Finset (Fin n)) : Prop := Disjoint A C ∨ A ⊆ C ∨ C ⊆ A

lemma lam_symm {A C : Finset (Fin n)} (h : Lam A C) : Lam C A := by
  unfold Lam at *; rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma lam_self (A : Finset (Fin n)) : Lam A A := Or.inr (Or.inl subset_rfl)

/-- A proper cluster: between `2` and `n - 1` witnesses. -/
def IsCluster (A : Finset (Fin n)) : Prop := 2 ≤ A.card ∧ A ≠ univ

/-- A laminar set of proper clusters: the clusters of a rooted stemma. -/
def IsHier (S : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ S, IsCluster A) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Lam a b

/-- The proper clusters of a binary rooted stemma: a laminar set of exactly `n - 2` of them. -/
def IsBinR (T : Finset (Finset (Fin n))) : Prop := IsHier T ∧ T.card = n - 2

/-- Total weight. -/
def wtR (w : Finset (Fin n) → ℝ) (S : Finset (Finset (Fin n))) : ℝ := ∑ σ ∈ S, w σ

/-- `T` is the unique solution among laminar sets of proper clusters of positive weight. -/
def IsUniqueSolutionR (w : Finset (Fin n) → ℝ) (T : Finset (Finset (Fin n))) : Prop :=
  IsHier T ∧ (∀ σ ∈ T, 0 < w σ) ∧
    ∀ S, IsHier S → (∀ τ ∈ S, 0 < w τ) → S ≠ T → wtR w S < wtR w T

/-- **Proposition 6.10 (`prop:rooted`), fact (i).**  A laminar family of distinct proper clusters
has at most `n - 2` members. -/
theorem card_le_rooted {S : Finset (Finset (Fin n))} (hS : IsHier S) : S.card ≤ n - 2 := by
  rcases S.eq_empty_or_nonempty with h | ⟨A, hA⟩
  · simp [h]
  have hUS : (univ : Finset (Fin n)) ∉ S := fun hU => (hS.1 _ hU).2 rfl
  have hA2 := (hS.1 A hA).1
  have hlt : A.card < (univ : Finset (Fin n)).card :=
    card_lt_card (ssubset_of_subset_of_ne (subset_univ A) (hS.1 A hA).2)
  have hL : Laminar (insert univ S) := by
    intro X hX Y hY
    rw [mem_insert] at hX hY
    rcases hX with hX | hX <;> rcases hY with hY | hY
    · rw [hX, hY]; exact Or.inr (Or.inl subset_rfl)
    · rw [hX]; exact Or.inr (Or.inr (subset_univ Y))
    · rw [hY]; exact Or.inr (Or.inl (subset_univ X))
    · by_cases e : X = Y
      · rw [e]; exact Or.inr (Or.inl subset_rfl)
      · exact hS.2 X hX Y hY e
  have hb : ∀ X ∈ insert univ S, X ⊆ univ ∧ 2 ≤ X.card := by
    intro X hX
    rw [mem_insert] at hX
    rcases hX with hX | hX
    · rw [hX]; exact ⟨subset_rfl, hA2.trans hlt.le⟩
    · exact ⟨subset_univ X, (hS.1 X hX).1⟩
  rcases laminar_card _ univ (insert univ S) rfl hL hb with h | h
  · exact absurd (h ▸ mem_insert_self univ S) (notMem_empty _)
  · rw [card_insert_of_notMem hUS, card_univ, Fintype.card_fin] at h; omega

/-- Every proper cluster is crossed by a proper cluster: `{a, c}` with `a ≠ b` in `C`, `c ∉ C`. -/
theorem exists_conflict_rooted {σ : Finset (Fin n)} (hσ : IsCluster σ) :
    ∃ τ, IsCluster τ ∧ ¬ Lam τ σ := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by have := hσ.1; omega : 1 < σ.card)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ σ := by
    by_contra h; push Not at h; exact hσ.2 (eq_univ_of_forall h)
  have hac : a ≠ c := fun e => hc (e ▸ ha)
  refine ⟨{a, c}, ⟨by rw [card_pair hac], fun e => ?_⟩, ?_⟩
  · have : b ∈ ({a, c} : Finset (Fin n)) := e ▸ mem_univ b
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact hab h.symm
    · exact hc (h ▸ hb)
  · unfold Lam
    rintro (h | h | h)
    · exact disjoint_left.mp h (mem_insert_self a {c}) ha
    · exact hc (h (by simp))
    · have := h hb
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact hab h.symm
      · exact hc (h ▸ hb)

/-- **Proposition 6.10 (`prop:rooted`), fact (ii), maximality.**  A proper cluster laminar with
every cluster of a binary rooted stemma belongs to it. -/
theorem maximal_rooted {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    {τ : Finset (Fin n)} (hτ : IsCluster τ) (hc : ∀ σ ∈ T, Lam τ σ) : τ ∈ T := by
  by_contra hnot
  have hsys : IsHier (insert τ T) := by
    refine ⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩
    · rw [mem_insert] at hA; rcases hA with rfl | hA
      · exact hτ
      · exact hT.1.1 A hA
    · rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hc b hb
      · exact lam_symm (hc a ha)
      · exact hT.1.2 a ha b hb hab
  have := card_le_rooted hsys
  rw [card_insert_of_notMem hnot, hT.2] at this
  omega

/-! ### Displacement matching (Lemma 6.1 of the report) -/

/-- **Proposition 6.10 (`prop:rooted`), Lemma 6.1 for clusters.**  Let `T` be a binary rooted
stemma (its `n - 2` proper clusters) and `S ≠ T` a laminar set of proper clusters; with
`A = T \ S`, `B = S \ T`: `A ≠ ∅`, `|B| ≤ |A|`, and an injection `B → A` along conflicts
(failures of laminarity), by Hall's theorem. -/
theorem displacement_matching_rooted {T S : Finset (Finset (Fin n))}
    (hT : IsBinR T) (hS : IsHier S) (hne : S ≠ T) :
    (T \ S).Nonempty ∧ (S \ T).card ≤ (T \ S).card ∧
    ∃ φ : ↥(S \ T) → Finset (Fin n), Function.Injective φ ∧
      ∀ τ, φ τ ∈ T \ S ∧ ¬ Lam τ.1 (φ τ) := by
  classical
  -- neighbourhoods along conflicts
  let t : ↥(S \ T) → Finset (Finset (Fin n)) := fun τ => (T \ S).filter (fun σ => ¬ Lam τ.1 σ)
  have hHall : ∀ s : Finset ↥(S \ T), s.card ≤ (s.biUnion t).card := by
    intro s
    set N := s.biUnion t
    set B' := s.map (Function.Embedding.subtype _)
    have hB'S : B' ⊆ S \ T := by
      intro x hx; simp only [B', mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, -, rfl⟩ := hx; exact y.2
    have hNT : N ⊆ T \ S := by
      intro x hx; simp only [N, t, mem_biUnion, mem_filter] at hx
      obtain ⟨_, _, h, _⟩ := hx; exact h
    have hsys : IsHier ((T \ N) ∪ B') := by
      refine ⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩
      · rcases mem_union.mp hA with h | h
        · exact hT.1.1 A (mem_sdiff.mp h).1
        · exact hS.1 A (mem_sdiff.mp (hB'S h)).1
      -- a true split outside `N` is compatible with every member of `B'`
      have cross : ∀ σ ∈ T \ N, ∀ τ ∈ B', Lam τ σ := by
        intro σ hσ τ hτ
        obtain ⟨hσT, hσN⟩ := mem_sdiff.mp hσ
        have hτ' := mem_sdiff.mp (hB'S hτ)
        have hne' : τ ≠ σ := fun e => hτ'.2 (e ▸ hσT)
        by_cases hσS : σ ∈ S
        · exact hS.2 τ hτ'.1 σ hσS hne'
        · by_contra hc
          apply hσN
          simp only [B', mem_map, Function.Embedding.coe_subtype] at hτ
          obtain ⟨y, hy, rfl⟩ := hτ
          simp only [N, t, mem_biUnion, mem_filter]
          exact ⟨y, hy, mem_sdiff.mpr ⟨hσT, hσS⟩, hc⟩
      rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
      · exact hT.1.2 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab
      · exact lam_symm (cross a ha b hb)
      · exact cross b hb a ha
      · exact hS.2 a (mem_sdiff.mp (hB'S ha)).1 b (mem_sdiff.mp (hB'S hb)).1 hab
    have hle := card_le_rooted hsys
    have hdisj : Disjoint (T \ N) B' := by
      rw [disjoint_left]; intro x hx hx'
      exact (mem_sdiff.mp (hB'S hx')).2 (mem_sdiff.mp hx).1
    rw [card_union_of_disjoint hdisj, card_sdiff_of_subset (hNT.trans sdiff_subset), hT.2.symm,
      card_map] at hle
    have : N.card ≤ T.card := card_le_card (hNT.trans sdiff_subset)
    omega
  obtain ⟨φ, hφinj, hφ⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hφ' : ∀ τ, φ τ ∈ T \ S ∧ ¬ Lam τ.1 (φ τ) := fun τ => by
    have := hφ τ; simp only [t, mem_filter] at this; exact this
  refine ⟨?_, ?_, φ, hφinj, hφ'⟩
  · rw [nonempty_iff_ne_empty]
    intro hA
    have hTS : T ⊂ S := ssubset_of_subset_of_ne (sdiff_eq_empty_iff_subset.mp hA) hne.symm
    have := card_lt_card hTS
    have := card_le_rooted hS
    rw [hT.2] at *; omega
  · have h := hHall univ
    have hsub : univ.biUnion t ⊆ T \ S := by
      intro x hx; simp only [t, mem_biUnion, mem_filter] at hx
      obtain ⟨_, _, h, _⟩ := hx; exact h
    have := card_le_card hsub
    rw [card_univ, Fintype.card_coe] at h
    omega


lemma not_mem_of_conflict_rooted {T : Finset (Finset (Fin n))} (hT : IsHier T)
    {σ τ : Finset (Fin n)} (hσ : σ ∈ T) (hc : ¬ Lam τ σ) : τ ∉ T := by
  intro hτ
  by_cases e : τ = σ
  · exact hc (e ▸ lam_self σ)
  · exact hc (hT.2 τ hτ σ hσ e)

/-- Local separation for clusters, strong form. -/
theorem local_separation_strong_rooted {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsCluster A → 0 ≤ w A)
    (hloc : ∀ τ σ, IsCluster τ → τ ∉ T → σ ∈ T → ¬ Lam τ σ → w τ < w σ) :
    (∀ σ ∈ T, 0 < w σ) ∧ ∀ S, IsHier S → S ≠ T → wt w S < wt w T := by
  have hpos : ∀ σ ∈ T, 0 < w σ := by
    intro σ hσ
    obtain ⟨τ, hτ, hc⟩ := exists_conflict_rooted (hT.1.1 σ hσ)
    have := hloc τ σ hτ (not_mem_of_conflict_rooted hT.1 hσ hc) hσ hc
    linarith [hw0 τ hτ]
  refine ⟨hpos, fun S hS hne => ?_⟩
  obtain ⟨hA, -, φ, hφinj, hφ⟩ := displacement_matching_rooted hT hS hne
  have hdiff : wt w T - wt w S = ∑ σ ∈ T \ S, w σ - ∑ τ ∈ S \ T, w τ :=
    (Finset.sum_sdiff_sub_sum_sdiff).symm
  -- `w(B) ≤ w(φ(B)) ≤ w(A)`, strictly if `B ≠ ∅`
  have himg : ∑ τ : ↥(S \ T), w (φ τ) = ∑ σ ∈ univ.image φ, w σ :=
    (sum_image (fun x _ y _ h => hφinj h)).symm
  have hsub : univ.image φ ⊆ T \ S := by
    intro x hx; simp only [mem_image] at hx; obtain ⟨y, -, rfl⟩ := hx; exact (hφ y).1
  have hle : ∑ σ ∈ univ.image φ, w σ ≤ ∑ σ ∈ T \ S, w σ :=
    sum_le_sum_of_subset_of_nonneg hsub fun σ hσ _ => (hpos σ (mem_sdiff.mp hσ).1).le
  have hB : ∑ τ ∈ S \ T, w τ = ∑ τ : ↥(S \ T), w τ.1 := (sum_coe_sort _ _).symm
  rcases (S \ T).eq_empty_or_nonempty with hBe | hBne
  · have : 0 < ∑ σ ∈ T \ S, w σ :=
      sum_pos (fun σ hσ => hpos σ (mem_sdiff.mp hσ).1) hA
    rw [hBe, sum_empty] at hdiff
    linarith
  · have hlt : ∑ τ : ↥(S \ T), w τ.1 < ∑ τ : ↥(S \ T), w (φ τ) := by
      apply sum_lt_sum_of_nonempty
      · obtain ⟨x, hx⟩ := hBne; exact ⟨⟨x, hx⟩, mem_univ _⟩
      · intro τ _
        have hτ := mem_sdiff.mp τ.2
        exact hloc τ.1 (φ τ) (hS.1 _ hτ.1) hτ.2 (mem_sdiff.mp (hφ τ).1).1 (hφ τ).2
    linarith

/-- **Proposition 6.10 (`prop:rooted`), Theorem 6.2 for clusters.**  Let `T` be a binary rooted
stemma and `w ≥ 0` on proper clusters.  If `w τ < w σ` whenever a false cluster `τ` and a true
cluster `σ` are not laminar, `T` is the unique solution among laminar sets of proper clusters. -/
theorem local_separation_rooted {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsCluster A → 0 ≤ w A)
    (hloc : ∀ τ σ, IsCluster τ → τ ∉ T → σ ∈ T → ¬ Lam τ σ → w τ < w σ) :
    IsUniqueSolutionR w T := by
  obtain ⟨hpos, hlt⟩ := local_separation_strong_rooted hT w hw0 hloc
  exact ⟨hT.1, hpos, fun S hS _ hne => hlt S hS hne⟩

/-- **Proposition 6.10 (`prop:rooted`), Theorem 6.3 for clusters.**  If every true cluster is
heavier than every false proper cluster, `T` is the unique solution. -/
theorem global_separation_rooted {T : Finset (Finset (Fin n))} (hT : IsBinR T)
    (w : Finset (Fin n) → ℝ) (hw0 : ∀ A, IsCluster A → 0 ≤ w A)
    (hglob : ∀ σ ∈ T, ∀ τ, IsCluster τ → τ ∉ T → w τ < w σ) :
    IsUniqueSolutionR w T :=
  local_separation_rooted hT w hw0 fun τ σ hτ hτT hσ _ => hglob σ hσ τ hτ hτT


/-! ### The outgroup bridge to unrooted splits -/

/-- Adding an outgroup: a cluster on `Fin n` becomes a side on `Fin (n + 1)` away from the new
witness `Fin.last n`. -/
def outg : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
  ⟨Finset.map Fin.castSuccEmb, Finset.map_injective _⟩

lemma outg_apply (A : Finset (Fin n)) : outg A = A.map Fin.castSuccEmb := rfl

lemma last_notMem_outg (A : Finset (Fin n)) : Fin.last n ∉ outg A := by
  simp [outg_apply, Fin.castSucc_ne_last]

lemma inter_compl_eq_empty {α : Type*} [Fintype α] [DecidableEq α] {A C : Finset α} :
    A ∩ Cᶜ = ∅ ↔ A ⊆ C := by
  simp [Finset.eq_empty_iff_forall_notMem, Finset.subset_iff]

/-- A cluster is proper exactly when its outgroup image is a non-trivial side. -/
lemma nontriv_outg (A : Finset (Fin n)) : Nontriv (outg A) ↔ IsCluster A := by
  have hc : (outg A).card = A.card := card_map _
  have hcc : (outg A)ᶜ.card = n + 1 - A.card := by
    rw [card_compl, Fintype.card_fin, hc]
  have hle : A.card ≤ n := by simpa using card_le_univ A
  have hu : A = univ ↔ A.card = n := by
    rw [← card_eq_iff_eq_univ, Fintype.card_fin]
  unfold Nontriv IsCluster
  rw [hc, hcc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => by have := hu.mp e; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by have := mt hu.mpr h2; omega⟩

/-- Compatibility of outgroup images is laminarity. -/
lemma compat_outg (A C : Finset (Fin n)) : Compat (outg A) (outg C) ↔ Lam A C := by
  have e1 : outg A ∩ outg C = ∅ ↔ Disjoint A C := by
    rw [outg_apply, outg_apply, ← map_inter, map_eq_empty, disjoint_iff_inter_eq_empty]
  have e2 : outg A ∩ (outg C)ᶜ = ∅ ↔ A ⊆ C := by
    rw [inter_compl_eq_empty, outg_apply, outg_apply, map_subset_map]
  have e3 : (outg A)ᶜ ∩ outg C = ∅ ↔ C ⊆ A := by
    rw [inter_comm, inter_compl_eq_empty, outg_apply, outg_apply, map_subset_map]
  have e4 : (outg A)ᶜ ∩ (outg C)ᶜ ≠ ∅ := by
    intro h
    have : Fin.last n ∈ (outg A)ᶜ ∩ (outg C)ᶜ := by
      simp only [mem_inter, mem_compl]; exact ⟨last_notMem_outg A, last_notMem_outg C⟩
    rw [h] at this; exact notMem_empty _ this
  unfold Compat Lam
  rw [e1, e2, e3]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h e4
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

/-- **Rooted stemmata as unrooted stemmata with an outgroup.**  A family `T` of clusters on `Fin n`
is the cluster set of a binary rooted stemma (`IsBinR`) if and only if its image on `Fin (n + 1)`,
with the new witness `Fin.last n` as the root, is the split system of a binary stemma, by the sides
away from that witness.  With `BinaryTree.isBinary_iff_binary_tree` this is the bridge to binary
trees (`BinaryTree.isBinR_iff_rooted_tree`). -/
theorem isBinR_iff_outgroup (T : Finset (Finset (Fin n))) :
    IsBinR T ↔ IsBinary (Fin.last n) (T.map outg) := by
  constructor
  · rintro ⟨⟨hcl, hlam⟩, hcard⟩
    refine ⟨⟨fun A' hA' => ?_, fun a' ha' b' hb' hab => ?_⟩, ?_⟩
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp hA'
      exact ⟨last_notMem_outg A, (nontriv_outg A).mpr (hcl A hA)⟩
    · obtain ⟨a, ha, rfl⟩ := mem_map.mp ha'
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hb'
      exact (compat_outg a b).mpr (hlam a ha b hb fun e => hab (e ▸ rfl))
    · rw [card_map, hcard]; omega
  · rintro ⟨⟨hside, hcomp⟩, hcard⟩
    refine ⟨⟨fun A hA => ?_, fun a ha b hb hab => ?_⟩, ?_⟩
    · exact (nontriv_outg A).mp (hside _ (mem_map_of_mem _ hA)).2
    · exact (compat_outg a b).mp (hcomp _ (mem_map_of_mem _ ha) _ (mem_map_of_mem _ hb)
        fun e => hab (outg.injective e))
    · rw [card_map] at hcard; omega

end Stemma.Rooted
