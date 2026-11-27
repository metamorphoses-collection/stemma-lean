/-
Mechanisms of false support: Theorem 8.5(i)–(iii) of the technical report (`thm:mechanisms`),
the classification of what one unit proposes in the attraction model.

A rooted stemma is given by the clades `C_e` of its edges, a family `K` of sets of witnesses.  In
one unit a set `M ⊆ K` of edges innovates; each innovation takes the attractive reading
(`att C = true`) or a reading of its own.  A witness reads the value of the lowest innovating edge
above it (`Lowest`), or the original reading if there is none (`read`).  The unrooted coding
proposes the split of every class of witnesses sharing a reading (`PropU A`: `A` is a class); the
rooted coding proposes the clusters of the classes of non-original readings (`PropR`).

Formalised, for every unit (deterministically):
* (i) `single`: with at most one innovation, every proposal is a split or cluster of the stemma,
  or trivial;
* (ii) `retention_coincidence`: with innovations on disjoint clades `C_e`, `C_f`, the unrooted
  coding proposes `(C_e ∪ C_f) | rest` whatever the readings (when the rest is non-empty), the
  rooted coding proposes the cluster `C_e ∪ C_f` iff both readings are attractive, and every other
  proposal is a split or cluster of the stemma;
* (iii) `overwrite`: with `C_f ⊊ C_e`, both codings propose `C_e \ C_f` unless both readings are
  attractive, and every other proposal is a split or cluster of the stemma.
* `retention_coincidence_report`, `overwrite_report`: (ii) and (iii) with the size conditions of
  the report, a proposal counted only when non-trivial (`SplitNT`: two witnesses on each side;
  `ClusterNT`: two witnesses, not all): the unrooted coding proposes `(C_e ∪ C_f) | rest` when
  `|rest| ≥ 2`; the rooted coding proposes `C_e ∪ C_f` iff both readings are attractive and
  `C_e ∪ C_f ≠ X`; both propose `C_e \ C_f` when `|C_e \ C_f| ≥ 2` (and `C_e ≠ X`), unless both
  readings are attractive.  Every statement holds for each assignment of readings to edges, so the
  independence of the attraction choices across edges, an assumption of the model, is used only by
  the probability bounds.

Not formalised: the probability bounds `Λ_τ ≤ m_τ ≤ Λ_τ + Pr(|M| ≥ 3) ≤ Λ_τ + (∑ π_e)³/6` that
follow by summing over outcomes; they are checked by machine (check C16).
-/
import Mathlib

open Finset
open scoped Classical

namespace Stemma.Mechanisms

variable {n : ℕ}

/-- A reading: the original one, the attractive one, or the own reading of an innovation (named by
its clade). -/
inductive Rd (n : ℕ)
  | orig : Rd n
  | attr : Rd n
  | own : Finset (Fin n) → Rd n
  deriving DecidableEq

/-- `C` is the lowest innovating edge above `x`. -/
def Lowest (M : Finset (Finset (Fin n))) (x : Fin n) (C : Finset (Fin n)) : Prop :=
  C ∈ M ∧ x ∈ C ∧ ∀ D ∈ M, x ∈ D → C ⊆ D

lemma lowest_unique {M : Finset (Finset (Fin n))} {x : Fin n} {C C' : Finset (Fin n)}
    (h : Lowest M x C) (h' : Lowest M x C') : C = C' :=
  subset_antisymm (h.2.2 C' h'.1 h'.2.1) (h'.2.2 C h.1 h.2.1)

/-- The reading of witness `x`. -/
noncomputable def read (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) (x : Fin n) :
    Rd n :=
  if h : ∃ C, Lowest M x C then (if att h.choose then .attr else .own h.choose) else .orig

lemma read_of_lowest {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {x : Fin n}
    {C : Finset (Fin n)} (h : Lowest M x C) :
    read M att x = if att C then .attr else .own C := by
  have hex : ∃ C, Lowest M x C := ⟨C, h⟩
  unfold read
  rw [dif_pos hex, lowest_unique hex.choose_spec h]

lemma read_of_none {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {x : Fin n}
    (h : ∀ C ∈ M, x ∉ C) : read M att x = .orig := by
  unfold read
  rw [dif_neg]
  rintro ⟨C, hC, hx, -⟩
  exact h C hC hx

/-- The class of witnesses with reading `v`. -/
noncomputable def cls (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) (v : Rd n) :
    Finset (Fin n) :=
  univ.filter fun x => read M att x = v

/-- The unrooted coding proposes the split `A | Aᶜ` of the class `A`. -/
def PropU (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ ∃ v, A = cls M att v

/-- The rooted coding proposes the cluster `A`, a class of a non-original reading. -/
def PropR (M : Finset (Finset (Fin n))) (att : Finset (Fin n) → Bool) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ ∃ v, v ≠ .orig ∧ A = cls M att v

/-- The value of an innovation on `C`. -/
def val (att : Finset (Fin n) → Bool) (C : Finset (Fin n)) : Rd n :=
  if att C then .attr else .own C

lemma val_ne_orig (att : Finset (Fin n) → Bool) (C : Finset (Fin n)) : val att C ≠ .orig := by
  unfold val; split_ifs <;> simp

lemma orig_ne_val (att : Finset (Fin n) → Bool) (C : Finset (Fin n)) : Rd.orig ≠ val att C :=
  fun h => val_ne_orig att C h.symm

lemma mem_cls {M : Finset (Finset (Fin n))} {att : Finset (Fin n) → Bool} {v : Rd n}
    {x : Fin n} : x ∈ cls M att v ↔ read M att x = v := by simp [cls]

lemma val_eq_iff (att : Finset (Fin n) → Bool) {C D : Finset (Fin n)} (hCD : C ≠ D) :
    val att C = val att D ↔ att C = true ∧ att D = true := by
  unfold val
  by_cases hC : att C <;> by_cases hD : att D <;> simp [hC, hD, hCD]

/-! ### (i) At most one innovation -/

/-- **Theorem 8.5(i).**  With no innovation, the only class is all witnesses (a trivial split,
no cluster); with one innovation on `C_e`, every proposal is `C_e` or its complement, in either
coding, so it is a split or cluster of the stemma. -/
theorem single (att : Finset (Fin n) → Bool) {e : Finset (Fin n)} (A : Finset (Fin n)) :
    (PropU ∅ att A → A = univ) ∧ (¬ PropR ∅ att A) ∧
    (PropU {e} att A → A = e ∨ A = eᶜ) ∧ (PropR {e} att A → A = e) := by
  have h0 : ∀ x, read (∅ : Finset (Finset (Fin n))) att x = .orig := fun x =>
    read_of_none (by simp)
  have h1 : ∀ x, read {e} att x = if x ∈ e then val att e else .orig := by
    intro x
    split_ifs with hx
    · exact read_of_lowest ⟨mem_singleton_self e, hx, fun D hD _ => (mem_singleton.mp hD) ▸ le_rfl⟩
    · exact read_of_none (by simpa using hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hA, v, rfl⟩
    obtain ⟨y, hy⟩ := hA
    have hv : v = .orig := by rw [mem_cls, h0] at hy; exact hy.symm
    ext x; simp [mem_cls, h0, hv]
  · rintro ⟨hA, v, hv, rfl⟩
    obtain ⟨y, hy⟩ := hA
    rw [mem_cls, h0] at hy
    exact hv hy.symm
  · rintro ⟨hA, v, rfl⟩
    obtain ⟨y, hy⟩ := hA
    simp only [cls, mem_filter, mem_univ, true_and, h1] at hy
    by_cases hye : y ∈ e
    · left
      rw [if_pos hye] at hy
      ext x; simp only [cls, mem_filter, mem_univ, true_and, h1, ← hy]
      by_cases hx : x ∈ e <;> simp [hx, orig_ne_val, val_ne_orig]
    · right
      rw [if_neg hye] at hy
      ext x; simp only [cls, mem_filter, mem_univ, true_and, h1, ← hy, mem_compl]
      by_cases hx : x ∈ e <;> simp [hx, orig_ne_val, val_ne_orig]
  · rintro ⟨hA, v, hv, rfl⟩
    obtain ⟨y, hy⟩ := hA
    simp only [cls, mem_filter, mem_univ, true_and, h1] at hy
    by_cases hye : y ∈ e
    · rw [if_pos hye] at hy
      ext x; simp only [cls, mem_filter, mem_univ, true_and, h1, ← hy]
      by_cases hx : x ∈ e <;> simp [hx, orig_ne_val, val_ne_orig]
    · rw [if_neg hye] at hy; exact absurd hy.symm hv

/-- The split `A | Aᶜ` is non-trivial: at least two witnesses on each side. -/
def SplitNT (A : Finset (Fin n)) : Prop := 2 ≤ A.card ∧ 2 ≤ Aᶜ.card

/-- The cluster `A` is non-trivial: at least two witnesses, and not all of them. -/
def ClusterNT (A : Finset (Fin n)) : Prop := 2 ≤ A.card ∧ A ≠ univ

lemma two_le_card_union {e f : Finset (Fin n)} (hd : Disjoint e f) (he : e.Nonempty)
    (hf : f.Nonempty) : 2 ≤ (e ∪ f).card := by
  rw [card_union_of_disjoint hd]
  have := he.card_pos; have := hf.card_pos; omega

/-! ### (ii) Two innovations on disjoint clades -/

section disjoint

variable (att : Finset (Fin n) → Bool) {e f : Finset (Fin n)} (hd : Disjoint e f)
include hd

lemma read_disj (x : Fin n) :
    read {e, f} att x = if x ∈ e then val att e else if x ∈ f then val att f else .orig := by
  split_ifs with hxe hxf
  · refine read_of_lowest ⟨by simp, hxe, fun D hD hxD => ?_⟩
    rcases mem_insert.mp hD with rfl | hD
    · exact le_rfl
    · rw [mem_singleton.mp hD] at hxD; exact absurd hxD (disjoint_left.mp hd hxe)
  · refine read_of_lowest ⟨by simp, hxf, fun D hD hxD => ?_⟩
    rcases mem_insert.mp hD with rfl | hD
    · exact absurd hxD hxe
    · rw [mem_singleton.mp hD]
  · exact read_of_none (by simp [hxe, hxf])

lemma cls_disj (v : Rd n) :
    cls {e, f} att v = (if val att e = v then e else ∅) ∪ (if val att f = v then f else ∅) ∪
      (if v = .orig then (e ∪ f)ᶜ else ∅) := by
  ext x
  rw [mem_cls, read_disj att hd]
  have hef : x ∈ e → x ∉ f := fun h => disjoint_left.mp hd h
  have h0e := val_ne_orig att e
  have h0f := val_ne_orig att f
  by_cases hxe : x ∈ e <;> by_cases hxf : x ∈ f <;> by_cases h1 : val att e = v <;>
    by_cases h2 : val att f = v <;> by_cases h3 : v = .orig <;>
    simp only [hxe, hxf, h1, h2, h3, if_true, if_false, mem_union, mem_compl, notMem_empty,
      or_false, false_or, true_or, or_true, not_true, not_false_eq_true, and_true, true_and] <;>
    simp_all [eq_comm (a := Rd.orig)]

/-- **Theorem 8.5(ii) (`thm:mechanisms`), retention and coincidence.**  With innovations on two
disjoint non-empty clades `C_e`, `C_f`: the unrooted coding proposes `(C_e ∪ C_f) | rest`
whatever the two readings (as soon as some witness lies outside both clades); the rooted coding
proposes the cluster `C_e ∪ C_f` iff both readings are attractive; and every other proposal is
`C_e`, `C_f` or the complement of one of them, a split or cluster of the stemma. -/
theorem retention_coincidence (he : e.Nonempty) (hf : f.Nonempty) :
    ((e ∪ f)ᶜ.Nonempty → PropU {e, f} att (e ∪ f)ᶜ) ∧
    (PropR {e, f} att (e ∪ f) ↔ att e = true ∧ att f = true) ∧
    (∀ A, PropU {e, f} att A → A = e ∨ A = f ∨ A = e ∪ f ∨ A = (e ∪ f)ᶜ) ∧
    (∀ A, PropR {e, f} att A → A = e ∨ A = f ∨ A = e ∪ f) := by
  have hef : e ≠ f := by
    rintro rfl; obtain ⟨x, hx⟩ := he; exact disjoint_left.mp hd hx hx
  have hcls := cls_disj att hd
  refine ⟨fun hne => ⟨hne, .orig, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hcls]; simp [val_ne_orig]
  · rintro ⟨-, v, hv, hA⟩
    obtain ⟨x, hx⟩ := he
    obtain ⟨y, hy⟩ := hf
    have hxv : read {e, f} att x = v := mem_cls.mp (hA ▸ mem_union_left _ hx)
    have hyv : read {e, f} att y = v := mem_cls.mp (hA ▸ mem_union_right _ hy)
    rw [read_disj att hd, if_pos hx] at hxv
    rw [read_disj att hd, if_neg (disjoint_right.mp hd hy), if_pos hy] at hyv
    exact (val_eq_iff att hef).mp (hxv.trans hyv.symm)
  · rintro ⟨h1, h2⟩
    have v1 : val att e = .attr := by simp [val, h1]
    have v2 : val att f = .attr := by simp [val, h2]
    refine ⟨he.mono subset_union_left, .attr, by simp, ?_⟩
    rw [hcls]; simp [v1, v2]
  · rintro A ⟨hA, v, rfl⟩
    rw [hcls] at hA ⊢
    by_cases h3 : v = .orig
    · subst h3
      simp only [val_ne_orig, if_false, if_true, empty_union]
      simp
    · simp only [h3, if_false, union_empty] at hA ⊢
      by_cases h1 : val att e = v <;> by_cases h2 : val att f = v <;>
        simp only [h1, h2, if_true, if_false, union_empty, empty_union] at hA ⊢
      · simp
      · simp
      · simp
      · exact absurd hA (by simp)
  · rintro A ⟨hA, v, hv, rfl⟩
    rw [hcls] at hA ⊢
    simp only [hv, if_false, union_empty] at hA ⊢
    by_cases h1 : val att e = v <;> by_cases h2 : val att f = v <;>
      simp only [h1, h2, if_true, if_false, union_empty, empty_union] at hA ⊢
    · simp
    · simp
    · simp
    · exact absurd hA (by simp)

/-- **Theorem 8.5(ii) as stated in the report** (proposals counted only when non-trivial).  The
unrooted coding proposes the non-trivial split `(C_e ∪ C_f) | rest` whatever the two readings,
provided the rest has at least two witnesses (`C_e ∪ C_f` has at least two, the clades being
disjoint and non-empty); the rooted coding proposes the non-trivial cluster `C_e ∪ C_f` iff both
readings are attractive and `C_e ∪ C_f ≠ X`.  The statement holds for every assignment `att` of
readings to edges, so in particular when the attraction choices are independent across edges. -/
theorem retention_coincidence_report (he : e.Nonempty) (hf : f.Nonempty) :
    (2 ≤ (e ∪ f)ᶜ.card → PropU {e, f} att (e ∪ f)ᶜ ∧ SplitNT (e ∪ f)ᶜ) ∧
    (PropR {e, f} att (e ∪ f) ∧ ClusterNT (e ∪ f) ↔
      att e = true ∧ att f = true ∧ e ∪ f ≠ univ) := by
  obtain ⟨hU, hR, -, -⟩ := retention_coincidence att hd he hf
  have h2 := two_le_card_union hd he hf
  refine ⟨fun hc => ⟨hU (card_pos.mp (by omega)), hc, by rw [compl_compl]; exact h2⟩, ?_⟩
  constructor
  · rintro ⟨hp, -, hne⟩
    obtain ⟨h1, h3⟩ := hR.mp hp
    exact ⟨h1, h3, hne⟩
  · rintro ⟨h1, h3, hne⟩
    exact ⟨hR.mpr ⟨h1, h3⟩, h2, hne⟩

end disjoint

/-! ### (iii) Two nested innovations -/

section nested

variable (att : Finset (Fin n) → Bool) {e f : Finset (Fin n)} (hfe : f ⊂ e)
include hfe

lemma read_nest (x : Fin n) :
    read {e, f} att x = if x ∈ f then val att f else if x ∈ e then val att e else .orig := by
  split_ifs with hxf hxe
  · refine read_of_lowest ⟨by simp, hxf, fun D hD _ => ?_⟩
    rcases mem_insert.mp hD with rfl | hD
    · exact hfe.1
    · rw [mem_singleton.mp hD]
  · refine read_of_lowest ⟨by simp, hxe, fun D hD hxD => ?_⟩
    rcases mem_insert.mp hD with rfl | hD
    · exact le_rfl
    · rw [mem_singleton.mp hD] at hxD; exact absurd hxD hxf
  · exact read_of_none (by
      intro C hC hxC
      rcases mem_insert.mp hC with rfl | hC
      · exact hxe hxC
      · rw [mem_singleton.mp hC] at hxC; exact hxf hxC)

lemma cls_nest (v : Rd n) :
    cls {e, f} att v = (if val att f = v then f else ∅) ∪ (if val att e = v then e \ f else ∅) ∪
      (if v = .orig then eᶜ else ∅) := by
  ext x
  rw [mem_cls, read_nest att hfe]
  have hfe' : x ∈ f → x ∈ e := fun h => hfe.1 h
  have h0e := val_ne_orig att e
  have h0f := val_ne_orig att f
  by_cases hxe : x ∈ e <;> by_cases hxf : x ∈ f <;> by_cases h1 : val att f = v <;>
    by_cases h2 : val att e = v <;> by_cases h3 : v = .orig <;>
    simp only [hxe, hxf, h1, h2, h3, if_true, if_false, mem_union, mem_compl, mem_sdiff,
      notMem_empty, or_false, false_or, true_or, or_true, not_true, not_false_eq_true, and_true,
      true_and] <;>
    simp_all [eq_comm (a := Rd.orig)]

/-- **Theorem 8.5(iii) (`thm:mechanisms`), overwrite.**  With innovations on nested clades
`C_f ⊊ C_e`, `C_f` non-empty: both codings propose `C_e \ C_f` unless both readings are
attractive; every other proposal is `C_f`, `C_e`, or the complement of `C_e`, a split or cluster
of the stemma. -/
theorem overwrite (hf : f.Nonempty) :
    (PropU {e, f} att (e \ f) ↔ ¬ (att e = true ∧ att f = true)) ∧
    (PropR {e, f} att (e \ f) ↔ ¬ (att e = true ∧ att f = true)) ∧
    (∀ A, PropU {e, f} att A → A = f ∨ A = e ∨ A = eᶜ ∨ A = e \ f) ∧
    (∀ A, PropR {e, f} att A → A = f ∨ A = e ∨ A = e \ f) := by
  have hef : e ≠ f := fun h => hfe.ne h.symm
  have hcls := cls_nest att hfe
  obtain ⟨z, hz⟩ : (e \ f).Nonempty := sdiff_nonempty.mpr (not_subset_of_ssubset hfe)
  -- `e \ f` is a class iff the two values differ
  have key : ∀ v, e \ f = cls {e, f} att v → v = val att e ∧ val att f ≠ v := by
    intro v hv
    have hzv : read {e, f} att z = v := mem_cls.mp (hv ▸ hz)
    rw [read_nest att hfe, if_neg (mem_sdiff.mp hz).2, if_pos (mem_sdiff.mp hz).1] at hzv
    refine ⟨hzv.symm, fun h => ?_⟩
    obtain ⟨y, hy⟩ := hf
    have : y ∈ cls {e, f} att v := by
      rw [mem_cls, read_nest att hfe, if_pos hy]; exact h
    rw [← hv] at this
    exact (mem_sdiff.mp this).2 hy
  have back : ¬ (att e = true ∧ att f = true) → e \ f = cls {e, f} att (val att e) := by
    intro h
    have hne : val att f ≠ val att e := fun h' => h ((val_eq_iff att hef).mp h'.symm)
    rw [hcls]; simp [hne, val_ne_orig]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨-, v, hv⟩ hboth
    obtain ⟨rfl, hne⟩ := key v hv
    exact hne ((val_eq_iff att hef).mpr hboth).symm
  · intro h; exact ⟨⟨z, hz⟩, val att e, back h⟩
  · rintro ⟨-, v, -, hv⟩ hboth
    obtain ⟨rfl, hne⟩ := key v hv
    exact hne ((val_eq_iff att hef).mpr hboth).symm
  · intro h; exact ⟨⟨z, hz⟩, val att e, val_ne_orig att e, back h⟩
  · rintro A ⟨hA, v, rfl⟩
    have hfe' : f ∪ e \ f = e := union_sdiff_of_subset hfe.1
    rw [hcls] at hA ⊢
    by_cases h3 : v = .orig
    · subst h3
      simp only [val_ne_orig, if_false, if_true, empty_union]
      simp
    · simp only [h3, if_false, union_empty] at hA ⊢
      by_cases h1 : val att f = v <;> by_cases h2 : val att e = v <;>
        simp only [h1, h2, if_true, if_false, union_empty, empty_union] at hA ⊢
      · simp [hfe']
      · simp
      · simp
      · exact absurd hA (by simp)
  · rintro A ⟨hA, v, hv, rfl⟩
    have hfe' : f ∪ e \ f = e := union_sdiff_of_subset hfe.1
    rw [hcls] at hA ⊢
    simp only [hv, if_false, union_empty] at hA ⊢
    by_cases h1 : val att f = v <;> by_cases h2 : val att e = v <;>
      simp only [h1, h2, if_true, if_false, union_empty, empty_union] at hA ⊢
    · simp [hfe']
    · simp
    · simp
    · exact absurd hA (by simp)

/-- **Theorem 8.5(iii) as stated in the report** (proposals counted only when non-trivial).  With
`C_f ⊊ C_e`, `C_f` non-empty and `C_e ≠ X` (the clade of an edge), and `|C_e \ C_f| ≥ 2`: both
codings propose `C_e \ C_f`, as a non-trivial split and as a non-trivial cluster, unless both
readings are attractive.  The statement holds for every assignment `att`, so in particular when the
attraction choices are independent across edges. -/
theorem overwrite_report (hf : f.Nonempty) (heU : e ≠ univ) (h2 : 2 ≤ (e \ f).card) :
    (PropU {e, f} att (e \ f) ∧ SplitNT (e \ f) ↔ ¬ (att e = true ∧ att f = true)) ∧
    (PropR {e, f} att (e \ f) ∧ ClusterNT (e \ f) ↔ ¬ (att e = true ∧ att f = true)) := by
  obtain ⟨hU, hR, -, -⟩ := overwrite att hfe hf
  obtain ⟨y, hy⟩ := hf
  obtain ⟨w, hw⟩ : eᶜ.Nonempty := by
    rw [compl_eq_univ_sdiff]
    exact sdiff_nonempty.mpr (fun h => heU (subset_antisymm (subset_univ e) h))
  have hsplit : SplitNT (e \ f) := by
    refine ⟨h2, ?_⟩
    have hwy : w ≠ y := by rintro rfl; exact (mem_compl.mp hw) (hfe.1 hy)
    have hsub : ({y, w} : Finset (Fin n)) ⊆ (e \ f)ᶜ := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · simp [hy]
      · rw [mem_singleton.mp hx]; simp [mem_compl.mp hw]
    have := card_le_card hsub
    rw [card_pair hwy.symm] at this
    exact this
  have hclus : ClusterNT (e \ f) := ⟨h2, fun h => by
    have : y ∈ e \ f := h ▸ mem_univ y
    exact (mem_sdiff.mp this).2 hy⟩
  exact ⟨⟨fun h => hU.mp h.1, fun h => ⟨hU.mpr h, hsplit⟩⟩,
    ⟨fun h => hR.mp h.1, fun h => ⟨hR.mpr h, hclus⟩⟩⟩

end nested

end Stemma.Mechanisms
