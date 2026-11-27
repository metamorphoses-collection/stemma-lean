/-
NP-completeness: Corollary 4.2 of the technical report (`cor:nphard`), completed.

`NPHard.lean` proves the compatible-splits problem NP-hard (unit weights, decision version).  This
file proves, with the classes of `cslib-community/cslib-frontier` (Apache-2.0, on `leanprover/cslib`):

* `CompatibleSplits_mem_NP`: the problem (well-formed instances with `m` pairwise compatible
  candidates; `NPHard.lean`) is in NP.  A certificate selects candidate splits (a mask over the
  candidate list); the check, polynomial-time by `fun_prop`, tests that the instance is well-formed
  (`wfS`: each candidate side a set of the witnesses, at least two witnesses on each side; read back
  by `wfS_iff`), that the number selected is `m` and that any two selected candidates give
  distinct, non-complementary, compatible splits (`okB`, read back as sets by `okB_iff`).  `compatibleSplits_eq` reads the problem on candidate
  lists rather than on the splits they give.
* `CompatibleSplits_npComplete`: it is NP-complete.
* `WeightedSplits`: the weighted problem, decision version of the maximum-weight compatible set
  problem: candidates carry weights in `ℕ`, and a yes-instance is well-formed (`WFW`) and has
  pairwise compatible candidates of total weight at least `k`.
* `WeightedSplits_mem_NP`, `toW_mem_iff` (unit weights are a special case, a polynomial-time
  reduction), `WeightedSplits_npHard`, `WeightedSplits_npComplete`.

The weight-preserving reduction from maximum-weight independent set itself, with arbitrary
weights, is `Reduction.lean`, in the operation-count model.
-/
import StemmaLean.NPHard
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

open Cslib.Complexity Turing.MultiTapeTM

namespace Stemma.NPHard

/-! ### Boolean tests on lists of witnesses -/

/-- `A ∩ B = ∅`. -/
def c1 (t : List ℕ × List ℕ × List ℕ) : Bool := t.2.1.all fun a => !t.2.2.contains a
/-- `A ∩ (U \ B) = ∅`. -/
def c2 (t : List ℕ × List ℕ × List ℕ) : Bool := t.2.1.all fun a => !t.1.contains a || t.2.2.contains a
/-- `(U \ A) ∩ B = ∅`. -/
def c3 (t : List ℕ × List ℕ × List ℕ) : Bool := t.2.2.all fun b => !t.1.contains b || t.2.1.contains b
/-- `(U \ A) ∩ (U \ B) = ∅`. -/
def c4 (t : List ℕ × List ℕ × List ℕ) : Bool := t.1.all fun u => t.2.1.contains u || t.2.2.contains u
/-- `A = U \ B`. -/
def cc (t : List ℕ × List ℕ × List ℕ) : Bool :=
  (t.2.1.all fun a => t.1.contains a && !t.2.2.contains a) &&
    t.1.all fun u => t.2.2.contains u || t.2.1.contains u
/-- `A = B` as sets. -/
def ce (t : List ℕ × List ℕ × List ℕ) : Bool :=
  (t.2.1.all fun a => t.2.2.contains a) && t.2.2.all fun b => t.2.1.contains b
/-- Two candidate splits may both be selected. -/
def okB (t : List ℕ × List ℕ × List ℕ) : Bool :=
  !ce t && !cc t && (c1 t || c2 t || c3 t || c4 t)

@[fun_prop] theorem c1_polyTime : ComputableInPolyTime c1
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold c1; fun_prop
@[fun_prop] theorem c2_polyTime : ComputableInPolyTime c2
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold c2; fun_prop
@[fun_prop] theorem c3_polyTime : ComputableInPolyTime c3
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold c3; fun_prop
@[fun_prop] theorem c4_polyTime : ComputableInPolyTime c4
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold c4; fun_prop
@[fun_prop] theorem cc_polyTime : ComputableInPolyTime cc
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold cc; fun_prop
@[fun_prop] theorem ce_polyTime : ComputableInPolyTime ce
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold ce; fun_prop
@[fun_prop] theorem okB_polyTime : ComputableInPolyTime okB
    (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) encBool := by
  unfold okB; fun_prop

/-- At least two distinct entries. -/
def twoB (l : List ℕ) : Bool := l.any fun b => !(l.all fun a => decide (a = b))

/-- The witnesses of `U` not in `l`. -/
def outside (t : List ℕ × List ℕ) : List ℕ := t.1.filter fun u => !t.2.contains u

/-- `l` is a well-formed candidate split of `U` (`WFsplit`). -/
def wfB (t : List ℕ × List ℕ) : Bool :=
  (t.2.all fun a => t.1.contains a) && twoB t.2 && twoB (outside t)

@[fun_prop] theorem twoB_polyTime : ComputableInPolyTime twoB (encList encNat) encBool := by
  unfold twoB; fun_prop
@[fun_prop] theorem outside_polyTime : ComputableInPolyTime outside
    (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  unfold outside; fun_prop
@[fun_prop] theorem wfB_polyTime : ComputableInPolyTime wfB
    (encPair (encList encNat) (encList encNat)) encBool := by
  unfold wfB; fun_prop

/-! ### What the tests decide -/

section Semantics
variable (t : List ℕ × List ℕ × List ℕ)

theorem c1_iff : c1 t = true ↔ t.2.1.toFinset ∩ t.2.2.toFinset = ∅ := by
  simp [c1, Finset.eq_empty_iff_forall_notMem]

theorem c2_iff : c2 t = true ↔ t.2.1.toFinset ∩ (t.1.toFinset \ t.2.2.toFinset) = ∅ := by
  simp only [c2, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, decide_eq_true_eq, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_inter, Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · intro h a ⟨ha, hu, hb⟩; rcases h a ha with h | h <;> contradiction
  · intro h a ha; by_cases hu : a ∈ t.1
    · exact Or.inr (by by_contra hb; exact h a ⟨ha, hu, hb⟩)
    · exact Or.inl hu

theorem c3_iff : c3 t = true ↔ (t.1.toFinset \ t.2.1.toFinset) ∩ t.2.2.toFinset = ∅ := by
  simp only [c3, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, decide_eq_true_eq, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_inter, Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · intro h b ⟨⟨hu, ha⟩, hb⟩; rcases h b hb with h | h <;> contradiction
  · intro h b hb; by_cases hu : b ∈ t.1
    · exact Or.inr (by by_contra ha; exact h b ⟨⟨hu, ha⟩, hb⟩)
    · exact Or.inl hu

theorem c4_iff : c4 t = true ↔ (t.1.toFinset \ t.2.1.toFinset) ∩ (t.1.toFinset \ t.2.2.toFinset) = ∅ := by
  simp only [c4, List.all_eq_true, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · rintro h u ⟨⟨hu, ha⟩, -, hb⟩; rcases h u hu with h | h <;> contradiction
  · intro h u hu; by_contra hc; push Not at hc; exact h u ⟨⟨hu, hc.1⟩, hu, hc.2⟩

theorem cc_iff : cc t = true ↔ t.2.1.toFinset = t.1.toFinset \ t.2.2.toFinset := by
  simp only [cc, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq, Finset.ext_iff,
    Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · rintro ⟨h1, h2⟩ a; constructor
    · intro ha; exact h1 a ha
    · rintro ⟨hu, hb⟩; rcases h2 a hu with h | h; · contradiction
      · exact h
  · intro h; refine ⟨fun a ha => (h a).1 ha, fun u hu => ?_⟩
    by_cases hb : u ∈ t.2.2
    · exact Or.inl hb
    · exact Or.inr ((h u).2 ⟨hu, hb⟩)

theorem ce_iff : ce t = true ↔ t.2.1.toFinset = t.2.2.toFinset := by
  simp only [ce, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    Finset.ext_iff, List.mem_toFinset]
  exact ⟨fun ⟨h1, h2⟩ a => ⟨h1 a, h2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

/-- The condition on two distinct selected candidates `A`, `B` (given by their lists). -/
def OK (U A B : List ℕ) : Prop :=
  A.toFinset ≠ B.toFinset ∧ A.toFinset ≠ U.toFinset \ B.toFinset ∧
    CompatU U.toFinset A.toFinset B.toFinset

theorem okB_iff : okB t = true ↔ OK t.1 t.2.1 t.2.2 := by
  simp only [okB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', OK, CompatU,
    ← c1_iff, ← c2_iff, ← c3_iff, ← c4_iff, ← cc_iff, ← ce_iff, ne_eq, Bool.not_eq_true]
  tauto

theorem twoB_iff (l : List ℕ) : twoB l = true ↔ 2 ≤ l.toFinset.card := by
  rw [show 2 ≤ l.toFinset.card ↔ 1 < l.toFinset.card from Iff.rfl, Finset.one_lt_card]
  simp only [twoB, List.any_eq_true, Bool.not_eq_true', List.all_eq_false, decide_eq_true_eq,
    List.mem_toFinset]
  constructor
  · rintro ⟨b, hb, a, ha, hab⟩; exact ⟨a, ha, b, hb, hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩; exact ⟨b, hb, a, ha, hab⟩

theorem wfB_iff (U l : List ℕ) : wfB (U, l) = true ↔ WFsplit U l := by
  have ho : (outside (U, l)).toFinset = U.toFinset \ l.toFinset := by
    ext w; simp [outside]
  simp only [wfB, Bool.and_eq_true, twoB_iff, ho, WFsplit, List.all_eq_true, List.contains_eq_mem,
    decide_eq_true_eq, Finset.subset_iff, List.mem_toFinset, and_assoc]

end Semantics

/-! ### Membership in NP -/

/-- A set of candidate lists that witnesses a yes-instance. -/
def Pairs (x : SplitInstance) (T : Finset (List ℕ)) : Prop :=
  T.card = x.m ∧ ∀ l ∈ T, ∀ l' ∈ T, l ≠ l' → OK x.univ l l'

/-- `HasCompatible`, read on candidate lists rather than on the splits they give. -/
theorem hasCompatible_iff (x : SplitInstance) : HasCompatible x ↔
    ∃ T : Finset (List ℕ), (∀ l ∈ T, l ∈ x.splits) ∧ Pairs x T := by
  simp only [HasCompatible, Pairs, OK]
  constructor
  · rintro ⟨S, hSm, hSs, hSc⟩
    choose f hf hft using hSs
    refine ⟨S.attach.image fun A => f A.1 A.2, ?_, ?_, ?_⟩
    · intro l hl
      obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hl
      exact hf _ _
    · rw [Finset.card_image_of_injective, Finset.card_attach, hSm]
      intro A B h
      apply Subtype.ext
      rw [← hft A.1 A.2, ← hft B.1 B.2]
      exact congrArg List.toFinset h
    · intro l hl l' hl' hne
      obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hl'
      have hAB : A.1 ≠ B.1 := fun h => hne (by
        have : A = B := Subtype.ext h
        rw [this])
      rw [hft, hft]
      exact ⟨hAB, hSc _ A.2 _ B.2 hAB⟩
  · rintro ⟨T, hTs, hTm, hTc⟩
    have hinj : Set.InjOn List.toFinset (T : Set (List ℕ)) := by
      intro l hl l' hl' h
      by_contra hne
      exact (hTc l hl l' hl' hne).1 h
    refine ⟨T.image List.toFinset, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, hTm]
    · intro A hA
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hA
      exact ⟨l, hTs l hl, rfl⟩
    · intro A hA B hB hAB
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hB
      have hne : l ≠ l' := fun h => hAB (h ▸ rfl)
      exact (hTc l hl l' hl' hne).2

/-- The compatible-splits problem, read on candidate lists rather than on the splits they give. -/
theorem compatibleSplits_eq : CompatibleSplits =
    {x | ∃ T : Finset (List ℕ), (∀ l ∈ T, l ∈ x.splits) ∧ (WF x ∧ Pairs x T)} := by
  ext x
  change WF x ∧ HasCompatible x ↔ _
  rw [hasCompatible_iff]
  constructor
  · rintro ⟨h, T, h1, h2⟩; exact ⟨T, h1, h, h2⟩
  · rintro ⟨T, h1, h, h2⟩; exact ⟨h, T, h1, h2⟩

/-- The well-formedness check of an instance. -/
def wfS (x : SplitInstance) : Bool := x.splits.all fun l => wfB (x.univ, l)

@[fun_prop] theorem wfS_polyTime : ComputableInPolyTime wfS encSplitInstance encBool :=
  ComputableInPolyTime.allWithInput
    (test := fun (x : SplitInstance) (l : List ℕ) => wfB (x.univ, l))
    (list := SplitInstance.splits) (by fun_prop) (by fun_prop)

theorem wfS_iff (x : SplitInstance) : wfS x = true ↔ WF x := by
  simp only [wfS, List.all_eq_true, wfB_iff, WF]

/-- The test of one selected candidate `l` against all selected candidates. -/
def rowU (q : (SplitInstance × List (List ℕ)) × List ℕ) : Bool :=
  q.1.2.all fun l' => decide (q.2 = l') || okB (q.1.1.univ, q.2, l')

/-- The check of a selected list of candidates, well-formedness aside. -/
def checkP (p : SplitInstance × List (List ℕ)) : Bool :=
  decide (p.2.length = p.1.m) && p.2.all fun l => rowU (p, l)

/-- The check of a selected list of candidates: the instance is well-formed, and `checkP`. -/
def checkU (p : SplitInstance × List (List ℕ)) : Bool := wfS p.1 && checkP p

theorem eqList_polyTime : ComputableInPolyTime (fun q : List ℕ × List ℕ => decide (q.1 = q.2))
    (encPair (encList encNat) (encList encNat)) encBool := by
  fun_prop

@[fun_prop] theorem rowU_polyTime : ComputableInPolyTime rowU
    (encPair (encWithEntries encSplitInstance (encList encNat)) (encList encNat)) encBool := by
  unfold rowU; fun_prop

@[fun_prop] theorem checkP_polyTime : ComputableInPolyTime checkP
    (encWithEntries encSplitInstance (encList encNat)) encBool := by
  have h1 : ComputableInPolyTime (fun p : SplitInstance × List (List ℕ) => decide (p.2.length = p.1.m))
      (encWithEntries encSplitInstance (encList encNat)) encBool :=
    ((ComputableInPolyTime.length_list_binary (encList encNat)).comp
      (ComputableInPolyTime.snd _ _)).decide_eq' (by fun_prop)
  have h2 : ComputableInPolyTime (fun p : SplitInstance × List (List ℕ) => p.2.all fun l => rowU (p, l))
      (encWithEntries encSplitInstance (encList encNat)) encBool :=
    ComputableInPolyTime.allWithInput (test := fun p l => rowU (p, l))
      (ComputableInPolyTime.snd _ _) rowU_polyTime
  exact ComputableInPolyTime.bool_and' h1 h2

@[fun_prop] theorem checkU_polyTime : ComputableInPolyTime checkU
    (encWithEntries encSplitInstance (encList encNat)) encBool :=
  ComputableInPolyTime.bool_and' (wfS_polyTime.comp (ComputableInPolyTime.fst _ _))
    checkP_polyTime

theorem checkP_iff (x : SplitInstance) (ls : List (List ℕ)) (hnd : ls.Nodup) :
    checkP (x, ls) = true ↔ Pairs x ls.toFinset := by
  simp only [checkP, rowU, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    okB_iff, Pairs, List.mem_toFinset, List.toFinset_card_of_nodup hnd]
  refine and_congr Iff.rfl ⟨fun h l hl l' hl' hne => ?_, fun h l hl l' hl' => ?_⟩
  · rcases h l hl l' hl' with h | h
    · exact absurd h hne
    · exact h
  · by_cases hne : l = l'
    · exact Or.inl hne
    · exact Or.inr (h l hl l' hl' hne)

theorem checkU_iff (x : SplitInstance) (ls : List (List ℕ)) (hnd : ls.Nodup) :
    checkU (x, ls) = true ↔ WF x ∧ Pairs x ls.toFinset := by
  rw [checkU, Bool.and_eq_true, wfS_iff, checkP_iff x ls hnd]

/-- **The compatible-splits problem is in NP**: a certificate selects candidate splits, and the
check (the instance well-formed; the number selected, pairwise distinct, not complementary,
compatible) is polynomial-time. -/
theorem CompatibleSplits_mem_NP : CompatibleSplits ∈ NP encSplitInstance := by
  rw [compatibleSplits_eq]
  exact mem_NP_of_subsetWitness (encγ := encList encNat) (vs := SplitInstance.splits)
    (by fun_prop) checkU_polyTime fun x ls hnd _ => checkU_iff x ls hnd

/-- **Corollary 4.2, completeness.**  The compatible-splits problem is NP-complete. -/
theorem CompatibleSplits_npComplete : NPComplete encSplitInstance CompatibleSplits :=
  ⟨CompatibleSplits_mem_NP, CompatibleSplits_npHard⟩

/-! ### The weighted problem -/

/-- An instance of the weighted compatible-splits problem: witnesses, weighted candidate splits
(each by one side, with a weight in `ℕ`) and a target weight. -/
@[ext]
structure WSplitInstance where
  univ : List ℕ
  cands : List (List ℕ × ℕ)
  k : ℕ
  deriving DecidableEq

enc_structure encWSplitInstance : WSplitInstance where
  univ : (encList encNat),
  cands : (encList (encPair (encList encNat) encNat)),
  k : encNat

attribute [fun_prop] encWSplitInstance_univ_polyTime encWSplitInstance_cands_polyTime
  encWSplitInstance_k_polyTime encWSplitInstance_mk_polyTime

/-- A well-formed weighted instance: every candidate is a well-formed split of the witnesses. -/
def WFW (x : WSplitInstance) : Prop := ∀ c ∈ x.cands, WFsplit x.univ c.1

/-- **Weighted compatible splits**: the well-formed instances (`WFW`: every candidate side is a set
of the listed witnesses, with at least two witnesses on each side) with a set of candidates,
pairwise giving distinct, non-complementary, compatible splits, of total weight at least `k`.  This
is the decision version of the maximum-weight compatible set problem of the report, with weights in
`ℕ`.  Malformed instances are no-instances. -/
def WeightedSplits : Set WSplitInstance :=
  {x | WFW x ∧ ∃ T : Finset (List ℕ × ℕ), (∀ c ∈ T, c ∈ x.cands) ∧
    (x.k ≤ ∑ c ∈ T, c.2 ∧ ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → OK x.univ c.1 c'.1)}

theorem weightedSplits_eq : WeightedSplits =
    {x | ∃ T : Finset (List ℕ × ℕ), (∀ c ∈ T, c ∈ x.cands) ∧
      (WFW x ∧ x.k ≤ ∑ c ∈ T, c.2 ∧ ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → OK x.univ c.1 c'.1)} := by
  ext x
  constructor
  · rintro ⟨h, T, h1, h2⟩; exact ⟨T, h1, h, h2⟩
  · rintro ⟨T, h1, h, h2⟩; exact ⟨h, T, h1, h2⟩

/-- The well-formedness check of a weighted instance. -/
def wfW (x : WSplitInstance) : Bool := x.cands.all fun c => wfB (x.univ, c.1)

@[fun_prop] theorem wfW_polyTime : ComputableInPolyTime wfW encWSplitInstance encBool :=
  ComputableInPolyTime.allWithInput
    (test := fun (x : WSplitInstance) (c : List ℕ × ℕ) => wfB (x.univ, c.1))
    (list := WSplitInstance.cands) (by fun_prop) (by fun_prop)

theorem wfW_iff (x : WSplitInstance) : wfW x = true ↔ WFW x := by
  simp only [wfW, List.all_eq_true, wfB_iff, WFW]

/-- The test of one selected weighted candidate against all selected candidates. -/
def rowW (q : (WSplitInstance × List (List ℕ × ℕ)) × (List ℕ × ℕ)) : Bool :=
  q.1.2.all fun c' => decide (q.2 = c') || okB (q.1.1.univ, q.2.1, c'.1)

/-- The total weight of a selected list of candidates. -/
def totalW (p : WSplitInstance × List (List ℕ × ℕ)) : ℕ := (p.2.map Prod.snd).sum

/-- The check of a selected list of weighted candidates, well-formedness aside. -/
def checkW0 (p : WSplitInstance × List (List ℕ × ℕ)) : Bool :=
  decide (p.1.k ≤ totalW p) && p.2.all fun c => rowW (p, c)

@[fun_prop] theorem rowW_polyTime : ComputableInPolyTime rowW
    (encPair (encWithEntries encWSplitInstance (encPair (encList encNat) encNat))
      (encPair (encList encNat) encNat)) encBool := by
  unfold rowW; fun_prop

@[fun_prop] theorem totalW_polyTime : ComputableInPolyTime totalW
    (encWithEntries encWSplitInstance (encPair (encList encNat) encNat)) encNat := by
  unfold totalW; fun_prop

@[fun_prop] theorem checkW0_polyTime : ComputableInPolyTime checkW0
    (encWithEntries encWSplitInstance (encPair (encList encNat) encNat)) encBool := by
  unfold checkW0
  have h1 : ComputableInPolyTime
      (fun p : WSplitInstance × List (List ℕ × ℕ) => decide (p.1.k ≤ totalW p))
      (encWithEntries encWSplitInstance (encPair (encList encNat) encNat)) encBool :=
    ComputableInPolyTime.binary_le' (by fun_prop) totalW_polyTime
  have h2 : ComputableInPolyTime
      (fun p : WSplitInstance × List (List ℕ × ℕ) => p.2.all fun c => rowW (p, c))
      (encWithEntries encWSplitInstance (encPair (encList encNat) encNat)) encBool :=
    ComputableInPolyTime.allWithInput (test := fun p c => rowW (p, c))
      (ComputableInPolyTime.snd _ _) rowW_polyTime
  exact ComputableInPolyTime.bool_and' h1 h2

theorem checkW0_iff (x : WSplitInstance) (ls : List (List ℕ × ℕ)) (hnd : ls.Nodup) :
    checkW0 (x, ls) = true ↔
      (x.k ≤ ∑ c ∈ ls.toFinset, c.2 ∧ ∀ c ∈ ls.toFinset, ∀ c' ∈ ls.toFinset, c ≠ c' →
        OK x.univ c.1 c'.1) := by
  have hs : totalW (x, ls) = ∑ c ∈ ls.toFinset, c.2 := by
    rw [totalW, List.sum_toFinset _ hnd]
  rw [checkW0, Bool.and_eq_true, decide_eq_true_eq, hs]
  simp only [rowW, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, okB_iff,
    List.mem_toFinset]
  refine and_congr Iff.rfl ⟨fun h c hc c' hc' hne => ?_, fun h c hc c' hc' => ?_⟩
  · rcases h c hc c' hc' with h | h
    · exact absurd h hne
    · exact h
  · by_cases hne : c = c'
    · exact Or.inl hne
    · exact Or.inr (h c hc c' hc' hne)

/-- The check of a selected list of weighted candidates: the instance is well-formed, and
`checkW0`. -/
def checkW (p : WSplitInstance × List (List ℕ × ℕ)) : Bool := wfW p.1 && checkW0 p

@[fun_prop] theorem checkW_polyTime : ComputableInPolyTime checkW
    (encWithEntries encWSplitInstance (encPair (encList encNat) encNat)) encBool :=
  ComputableInPolyTime.bool_and' (wfW_polyTime.comp (ComputableInPolyTime.fst _ _))
    checkW0_polyTime

theorem checkW_iff (x : WSplitInstance) (ls : List (List ℕ × ℕ)) (hnd : ls.Nodup) :
    checkW (x, ls) = true ↔
      (WFW x ∧ x.k ≤ ∑ c ∈ ls.toFinset, c.2 ∧ ∀ c ∈ ls.toFinset, ∀ c' ∈ ls.toFinset, c ≠ c' →
        OK x.univ c.1 c'.1) := by
  rw [checkW, Bool.and_eq_true, wfW_iff, checkW0_iff x ls hnd]

/-- **The weighted problem is in NP.** -/
theorem WeightedSplits_mem_NP : WeightedSplits ∈ NP encWSplitInstance := by
  rw [weightedSplits_eq]
  exact mem_NP_of_subsetWitness (encγ := encPair (encList encNat) encNat) (vs := WSplitInstance.cands)
    (by fun_prop) checkW_polyTime fun x ls hnd _ => checkW_iff x ls hnd

/-- Unit weights: every candidate gets weight `1`, and the target weight is `m`. -/
def toW (x : SplitInstance) : WSplitInstance :=
  ⟨x.univ, x.splits.map fun l => (l, 1), x.m⟩

@[fun_prop] theorem toW_polyTime : ComputableInPolyTime toW encSplitInstance encWSplitInstance := by
  unfold toW; fun_prop

/-- **Unit weights are a special case.**  An instance of the compatible-splits problem is a
yes-instance iff its unit-weight instance is. -/
theorem toW_mem_iff (x : SplitInstance) : x ∈ CompatibleSplits ↔ toW x ∈ WeightedSplits := by
  change WF x ∧ HasCompatible x ↔ WFW (toW x) ∧ _
  have hwf : WF x ↔ WFW (toW x) := by
    simp only [WF, WFW, toW, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr hwf ?_
  rw [hasCompatible_iff]
  simp only [toW, Pairs, List.mem_map]
  constructor
  · rintro ⟨T, hTs, hTm, hTc⟩
    refine ⟨T.image fun l => (l, 1), ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨l, hTs l hl, rfl⟩
    · rw [Finset.sum_image (fun l _ l' _ h => (Prod.ext_iff.mp h).1)]
      simp [hTm]
    · intro c hc c' hc' hne
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hc'
      exact hTc l hl l' hl' fun h => hne (h ▸ rfl)
  · rintro ⟨T, hTs, hTk, hTc⟩
    have hone : ∀ c ∈ T, c.2 = 1 := by
      intro c hc
      obtain ⟨l, -, rfl⟩ := hTs c hc
      rfl
    have hcard : x.m ≤ T.card := by
      rw [Finset.sum_congr rfl hone] at hTk
      simpa using hTk
    obtain ⟨T', hT'T, hT'm⟩ := Finset.exists_subset_card_eq hcard
    have hinj : Set.InjOn Prod.fst (T' : Set (List ℕ × ℕ)) := by
      intro c hc c' hc' h
      exact Prod.ext h ((hone c (hT'T hc)).trans (hone c' (hT'T hc')).symm)
    refine ⟨T'.image Prod.fst, ?_, ?_, ?_⟩
    · intro l hl
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨l', hl', rfl⟩ := hTs c (hT'T hc)
      exact hl'
    · rw [Finset.card_image_of_injOn hinj, hT'm]
    · intro l hl l' hl' hne
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hl'
      exact hTc c (hT'T hc) c' (hT'T hc') fun h => hne (h ▸ rfl)

/-- The compatible-splits problem reduces in polynomial time to its weighted version. -/
theorem polyTimeReducible_CompatibleSplits_WeightedSplits :
    PolyTimeReducible encSplitInstance encWSplitInstance CompatibleSplits WeightedSplits :=
  ⟨toW, toW_polyTime, toW_mem_iff⟩

/-- **Corollary 4.2, weighted.**  The maximum-weight compatible set problem (decision version) is
NP-hard. -/
theorem WeightedSplits_npHard : NPHard encWSplitInstance WeightedSplits :=
  CompatibleSplits_npHard.trans polyTimeReducible_CompatibleSplits_WeightedSplits

/-- **Corollary 4.2, weighted.**  The maximum-weight compatible set problem (decision version) is
NP-complete. -/
theorem WeightedSplits_npComplete : NPComplete encWSplitInstance WeightedSplits :=
  ⟨WeightedSplits_mem_NP, WeightedSplits_npHard⟩

end Stemma.NPHard
