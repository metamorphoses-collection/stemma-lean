# stemma-lean: best-supported stemmata, in Lean 4

[![CI](https://github.com/metamorphoses-collection/stemma-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/metamorphoses-collection/stemma-lean/actions/workflows/lean_action_ci.yml)

`stemma-lean` is a Lean 4 + Mathlib formalisation of the results on best-supported stemmata. A
best-supported stemma reconstructs a text's copying history as a maximum-weight set of compatible
families of witnesses. The library covers:

- the combinatorics of splits and stemmata: the counting facts, Buneman's theorem, the resolution of
  polytomies, universality of conflict graphs, the crossing set, the five-witness graph and the
  dynamic programme over subsets;
- fragmentary witnesses: partial splits, the triple obstruction, exact selection by cutting planes;
- deterministic certificates: displacement matching, local and global separation, thresholds, the
  rooted analogue;
- consistency and sample size: Chernoff, Hoeffding and Bernstein bounds, the margin, dependent
  blocks, confidence bounds for the margin, illegible witnesses, the cutting-plane estimator with
  and without illegibility;
- non-binary stemmata and coincident error: the Bédier effect and threshold, the rival test, the
  mechanisms of false support, the comparison of the codings, the irreversible model's support
  bounds, the quartet coding theorem, the largest-gap threshold and drift towards the root.

It accompanies the technical report of Metamorphoses of Civilization (2026), *Testing stemmata
against the evidence: Exact optimisation, evidence maps and Bédier's question (Technical report)*
(https://doi.org/10.5281/zenodo.24405385), and the two papers built on it. Each theorem's docstring
quotes the report's result number and says where the Lean statement differs from the report's.
Archived releases (all versions): https://doi.org/10.5281/zenodo.24405389.

Every declaration depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); there is no `sorry`.

## Building

Lean `v4.36.0` and Mathlib `v4.36.0`:

```
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

## Blueprint

The blueprint, https://metamorphoses-collection.github.io/stemma-lean/, sets out the report's
definitions and its 41 numbered results, with their statements and proofs. Each one links to its
Lean declarations, and a dependency graph shows which results each proof uses. It is built with
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) from [`blueprint/`](blueprint).
`blueprint/src/content.tex` is generated from the report's LaTeX source by
`blueprint/gen_content.py`, so it is never edited by hand. To build it locally, with graphviz and
`pip install leanblueprint`:

```
leanblueprint web                 # blueprint/web/index.html, dep_graph_document.html
python3 blueprint/link_decls.py   # Lean links point to the source on GitHub
leanblueprint pdf                 # blueprint/print/print.pdf (xelatex)
lake build && leanblueprint checkdecls
```

`checkdecls` checks that every Lean name in the blueprint exists. It is the only reason
`lakefile.toml` requires `checkdecls`. The workflow `.github/workflows/blueprint.yml` builds the
blueprint and publishes it on GitHub Pages on every push to `master`.

## Contents

Results in the order of the technical report. Files are in [`StemmaLean/`](StemmaLean).

| Report | Result | Lean |
| --- | --- | --- |
| Prop. 3.2 | Buneman's theorem: a set of non-trivial splits is pairwise compatible iff, with the trivial splits, it is the split system of an X-tree; the tree is unique up to label-preserving isomorphism | `Buneman` (`buneman`, `nontrivial_splits_of_tree`, `buneman_unique`), on the vendored Splits Equivalence Theorem |
| Lemma 3.3 | At most n−3 compatible non-trivial splits (by induction on laminar families); a set of n−3 is maximal; a binary tree has exactly n−3 non-trivial splits, and every system of n−3 splits is the split system of a binary tree | `Splits` (`card_le`, `maximal`), `BinaryTree` (`binary_tree_splits`, `isBinaryTree_of_fam`, `isBinary_iff_binary_tree`) |
| — | Every compatible split set lies in one of exactly n−3 (resolution of polytomies, without trees) | `Resolve` (`laminar_extend`, `resolvable`) |
| Lemma 3.5 | Exclusivity: one unit never proposes conflicting splits; the classes of two distinct readings of one unit give compatible splits | `Basic` (`exclusivity`, `exclusivity_fibres`) |
| Thm 4.1, Cor. 4.2 | Universality: every finite simple graph is a split-conflict graph on 4\|E\|+2\|V\|+2 witnesses; the reduction from MWIS preserves weights, has 4\|E\|+2\|V\|+2 witnesses and \|V\| candidates, costs O((\|V\|+\|E\|)²), and turns a polynomial-cost solver into one for MWIS on all graphs (costs in an abstract operation-count interface: `encodeCost`, `decodeCost` are stipulated, one unit per membership test); a class containing every split-conflict graph contains every graph | `Universal` (`universality`), `Reduction` (`reduction_mwis`, `decode_optimal`, `instance_size`, `encode_cost_le`, `transfer`, `transfer_poly`, `class_contains_all`); NP-completeness with Turing-machine polynomial time, unit weights and weighted: `NPHard` (`toSplits_polyTime`, `toSplits_wf`, `toSplits_mem_iff`, `CompatibleSplits_npHard`, `malformed_not_mem`), `NPComplete` (`CompatibleSplits_mem_NP`, `CompatibleSplits_npComplete`, `toW_mem_iff`, `WeightedSplits_mem_NP`, `WeightedSplits_npHard`, `WeightedSplits_npComplete`) |
| Prop. 5.2 | Pairs of partial splits are exact, triples are not; five witnesses are needed | `PartialSplits` (`pair_exact`, `triple_not_joint`, `four_nontrivial_full`) |
| Thm 5.3 | Cutting planes: relaxation, correctness of the first completable optimum, termination within 2^\|C\| rounds | `CuttingPlanes` (`relaxation`, `cutting_correct`, `cutting_terminates`) |
| Lemma 6.1 | Displacement matching, by Hall's theorem | `Splits` (`displacement_matching`) |
| Thms 6.2, 6.3 | Local and global separation | `Splits` (`local_separation`, `global_separation`) |
| Prop. 6.9 | Threshold for non-binary stemmata | `Splits` (`threshold`) |
| Prop. 6.10 | Rooted analogue: the counting facts, matching and separation for clusters; a cluster family is a binary rooted stemma iff, with an outgroup added, it is the split system of a binary tree | `Rooted` (`isBinR_iff_outgroup`), `BinaryTree` (`isBinR_iff_rooted_tree`) |
| Thm 7.1 | Pairwise Chernoff bound | `Chernoff` (`pairwise_bound`) |
| Lemma 7.3 | Computing the margin γ: T maximises the shifted supports iff g ≤ γ; γ ∈ [−1, 1] for supports in [0, 1]; after k bisection steps the bracket contains γ and has width 2·2^{−k} | `Margin` (`computing_gamma`, `margin_mem_Icc`, `bisect`, `bisect_spec`, `bisect_error`) |
| Thm 7.4(a) | Consistency, Hoeffding form 2\|R\|e^{−Lγ²/2} and Bernstein form Σ 2e^{−Lγ²/(8m_σ+4γ/3)}; Bernstein's inequality itself, which Mathlib lacks | `Consistency` (`consistency`), `Bernstein` (`bernstein_two`, `consistency_bernstein`) |
| Thm 7.4(b) | Inconsistency when another compatible set has larger expected support (strong law) | `Margin` (`inconsistency`) |
| Cor. 7.6 | Sample size | `Margin` (`sample_size`) |
| Prop. 7.8 | Dependent blocks | `Blocks` (`dependent_blocks`) |
| Thm 7.9 | Confidence bound for the margin, simultaneous over binary stemmata; the supports are binomial, and the one-sided Clopper–Pearson bounds have their coverage | `GammaConf` (`gamma_confidence`), `ClopperPearson` (`binomial_law`, `cpUpper_coverage`, `cpLower_coverage`, `gamma_confidence_cp`) |
| Prop. 7.11 (`prop:gammablocks`, current draft) | Certifying the margin with dependent units: J independent blocks of k units, bounds w(s)/L ∓ h with h = √(log(2N/δ)/(2J)); the conclusions of Thm 7.9 (Hoeffding on the block averages) | `GammaBlocks` (`gamma_confidence_avg`, `gamma_confidence_blocks`) |
| Thm 7.12 | Fragmentary witnesses: the bounds on restriction supports (b); with many units, each with its own illegibility, all of Theorem 7.4 for the completion estimator with m̃ (a: Hoeffding form for any R, Bernstein form, inconsistency) and its consistency for δ(4+2μ) < ρ (c) | `Fragmentary` (`restr_lower`, `restr_upper`, `fragmentary_margin_pos`), `FragmentaryUnits` (`fragmentary_consistency`, `fragmentary_consistency_bernstein`, `fragmentary_inconsistency`, `fragmentary_consistent`) |
| Thm 7.14(a), (b) | Cutting-plane estimator: completable iff displayed by a binary stemma; consistency from the strong law, almost surely and in probability; the closing remark of (b): a split can be displayed without being proposed, and with every m_σ > 0 and δ < 1 each split of T is eventually observed in full, almost surely | `Resolve` (`completable_iff_displayed'`), `Cutting` (`cutting_consistent`, `cutting_inconsistent`), `CuttingRemark` (`displayed_without_proposal`, `observed_in_full`, `all_observed_in_full`) |
| Thm 7.14(c) | Illegible witnesses: M(T) − M(T′) ≥ m(T) − m(Σ(T′)) − δ(2(n−1)μ + 2μ₂); T the unique maximum of M, and the estimator consistent, when δ(2(n−1)μ + 2μ₂) < γ | `CuttingIllegible` (`M_lower`, `M_upper`, `cutting_illegible`, `cutting_illegible_margin`, `cutting_illegible_consistent`) |
| Prop. 7.13 (`prop:textillegible`, current draft) | Illegibility that depends on the text: given the unit's complete proposals each witness is illegible with probability at most δ, otherwise arbitrary; m̃_σ ≥ (1−4δ)m_σ, m̃_τ ≤ m_τ + 2δμ, consistency of the completion estimator for δ(4+2μ) < ρ, and the inequality, margin and consistency of Thm 7.14(c) unchanged; the independent model is a special case | `TextIllegible` (`condIllegible_of_indep`, `restr_lower`, `restr_upper`, `margin_pos`, `consistent`, `M_lower`, `M_upper`, `cutting_illegible`, `cutting_illegible_margin`, `cutting_illegible_consistent`) |
| Prop. 7.15 (`prop:dimfree`, current draft) | A tolerance independent of the number of witnesses: for binary T′ and a non-trivial split σ ∉ Σ(T′), σ = A₁ ⊔ A₂, σᶜ = B₁ ⊔ B₂ (the quadrants of σ and a split of T′ that it crosses) and display of σ\|_O requires one part wholly illegible; the display probability is at most 2 max(δ, 2δ²) m_σ (4δ m_σ under Prop. 7.13); M(T) − M(T′) ≥ m(T) − m(Σ(T′)) − δ(6μ + 2μ₂) for δ ≤ 1/2 (− δ(8μ + 2μ₂) under Prop. 7.13); T the unique maximum of M, and the estimator consistent, when δ(6μ + 2μ₂) < γ (δ(8μ + 2μ₂) < γ) | `CuttingDimFree` (`four_parts`, `display_prob_le`, `display_prob_le_half`, `M_upper_dimfree`, `cutting_dimfree`, `cutting_dimfree_margin`, `cutting_dimfree_consistent`, `display_prob_le_text`, `M_upper_text`, `cutting_text`, `cutting_text_margin`, `cutting_text_consistent`) |
| Prop. 8.1 | Bédier effect: Pr(T optimal) ≤ (1−m_τ)^L; a polytomy gives a false split, not in T, compatible with every split of T, and of positive expected support in the attraction model | `Polytomy` (`bedier_effect`, `polytomy_split`), `Attraction` (`polytomy_support_pos`; `polytomy_support_pos_nt` with two witnesses outside, the split and the cluster non-trivial, rates positive on the two branches only), from `Basic` (`bedier_core`) and `Consistency` (`bedier_probability`) |
| Thm 8.2 | Bédier threshold, Kullback–Leibler and simplified forms; the KL form with the terms of true splits of rate 1 omitted, as in the report | `Chernoff` (`bedier_threshold`, `bedier_threshold_kl`, `bedier_threshold_simple`) |
| Prop. 8.3 (`prop:gap`, current draft) | Largest-gap threshold: if every observed w/L is within η = (G − g₂)/4 of its expectation, the observed values with 0 have a largest gap and the midpoint of every largest gap separates T from F (deterministic step, via the chain of expected values with gaps ≤ g₂); Pr(the cut does not separate) ≤ 2(\|T\| + \|F\|)e^{−L(G−g₂)²/8} (Hoeffding and a union bound) | `GapThreshold` (`gap_separation`, `gap_threshold`, `chain`) |
| Prop. 8.3 | Rival test: the conditional binomial law; the tail Pr(w(σ) ≥ k \| N), the test's p-value, and its value 2^{−N} Σ_{i≥k} C(N, i) under m_σ = m_τ | `Rival` (`rival`, `rival_null`, `rival_binomial`, `rival_tail`, `rival_tail_null`) |
| Thm 8.5 | Mechanisms of false support: what one unit proposes with one innovation, two on disjoint clades (retention, coincidence) and two nested (overwrite), in both codings; Λ_τ ≤ m_τ ≤ Λ_τ + Pr(\|M\| ≥ 3) ≤ Λ_τ + (Σπ)³/6, with Λ_τ in closed form and ω = 1, α², 1 − α² | `Mechanisms` (`single`, `retention_coincidence`, `overwrite`; with the report's size conditions `retention_coincidence_report`, `overwrite_report`), `Attraction` (`ex_split`, `P3_le`, `lambda_eq`, `omega_retention`, `omega_coincidence`, `omega_overwrite_rooted`, `omega_overwrite_unrooted`) |
| Cor. 8.7 (`cor:dominance`, current draft) | Comparison of the codings at second order: Λ of each cluster C, D in the rooted coding ≤ Λ of C\|D in the unrooted coding, and the same at every order; the pair weights ω: α² against 1 for disjoint pairs, 1−α² in both for nested pairs, 1 against 0 for a pair whose union is the other side, no single-edge term for a split not of the tree | `Dominance` (`dominance`, `dominance_exact`, `omega_dominance`, `omega_other_side`, `single_none`) |
| Prop. 8.9 (`prop:modelbounds`, current draft) | Irreversible model, support bounds: m_{σ_e} ≥ π_e ∏_{C_f ⊄ C_e}(1−π_f) for C_e non-trivial (the event computed exactly); the false mass, over any set of non-complementary false splits and over all false sides away from r, ≤ Σ_{C_e∩C_f=∅} π_eπ_f | `Irreversible` (`suppI_edge_ge`, `false_mass_le`, `false_mass_sides`) |
| Cor. 8.10 (`cor:modelglobal`, current draft) | A sufficient condition: binary T, min_e π_e ∏_f(1−π_f) ≥ c > Σ_{disjoint} π_eπ_f gives global separation, T the unique solution, the margin inequality with γ = c − D > 0, and consistency 2\|R\|e^{−L(c−D)²/2} | `Irreversible` (`model_global`, `model_consistency`) |
| Thm 8.6 | Coding theorem: exact supports, both leading-order boundaries, and, with the units, consistency or the false split (unrooted) and consistency or inconsistency (rooted); the companion quartet of the mathematical paper (Cor. 4.5), the long-branch boundary and, with the units, consistency or the false split in the two strict cases (the tie is left to the text) | `Quartet` (`long_branch`), `CodingGen`, `Coding`, `CodingLimit` (`unrooted_consistency`, `unrooted_false_selected`, `rooted_consistency`, `rooted_inconsistency`, `long_branch_consistent`, `long_branch_inconsistent`) |
| Prop. 8.14 (`prop:drift`, current draft) | Drift towards the root on (((1,3),2),4): exact supports as polynomials (81 outcomes), leading orders ρε², ((1−α²)σ+τ)bε², (1−α²)σbε², σε, α²τbε²; for every small fixed ε, unrooted: consistent if ((1−α²)σ+τ)b < ρ, 12\|34 selected if >; rooted: consistent if (1−α²)σb < ρ, the family {12, 123} selected if > | `DriftGen` (`closedD_*`, `scaleD_*`, `zeroD_*`), `Drift` (`drift_unrooted_consistency`, `drift_unrooted_false`, `drift_rooted_consistency`, `drift_rooted_false`) |
| Prop. 8.7 | Estimating α: C⁽²⁾ = α²R⁽²⁾ for an isolated pair, \|C − α²R\| ≤ Pr(\|M\| ≥ 3), the pooled bias bound, almost sure convergence of the observed ratio, and its invariance to units proposing nothing | `Alpha` (`two_part`, `alpha_pair`, `alpha_pooled`, `ratio_tendsto`, `ratio_drop_empty`) |
| Prop. 8.8 | Coincidence null at a polytomy: the outcomes that propose τ, the exact two-innovation part, \|m_τ − (α²q_iq_j + [k=3, v not the root](1−α²)q_vq_l)\| ≤ 7s³, and with random rates the factor κ, remainder ≤ 7 Eρ³ s³ | `PolytomyNull` (`pair_cases`, `lambda_null`, `null_bound`), `PolytomyMix` (`null_mixture`) |
| Prop. 9.1 | 2^{n−1}−n−1 non-trivial splits; independent sets and completions have at most n−3 members | `Size` (`card_nontrivial`, `independent_le`, `completions_le`) |
| Prop. 9.2 | Crossing set: an edge's split conflicts with A\|B iff the edge lies in T[A] and T[B]; these edges are internal, joined by paths of crossing edges, and non-empty for binary T and a false split | `Crossing` (`crossing_iff`, `crossing_internal`, `crossing_path`, `crossing_nonempty`) |
| Prop. 9.3 | Five witnesses: the line graph of K₅, an induced copy for n ≥ 5, induced 4- and 5-cycles; chordal and perfect graphs defined, and the conflict graph neither chordal nor perfect for every n ≥ 5 | `Five` (`Chordal`, `Perfect`, `conflictGraph`, `conflict_not_chordal`, `conflict_not_perfect`, `card_conflict_five`) |
| Thm 9.4 | Dynamic programme over subsets: the optimum satisfies the recurrences for F and P, any solution of them equals it, and F(X∖{x}) is the maximum weight of a compatible set; at most 5·3ⁿ⁻¹ operations | `Dynamic` (`opt_rec_F`, `opt_rec_P`, `dp_unique`, `dp_correct`, `totalCost_le`) |

## How the report's objects are encoded

Witnesses are `Fin n`. A split is recorded by one of its sides. Where splits are counted or
compared, the side used is the one away from a fixed reference witness `r`, so that each unordered
split has one representative. A stemma is its split system (`Splits.IsSystem`), and a binary stemma
is a system of exactly n−3 splits (`Splits.IsBinary`). `Buneman.buneman` connects split systems to
trees, as Mathlib graphs, and `BinaryTree.isBinary_iff_binary_tree` shows that the systems of n−3
splits are exactly the split systems of binary trees: the witnesses label the leaves bijectively,
and every other vertex has degree three. Probabilistic results take independent units on a probability space; the
consistency theorems use, for each split, the indicators that units propose it.

## Where Lean says more or less than the report

- **Model hypotheses.** Exclusivity of conflicting proposals (Lemma 3.5) enters the pairwise bound
  and the rival test as a property of the units. In Thm 7.9 the units are independent for each
  split, and the binomial law of the supports is derived from that. In Thm 7.12 the units' data (complete proposals and
  illegibility) are independent and identically distributed, and the restriction indicators are
  derived from them. In Thm 7.14(c) the units are i.i.d. through their partial proposals, as in
  (b), with unit 0 following the illegibility model. In Thm 8.6 the law of the units enters
  through their means, the supports of the attraction model computed in `Quartet.lean`; likewise
  in Prop. 8.14, with the drift tree's supports of `DriftGen.lean`, and in Cor. 8.10, with those of
  the irreversible model. The irreversible model of Prop. 8.9 and Cor. 8.10 is its own explicit finite
  distribution over mark sets (`Irreversible.pM`), not the α = 1 case of `Attraction.wt`. In
  Thms 8.5, 8.7 and 8.8 the attraction model is the explicit finite distribution of the outcomes
  (innovating edges, attractive readings) of one unit (`Attraction.wt`); the random-rate mixture
  of Prop. 8.8 is a probability measure ν on [0, ρ_max].
- **Unions.** The consistency bounds sum over any set R containing every split of positive expected
  support; the report's R = T ∪ F has \|R\| ≤ n−3+K.
- **Complexity.** Cor. 4.2: the decision version of the maximum compatible set problem is
  NP-complete, with unit weights and with weights in ℕ, with polynomial time on multi-tape Turing
  machines: in NP by a certificate selecting candidates, NP-hard by a polynomial-time reduction from
  Independent Set, the weighted problem by the reduction from unit weights. The languages are
  exactly `CompatibleSplits` and `WeightedSplits`: well-formed instances (every candidate side a set
  of the listed witnesses, with at least two witnesses on each side; malformed instances are
  no-instances) with m pairwise compatible candidates, or compatible candidates of total weight at
  least k. The classes, the
  encodings and Karp's theorem are those of `cslib-frontier`. Weights sit on the candidate entries,
  and a target weight is part of the input. The weight-preserving reduction from MWIS with arbitrary
  weights is stated in the operation-count model. Thm 5.3 treats the solver and the search for an infeasible core abstractly.
  Thm 9.4 is the correctness of the recurrences, for any element of C in place of min C, and the
  O(3ⁿ) count is in a cost model that charges the additions and comparisons the recurrences
  prescribe, each table entry once (a tick count, not a machine model).
- **Encodings.** In Prop. 9.2, T[A] is given by its edges, those on the paths between witnesses of
  A, and connectedness is stated as: every edge on the path between two crossing edges crosses.
  In Thm 7.14(c) each unordered partial split is recorded once (`canon`), so that M is
  `Cutting.M`; the condition δ < γ/(2(n−1)μ + 2μ₂) is stated multiplicatively. In Thms 8.5, 8.7
  and 8.8 a rooted stemma is given by the clades of its edges, and Prop. 8.8's vertex by its
  children (`PolytomyNull.Vertex`). The report's O(ε) and O(ε³) are explicit bounds in s = Σπ:
  Pr(\|M\| ≥ 3) ≤ s³/6 (Prop. 8.7) and 7s³, 7 Eρ³ s³ (Prop. 8.8, for s ≤ 1, ρ_max s ≤ 1).
- **Graph classes.** Mathlib defines neither chordal nor perfect graphs; `Five` defines them on
  `SimpleGraph` (chordal: no induced cycle of length ≥ 4, the usual equivalent of "every cycle of
  length ≥ 4 has a chord"; perfect: clique number = chromatic number on every induced subgraph,
  with Mathlib's `cliqueNum` and `chromaticNumber`). The conflict graph has one vertex per split,
  its side away from a reference witness. The line graph of K₅ appears through its adjacency on
  pairs.
- **Edge cases.** In `bedier_threshold`, the KL form of Thm 8.2, a true split of rate exactly 1
  gets a trivial term (≥ 1) instead of 0; `bedier_threshold_kl` omits those terms, as the report
  does, and the simplified form is exact.
- **Stronger in Lean.**
  - Thm 4.1 needs no \|V\| ≥ 2.
  - Thm 6.2 compares T with every compatible set, not only sets of candidates.
  - Thm 7.1 needs no m_σ > 0.
  - Prop. 7.8 needs equal block means, not identically distributed blocks.
  - In Prop. 7.15 the four-part lemma holds for every set O, without the size conditions, and any
    split of T′ crossed by σ gives the parts; the margin and consistency need no δ ≤ 1/2, which
    follows from the condition since γ ≤ μ (`margin_le_mu1`).
  - Prop. 8.3 (`prop:gap`) needs only that every false value is at most a, not that a is
    attained, and every largest gap separates (ties included).
  - Cor. 8.7 (`cor:dominance`) is proved outcome by outcome (a rooted cluster is a reading class),
    so it holds for every split, true or false, and for the exact supports, not only at second
    order.
  - Prop. 8.14 (`prop:drift`): in the rooted coding the drifted family {{1,2}, {1,2,3}} is shown
    to be selected (eventually the unique maximum, almost surely), not only T to be lost.
  - Thms 7.4(b) and 7.14(b) hold almost surely (eventually) with pairwise independence only, and
    the report's statements in probability are derived from them.

## Checks

`lake build` checks every proof. `lake env lean scripts/Audit.lean` checks that every declaration of
the library, vendored files included, depends only on `propext`, `Classical.choice` and
`Quot.sound`. A `sorry` would show as `sorryAx` and fail the audit. CI (GitHub Actions) runs both on
every push.

`StemmaLean/Statements.lean` is the single audit surface: for each numbered result of the report,
in report order, its main theorems restated in full and proved by the library, with the
definitions they use pinned by `rfl`. It is generated by `scripts/ExtractStatements.lean`, which
also prints every statement quoted in the report (`statements.json`); the report's code blocks
are regenerated from that file, never copied by hand (`scripts/README.md`).

## Credits

The complexity classes, polynomial-time reductions, NP verifiers and the NP-hardness of Independent Set used in
`NPHard.lean` and `NPComplete.lean` are those of [cslib-community/cslib-frontier](https://github.com/cslib-community/cslib-frontier)
and [leanprover/cslib](https://github.com/leanprover/cslib) (Apache-2.0), a dependency, pinned in
`lakefile.toml`.

`StemmaLean/Vendor/XTree.lean` and `StemmaLean/Vendor/SplitsEquivalence.lean` are the Splits
Equivalence Theorem of [vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics)
(commit `f1a3592`), under the Apache License 2.0
([`LICENSES/Apache-2.0-lean4-phylogenetics.txt`](LICENSES/Apache-2.0-lean4-phylogenetics.txt)). The
files are vendored unchanged except for a header and one import path.

Related work: `facebookresearch/atlas-lean` formalises unrooted binary trees with the same hypotheses
(`UnrootedBinaryTree`: a tree, leaves labelled bijectively, internal vertices of degree three) and a
Buneman-type result on split systems; it is not used here. `BinaryTree.lean` proves the n−3 count
differently, by counting the vertices of the binary tree and of the tree that the vendored Buneman
proof builds from its split system. `vltanh/lean4-gusfield2007` formalises the perfect phylogeny
theorem (pairwise compatibility of binary characters) and the incompatibility graph.

## Licence

MIT, except the vendored files above (Apache-2.0).
