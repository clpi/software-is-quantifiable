# software-is-quantifiable

Lean 4 formalization of the qualification-of-software claims: the
construction behind "a proposal for the qualification of software"
(the decidability-engine spec, sections 16–22). Each claim is taken
as stated in the spec, formalized in Lean, and then proven,
disproven, or recorded as a named premise. Nothing here is proven
on the strength of source text: the verdicts below stand on the
recorded build run with zero `sorry`s.

Build: `lake build` with the pinned toolchain
(`leanprover/lean4:v4.15.0`). Lean core only — no Mathlib — by
choice: a core development that builds is worth more than a
Mathlib development that cannot, and every claim here goes through
with elementary means (lists, characteristic functions, counting
over a finite universe, induction).

## Build evidence

Recorded 2026-11-18 on Lean 4.15.0 (commit 11651562caae).
`lake build` exited 0 and compiled the root module, which
imports every module below. Zero `sorry`s and zero added
`axiom`s in the sources (search over the tree). Axiom audit of
the headline theorems (`#print axioms`): each depends only on
Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), or on none of them. No `sorryAx`, no custom
axiom. In particular `Interface.noWorse_trans`,
`Interface.dominates_trans`, `Pareto.separated_sum`,
`Pareto.dominates_iff_interface`,
`Coverage.unconstrained_witness_exists`, and
`Coverage.not_ledger_from_placement` depend on no axioms.
`Coverage.coverage` is unchanged: it is the projection of the
named premise.

## The claims and their verdicts

| # | Claim (spec source) | Lean form | Status |
|---|---|---|---|
| 1 | Finiteness: a qualification — named software, named criteria, the behavior intended under them — forms a finite problem space (§20.0 presentation lemma, §20.1) | `Finiteness.schedules_finite`, `Finiteness.valid_orderings_finite`: a qualification's runs and venues are lists by construction, and an explicit finite list enumerates every schedule / valid ordering over them | PROVEN |
| 2 | Fold correctness: the witness join is a semi-lattice, so the accounting fold is order- and duplication-independent and exactly recomputable (§17.4, §17.8, §22.D) | `Fold.join_assoc`, `Fold.join_comm`, `Fold.join_idem`, `Fold.account_eq_true_iff`, `Fold.account_ext`, `Fold.account_perm`, `Fold.account_append_self`, `Fold.account_append` | PROVEN |
| 3 | Coloring: relative to a named snapshot, the coloring computed as a least fixed point over ground Horn rules is sound and complete, and the iteration terminates (§5, §16.8, §20) | `Coloring.exists_fixed_point` (a fixed point is reached within `U.length` steps), `Coloring.coloring_fixed`, `Coloring.coloring_sound`, `Coloring.coloring_complete` | PROVEN, under one stated side condition: the snapshot's universe names every conclusion the rules can produce — that is what makes the snapshot a snapshot |
| 4 | Pareto: the computed ordering is Pareto optimal, never worse than the incumbent, regression-free (§20.1, §20.2, §21.3) | `Pareto.separated_sound` (separation under interval bounds decides dominance for every realization), `Pareto.frontier_nonempty`, `Pareto.frontier_not_dominated`, `Pareto.separated_of_refined` (refinement is monotone), `Pareto.accepts_iff` (the regression gate accepts exactly the candidates that drop no qualified behavior) | PROVEN at the level of bounds, which is the level the spec claims |
| 4′ | Per-execution dominance: a dominated schedule finishes worse on every single execution | `Pareto.not_per_execution_dominance`: concrete counterexample (bounds [1, 100] against [2, 3]; the dominated schedule can realize 1 against 3) | DISPROVEN — the spec itself names this boundary at §20.4; dominance is a statement about bounds, never about one execution |
| 5 | Coverage universality: every execution crosses the kernel boundary, hence is witnessed (§19) | `Coverage.coverage`, conditional on `Coverage.PlatformPremise` | PREMISE — assumed, named, never counted as proven. The spec states this as a protection-model argument on three named assumptions (§19.4) with an exact falsification condition (§19.5, `Coverage.coverage_iff`). Every coverage theorem of this form takes the premise as an argument |
| 5a | Unconstrained witness existence (`Witness` is any pair of naturals with a matching id) discharges §19 | `Coverage.unconstrained_witness_exists` | PROVEN, and it does **not** discharge claim 5. A matching pair of naturals can be built with no sensor and no ledger. Ledger membership is the claim that still bites |
| 5b | Ledger coverage: every execution occurs in a named ledger. Sensor-below and append-only imply it | `Coverage.LedgerPremise` (assumed); `Coverage.not_ledger_coverage_empty`; `Coverage.not_ledger_from_placement` | PREMISE for `LedgerPremise`. DISPROVEN as a theorem: the empty ledger misses execution `0`, and `True → True → LedgerPremise` fails on that ledger |
| 5c | Named coverage composes: ledgers that cover each component's execution list cover the concatenation | `Coverage.ledger_coverage_compose` | PROVEN from the per-component membership hypotheses. It does not produce `LedgerPremise` for every `Execution` |
| 6 | Profile preorder and Pareto dominance on a measure space (shared interface) | `Interface.noWorse_refl`, `Interface.noWorse_trans`, `Interface.noWorse_antisymm`, `Interface.not_dominates_self`, `Interface.dominates_trans`, `Interface.frontier_exact` | PROVEN on aligned profiles. `noWorse` is measures plus preserved observed behavior. The frontier of a finite list is exactly the undominated members |
| 6′ | Measure improvement alone dominates | `Interface.not_dominates_from_measures` | DISPROVEN. Readings `0` against `1` on a minimize axis, with `observed` dropped, are `measuresLe` and `strictlyBetter` and not `dominates` |
| 7 | Products of measure spaces: both halves `noWorse`, one half strict, yields dominance on the concatenation | `Interface.measuresLe_append_iff`, `Interface.noWorse_append`, `Interface.dominates_append_of_halves`, `Interface.dominates_append_left`, `Interface.dominates_append_right` | PROVEN |
| 7′ | `noWorse` / `dominates` on a concatenation splits into the halves | `Interface.not_noWorse_append_converse`, `Interface.not_dominates_append_splits` | DISPROVEN. Observed bits are conjoined, so a dropped behavior on one half is hidden when the other half's observed bit is already false |
| 8 | Assemblies of per-symbol profiles compose, matched by symbol | `Interface.releaseLe_refl`, `Interface.releaseLe_trans`, `Interface.releaseLe_append`, `Interface.releaseDominates_append_left`, `Interface.releaseDominates_append_right` | PROVEN. This is one measurement of many symbols, not monotonicity along a sequence of releases |
| 8′ | Index order is the profile preorder | `Interface.not_index_aligned_preorder` | DISPROVEN. Swapping two symbols keeps `releaseLe` and breaks a position-wise comparison of `9` against `1` |
| 9 | Exact finite enumerator, and closure of valid schedules under side-respecting composition | `Finiteness.listsOfLen_length`, `Finiteness.schedules_card`, `Finiteness.validB_iff`, `Finiteness.mem_validSchedules`, `Finiteness.combine_valid`, `Finiteness.mem_composites` | PROVEN. `validSchedules` contains a schedule iff it is `Valid` |
| 9′ | Every `Valid` schedule of a product qualification is a side-respecting composite | `Finiteness.not_all_valid_side_respecting` | DISPROVEN. A run of one component may be wired to a venue of the other. Composition is `combineSched` |
| 10 | The witness fold composes across a sum of witness domains | `Fold.account_sum` | PROVEN. The account of a tagged concatenation is the side-by-side pair of the component accounts |
| 11 | Coloring compounds, and segregated domains factor | `Coloring.coloring_mono_seed`, `Coloring.coloring_idem`, `Coloring.coloring_compound`, `Coloring.coloring_segregated_left`, `Coloring.coloring_segregated_right` | PROVEN under the same snapshot condition as claim 3. `C(s₁ ∨ s₂) = C(C(s₁) ∨ C(s₂))`. On a sum of fact domains with no cross-rule, the coloring at each side is that side's coloring |
| 11′ | Coloring distributes over join: qualifying the parts and unioning the colors equals qualifying the join | `Instance.not_coloring_distributes_on_path` | DISPROVEN on the command-path rules. Separate colorings both miss `committed`; closing the joined seed records it. One counterexample refutes the universal claim |
| 12 | Separation is preserved by sequential sums and by parallel makespan (max time, sum compute) | `Pareto.separated_sum`, `Pareto.separated_parallel` | PROVEN |
| 12′ | Every Pareto point is the minimum of some positive weighted sum | `Pareto.not_scalarized`, with `(2, 2)` on the frontier by `Pareto.scalar_frontier_point`. The true direction is `Pareto.scalar_optimum_undominated` | DISPROVEN. `(2, 2)` is undominated by `(0, 3)` and `(3, 0)` and is not a minimizer of any positive weights. A positive-weight minimum is undominated |
| 12″ | The Minkowski sum of frontiers is the frontier of the sum | `Pareto.minkowski_frontier_subset` (the direction that holds); `Pareto.not_frontier_minkowski` | The subset direction is PROVEN (an undominated sum is a sum of undominated points). Equality is DISPROVEN: `(0,3)+(3,0)=(3,3)` is dominated by `(2,0)+(0,2)=(2,2)` |
| 12‴ | The two-axis order is the interface order on time and compute | `Pareto.dominates_iff_interface` | PROVEN. Both axes `minimize`, observed behavior held |
| 13 | The theorems apply to a two-component command path (synthetic) | `Instance.service_schedule_card` (16), `Instance.service_valid_count` (8), `Instance.accounts_compose`, `Instance.not_coloring_distributes_on_path`, `Instance.service_compounds`, `Instance.path_separated`, `Instance.deployments_frontier`, `Instance.trimmed_rejected`, `Instance.cost_does_not_excuse_behavior_drop`, `Instance.request_two_uncovered`, `Instance.path_requests_covered` | PROVEN for the synthetic data in `Instance.lean`. Not measurements of a deployed system |

## Reading the modules

* `SoftwareIsQuantifiable/Finiteness.lean` — claim 1. The
  qualification is a structure whose fields are lists; finiteness
  falls out of the definitions, exactly as §20.0 derives it from
  what a qualification is. No finiteness hypothesis appears
  anywhere in this repository.
* `SoftwareIsQuantifiable/Fold.lean` — claim 2. The accounting
  state is the characteristic function of the recorded witness
  set; the join is pointwise union; the fold is shown to record
  exactly the presented set, hence to depend only on the set.
* `SoftwareIsQuantifiable/Coloring.lean` — claim 3. Ground Horn
  rules over a finite fact universe; the closure step iterated;
  termination by a counting argument over the universe; soundness
  and completeness against an inductive derivability relation.
* `SoftwareIsQuantifiable/Pareto.lean` — claim 4 and the disproof
  4′. Interval cost bounds on two axes; separation; the frontier;
  monotone refinement; the regression gate.
* `SoftwareIsQuantifiable/Coverage.lean` — claim 5, as a premise
  with its falsification condition; the vacuous witness theorem;
  ledger coverage and its composition.
* `SoftwareIsQuantifiable/Interface.lean` — the stable interface
  downstream repositories import or mirror. Measure space,
  per-symbol profile, profile preorder, Pareto dominance, and the
  composition laws for measure spaces and symbol assemblies.
  No local imports.
* `SoftwareIsQuantifiable/Instance.lean` — a synthetic
  gate-then-commit command path exercising the theorems.

## Stable interface

`import SoftwareIsQuantifiable.Interface`, or mirror that file.
It is the shared vocabulary for `software-optimality`,
`software-is-composable`, `software-is-incrementally-certifiable`,
`software-is-incrementally-safe`, and
`software-doesnt-have-to-regress`.

What a downstream proof may rely on, and what it guarantees:

| Name | Guarantee |
|---|---|
| `Polarity`, `axisLe`, `axisLt` | On `minimize`, smaller is better. On `maximize`, larger is better. `axisLe` is a preorder; `axisLt` is its strict part and is irreflexive |
| `Axis`, `MeasureSpace` | A measure space is a finite ordered list of named axes. Position in the list is position in a reading vector |
| `Profile` | One symbol, one reading per axis, and a separate `observed` bit. The bit is not a measure |
| `aligned` | The reading vector has one entry per axis. Reflexivity needs this |
| `measuresLe` | Same symbol, no worse on every axis. Reflexive on aligned profiles, transitive. Antisymmetry gives equal symbol and equal readings; it ignores `observed` |
| `behaviorLe` | If the incumbent's observed bit holds, the candidate's does too |
| `noWorse` | `measuresLe` and `behaviorLe`. Reflexive on aligned profiles, transitive, antisymmetric |
| `strictlyBetter`, `dominates` | `dominates` is `noWorse` plus a strict axis. Irreflexive and transitive. Not implied by measure improvement alone |
| `appendProfile` | Same symbol, readings concatenated, observed bits conjoined |
| `measuresLe_append_iff` | Measure comparison splits across a concatenation of spaces when the left vectors have the left space's length |
| `noWorse_append`, `dominates_append_of_halves` | Both halves `noWorse`, and one half strict, yields `noWorse` / `dominates` on the concatenated space |
| `not_noWorse_append_converse`, `not_dominates_append_splits` | The converse is false. Check behavior on the halves |
| `Release`, `releaseLe`, `releaseDominates` | A finite list of profiles over one space, matched by symbol, not by index |
| `releaseLe_append`, `releaseDominates_append_left`, `releaseDominates_append_right` | Assemblies of symbols compose |
| `not_index_aligned_preorder` | Zipping releases by position is not `releaseLe` |
| `frontier`, `frontier_exact` | The undominated sublist of a finite candidate list |

`Pareto.dominates_iff_interface` is the bridge from the existing
two-axis order to `Interface.dominates` on time and compute.
Release-sequence monotonicity is not in this repository.

## Discipline

* Zero `sorry`s. Anything unproven would be listed in this table
  as OPEN with what is missing; at the recorded build, no claim is
  OPEN.
* Release-sequence monotonicity is out of scope. It belongs to
  `software-is-composable`.
* A claim that needed a side condition (claim 3's universe
  condition) is proven in its conditioned form, with the condition
  stated in the table — never silently weakened.
* The build evidence (command, exit state, theorem inventory) is
  recorded in the lane record that accompanies this repository.
