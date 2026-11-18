# software-is-quantifiable

Lean 4 formalization of the qualification-of-software claims: the
construction behind "a proposal for the qualification of software"
(the decidability-engine spec, sections 16–22). Each claim is taken
as stated in the spec, formalized in Lean, and then proven,
disproven, or recorded as a named premise. Nothing here is proven
on the strength of source text: the verdicts below stand on the
recorded build run with zero `sorry`s.

Build: `lake --wfail build` with the pinned toolchain
(`leanprover/lean4:v4.19.0`). Lean core only — no Mathlib — by
choice: a core development that builds is worth more than a
Mathlib development that cannot, and every claim here goes through
with elementary means (lists, characteristic functions, counting
over a finite universe, induction). `--wfail` treats warnings as
errors.

## Build evidence

Recorded on this branch with Lean 4.19.0 (commit `6caaee842e94`).
`lake --wfail build` exited 0: warnings are errors, and the build
reported none. Zero `sorry`s, zero `admit`s, and zero added
`axiom`s. `#print axioms` on the headline theorems shows only
`propext`, `Classical.choice`, and `Quot.sound`, or no axioms.
`Coverage.coverage` is an abbreviation of `PlatformPremise.mediated`,
not a theorem. `Pareto.separated_sum`, `Pareto.scalar_optimum_undominated`,
`Pareto.dominates_iff_interface`, `Interface.noWorse_trans`,
`Interface.dominates_trans`, and `Coverage.unrestricted_witness`
depend on no axioms.

The notes below are the earlier 4.15.0 records for the Pareto and
ledger repairs that this branch merges. They are not the record for
the current toolchain pin.

### Pareto correction verification (2026-11-18)

The preceding Pareto correction passed `lake build` with its unchanged
Lean 4.15.0 pin. That recorded tree retained unused-variable/section-variable
warnings in Fold, Coloring, and Coverage; they were not proof failures.
The changed Pareto module also passed separately with
`-DwarningAsError=true`. Independent review checked it and eight
executable guards plus four proof controls under both Lean 4.15.0
and 4.19.0. See [reproduction and evidence](verification/pareto-repair.md).

### Integrated coverage and interval verification (2026-11-18)

This change builds on `a1d84c603906edfbf34dd117e5bd5de986db3940`, retaining
the validated-ledger/roster owner and the incumbent-guarded release gate.
The final source was checked with the complete official Lean 4.15.0 Linux
toolchain, compiler commit `11651562caae`:

* `lake clean` followed by `lake --wfail build`: all five modules and root,
  exit 0, no warnings.
* All 63 declared theorems audited with `#print axioms`: exit 0; dependencies
  limited to `propext`, `Classical.choice`, and `Quot.sound`.
* The unchanged upstream eight executable guards and four proof controls:
  exit 0 with `-DwarningAsError=true`.
* Four damaged definitions rejected with exit 1: fabricating recorded
  coverage, bypassing the validator, omitting compute non-regression,
  and omitting behavior inclusion from the shared release gate.

The [portable replayer and raw evidence](verification/coverage/README.md)
are committed with the source. The final
[record.json](verification/coverage/record.json) SHA-256 is
`2e05339a2ebbe6070ef408552296b9a3e26e1e408b06141f383585637461ab60`.

## The claims and their verdicts

| # | Claim (spec source) | Lean form | Status |
|---|---|---|---|
| 1 | Finiteness: a qualification — named software, named criteria, the behavior intended under them — forms a finite problem space (§20.0 presentation lemma, §20.1) | `Finiteness.schedules_finite`, `Finiteness.valid_orderings_finite`: a qualification's runs and venues are lists by construction, and an explicit finite list enumerates every schedule / valid ordering over them | PROVEN |
| 2 | Fold correctness: the witness join is a semi-lattice, so the accounting fold is order- and duplication-independent and exactly recomputable (§17.4, §17.8, §22.D) | `Fold.join_assoc`, `Fold.join_comm`, `Fold.join_idem`, `Fold.account_eq_true_iff`, `Fold.account_ext`, `Fold.account_perm`, `Fold.account_append_self`, `Fold.account_append` | PROVEN |
| 3 | Coloring: relative to a named snapshot, the coloring computed as a least fixed point over ground Horn rules is sound and complete, and the iteration terminates (§5, §16.8, §20) | `Coloring.exists_fixed_point` (a fixed point is reached within `U.length` steps), `Coloring.coloring_fixed`, `Coloring.coloring_sound`, `Coloring.coloring_complete` | PROVEN, under one stated side condition: the snapshot's universe names every conclusion the rules can produce — that is what makes the snapshot a snapshot |
| 4 | Pareto selection, separation, and no-regression admission | `Pareto.separated_sound`, `Pareto.frontier_nonempty`, `Pareto.separated_of_refined`, `Pareto.admitted_frontier_exists`, `Pareto.admitted_frontier_sound`, `Pareto.separated_sum`, `Pareto.separated_parallel`, `Pareto.replacement_no_regression` | PROVEN at the level of bounds and named scopes. `Pareto.frontier_can_regress` shows frontier membership alone permits an incomparable regression |
| 4a | No qualified behavior lost, one half of admission | `Pareto.noQualifiedBehaviorLost`, `Pareto.noQualifiedBehaviorLost_iff`, used by `Pareto.acceptsRelease` | PROVEN. The qualified list is `PriorQualification.qualified` from the previous closure. The submission only offers `BehaviorSubmission.offered`. `omitted_qualified_behavior_refused` and `empty_submission_refused_when_qualified` refuse a submission that drops or empties that prior set |
| 4′ | Overlapping intervals alone guarantee per-execution dominance | `Pareto.not_per_execution_dominance` | DISPROVEN. This does not refute `separated_sound` |
| 4″ | Every Pareto point is a positive weighted-sum minimum; the Minkowski sum of frontiers is the frontier | `Pareto.not_scalarized`, `Pareto.scalar_frontier_point`, `Pareto.scalar_optimum_undominated`, `Pareto.minkowski_frontier_subset`, `Pareto.not_frontier_minkowski` | The subset direction and "a positive-weight minimum is undominated" are PROVEN. Both universal converses are DISPROVEN |
| 5 | Coverage of named roster executions (§19) | `Coverage.coverage`, an `abbrev` of `PlatformPremise.mediated` | PREMISE, not a theorem. `sensorBelow` is `sensorSitsBelow sensorPrivilege observedPrivilege = true`, a comparison of two privilege ranks. `coverage_iff` and `coverage_missing_iff` state the falsification condition on the roster |
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
| 13 | The theorems apply to a two-component command path (synthetic) | `Instance.service_schedule_card` (16), `Instance.service_valid_count` (8), `Instance.accounts_compose`, `Instance.not_coloring_distributes_on_path`, `Instance.service_compounds`, `Instance.path_separated`, `Instance.deployments_frontier`, `Instance.trimmed_rejected`, `Instance.empty_submission_rejected`, `Instance.request_two_uncovered`, `Instance.path_requests_covered` | PROVEN for the synthetic data in `Instance.lean`. Not measurements of a deployed system |

## Coverage against an actual ledger

`Coverage.unrestricted_witness` proves that a record containing the execution's
ID and zero events witnesses every execution under the original ID-equality
predicate. This construction reads no ledger. The protection-model premise
therefore supplies no evidence that any particular collector observed a run.

Use `Coverage.recorded valid ledger e` for a live ledger and
`Coverage.missing valid ledger roster` for a finite, independently supplied
roster. `recorded_exact` extracts a matching record present in the ledger
that passed the supplied validator. `missing_exact` identifies each uncovered
execution. `missing_append` proves that the executions missing from two
combined ledgers are exactly those missing from both. With an empty ledger the
entire roster is missing. Authenticity, unique execution IDs, completeness of
the roster, and whether the validator enforces the intended policy are
deployment obligations.

`PlatformPremise valid ledger roster` uses that same `recorded` checker.
`coverage` is an abbreviation of the premise field `mediated`, not a derived
theorem. `sensorBelow` is `sensorSitsBelow sensorPrivilege observedPrivilege = true`:
the sensor's privilege rank is strictly below the observed software's rank.
`coverage_iff`
requires roster membership for a missing execution to falsify coverage, and
`coverage_missing_iff` identifies complete coverage with `missing = []`.
`empty_roster_covered` establishes vacuous coverage of an empty actual domain;
`empty_ledger_has_no_platform_premise` rejects mediation of a nonempty roster
by an empty ledger. No separate witness-membership or coverage evaluator is
introduced. Callers of the former unrestricted `PlatformPremise`, `coverage`,
and `coverage_iff` argument lists must supply the validator, ledger, and roster.

## Scope of the combined result

`noQualifiedBehaviorLost` is one half of `acceptsRelease`. It compares the
submission's offered behaviors to the prior qualification's qualified list.
`acceptsReplacement` delegates to that same gate using candidate upper bounds
and incumbent lower bounds. Its all-realizations theorem is conditional on
those bounds. The exploratory frontier and the guarded frontier remain
available.

The finite schedule construction covers the supplied run and venue lists at
the specified schedule length. Witness accounting proves set union, not
physical authenticity or zero runtime replay cost. Coloring computes the
conjunctive Horn consequences of the supplied seeds and rules; a dependency
projection cannot replace a multi-premise rule with independent implications.
External evidence must bind the candidate, workload, target, protocol, units,
axes, and behavior contract. The formal build does not prove catalogue
completeness, physical mediation, or the truth of an unvalidated observation.

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
  4′. Interval cost bounds on two axes; separation; the exploratory
  frontier; monotone refinement; guarded no-regression selection and
  combined release admission and its interval adapter.
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

* Zero `sorry`s. The verdict applies to each exact formal statement
  and its premises. Broader physical or end-to-end claims do not
  follow from a successful build. Anything unproven is listed as OPEN;
  at the recorded build, no claim is OPEN.
* Release-sequence monotonicity, and the two-sided behavior order
  `required ⊆ behaviors ⊆ allowed`, belong to the sibling repositories.
  This repository names only the "no qualified behavior lost" half.
* A claim that needed a side condition (claim 3's universe
  condition) is proven in its conditioned form, with the condition
  stated in the table — never silently weakened.
* The build evidence (command, exit state, theorem inventory) is
  recorded in the lane record that accompanies this repository.

## Exact admission and counterexamples

* `Finiteness.orderings_exact` characterizes the output of an executable schedule filter in both directions. It preserves run multiplicities and assigns every occurrence to an allowed venue. With runs [A,A,B], the earlier distinct-name coverage predicate also accepts [A,B,B]. The new filter rejects it. Applications that distinguish separate invocations must name them separately.
* `Coverage.scoped_recorded_exact` checks the scope before the existing ledger lookup. Two scopes may use the same execution ID. `Coverage.audit_complete` gives an exact audit of actual occurrences when an independent manifest enumerates precisely those occurrences. An empty or incomplete manifest can conceal a lost record.
* `Pareto.separated_iff_all` and `replacement_iff_all` establish the converse of the interval guarantees. The extremal corner pair witnesses necessity for independent rectangular boxes. The existing release gate retains its context and behavior requirements. A workload that couples the realizations can exclude that corner pair.

Build the default Lake target with the pinned Lean 4.19.0 toolchain using `lake --wfail build`.
