# software-is-quantifiable

Lean 4 formalization of the qualification-of-software claims: the
construction behind "a proposal for the qualification of software"
(the decidability-engine spec, sections 16–22). Each claim is taken
as stated in the spec, formalized in Lean, and then proven,
disproven, or recorded as a named premise. Nothing here is proven
on the strength of source text: the verdicts below stand on the
recorded build run with zero `sorry`s.

Build: `lake --wfail build` with the pinned toolchain
(`leanprover/lean4:v4.15.0`). Lean core only — no Mathlib — by
choice: a core development that builds is worth more than a
Mathlib development that cannot, and every claim here goes through
with elementary means (lists, characteristic functions, counting
over a finite universe, induction).

## Build evidence

Recorded 2026-11-17 on Lean 4.15.0 (commit 11651562caae). The
build machine's disk quota admitted only a partial toolchain
(the compiler and the Init/Std/Lake libraries, without the
Lean-library object files the Lake driver itself loads), so the
recorded run compiled every module directly with `lean` — the
lean equivalent of `lake build` — including the root module,
which imports all five:

* `SoftwareIsQuantifiable/Finiteness.lean` — compiled, exit 0
* `SoftwareIsQuantifiable/Fold.lean` — compiled, exit 0
* `SoftwareIsQuantifiable/Coloring.lean` — compiled, exit 0
* `SoftwareIsQuantifiable/Pareto.lean` — compiled, exit 0
* `SoftwareIsQuantifiable/Coverage.lean` — compiled, exit 0
* `SoftwareIsQuantifiable.lean` (root) — compiled, exit 0

Zero `sorry`s and zero added `axiom`s in the sources (grep over
the tree). Axiom audit of the headline theorems (`#print
axioms`): each depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`,
no custom axiom anywhere. `Coverage.coverage` depends on no
axioms at all: it is the projection of the named premise, which
is passed as an argument, exactly as the PREMISE verdict
requires. On a complete toolchain the same tree builds with
`lake build` unchanged.

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
| 4 | Pareto selection and no-regression admission | `Pareto.frontier_nonempty` preserves the unrestricted trade-off frontier; `Pareto.frontier_can_regress` shows that frontier membership alone permits incomparable regressions. `Pareto.admitted_frontier_exists` and `Pareto.admitted_frontier_sound` add incumbent-guarded selection. `Pareto.acceptsRelease_iff` checks common context, behavior inclusion, and point costs; the interval adapter `Pareto.replacement_no_regression` extends the same gate to every contained realization. | PROVEN at model level, under the stated scope, valid-bound, and baseline-retention premises; measurements and behavior certificates remain scoped inputs |
| 4′ | Overlapping intervals alone guarantee per-execution dominance | `Pareto.not_per_execution_dominance`: bounds [1, 100] against [2, 3] permit realizations 1 against 3 | DISPROVEN for overlapping intervals. This does not refute `separated_sound`, which proves dominance for every pair of in-bound realizations when its separation premise holds |
| 5 | Coverage of named actual executions (§19) | `Coverage.coverage`, `Coverage.coverage_missing_iff`, `Coverage.recorded_exact`, `Coverage.missing_exact` | PREMISE for physical mediation. Coverage is indexed by the validator, recorded ledger, and independent execution roster and is equivalent to an empty missing list. `unrestricted_witness` still demonstrates why constructing an ID-matching value is insufficient. |

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

`PlatformPremise valid ledger roster` now uses that same `recorded` checker.
Its sensor and append-only conditions have proof fields; its mediation field
requires an accepted ledger record for every named execution. `coverage_iff`
requires roster membership for a missing execution to falsify coverage, and
`coverage_missing_iff` identifies complete coverage with `missing = []`.
`empty_roster_covered` establishes vacuous coverage of an empty actual domain;
`empty_ledger_has_no_platform_premise` rejects mediation of a nonempty roster
by an empty ledger. No separate witness-membership or coverage evaluator is
introduced. Callers of the former unrestricted `PlatformPremise`, `coverage`,
and `coverage_iff` argument lists must supply the validator, ledger, and roster.

The preceding ledger repair was compiled under Lean 4.15.0 and 4.19.0. The
integrated verification above uses the package's unchanged 4.15.0 pin.

## Scope of the combined result

`acceptsReplacement` delegates to the existing `acceptsRelease` gate using
candidate upper bounds and incumbent lower bounds. Both context parameters
are retained. Its all-realizations theorem is conditional on those bounds;
observed sample extrema do not automatically establish them. The original
point gate, exploratory frontier, and guarded frontier remain available.

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
  with its falsification condition.

## Discipline

* Zero `sorry`s. The verdict applies to each exact formal statement
  and its premises. Broader physical or end-to-end claims do not
  follow from a successful build.
* A claim that needed a side condition (claim 3's universe
  condition) is proven in its conditioned form, with the condition
  stated in the table — never silently weakened.
* The build evidence (command, exit state, theorem inventory) is
  recorded in the lane record that accompanies this repository.
