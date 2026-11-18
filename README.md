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

The complete repository now passes `lake build` with its unchanged
Lean 4.15.0 pin. Existing unused-variable/section-variable warnings
remain in Fold, Coloring, and Coverage; they are not proof failures.
The changed Pareto module also passes separately with
`-DwarningAsError=true`. Independent review checked it and eight
executable guards plus four proof controls under both Lean 4.15.0
and 4.19.0. See [reproduction and evidence](verification/pareto-repair.md).

## The claims and their verdicts

| # | Claim (spec source) | Lean form | Status |
|---|---|---|---|
| 1 | Finiteness: a qualification — named software, named criteria, the behavior intended under them — forms a finite problem space (§20.0 presentation lemma, §20.1) | `Finiteness.schedules_finite`, `Finiteness.valid_orderings_finite`: a qualification's runs and venues are lists by construction, and an explicit finite list enumerates every schedule / valid ordering over them | PROVEN |
| 2 | Fold correctness: the witness join is a semi-lattice, so the accounting fold is order- and duplication-independent and exactly recomputable (§17.4, §17.8, §22.D) | `Fold.join_assoc`, `Fold.join_comm`, `Fold.join_idem`, `Fold.account_eq_true_iff`, `Fold.account_ext`, `Fold.account_perm`, `Fold.account_append_self`, `Fold.account_append` | PROVEN |
| 3 | Coloring: relative to a named snapshot, the coloring computed as a least fixed point over ground Horn rules is sound and complete, and the iteration terminates (§5, §16.8, §20) | `Coloring.exists_fixed_point` (a fixed point is reached within `U.length` steps), `Coloring.coloring_fixed`, `Coloring.coloring_sound`, `Coloring.coloring_complete` | PROVEN, under one stated side condition: the snapshot's universe names every conclusion the rules can produce — that is what makes the snapshot a snapshot |
| 4 | Pareto selection and no-regression admission | `Pareto.frontier_nonempty` preserves the unrestricted trade-off frontier; `Pareto.frontier_can_regress` shows that frontier membership alone permits incomparable regressions. `Pareto.admitted_frontier_exists` and `Pareto.admitted_frontier_sound` add incumbent-guarded selection: no worse on either existing axis and nondominated among the original candidates. `Pareto.acceptsRelease_iff` checks identical measurement context, qualified-behavior inclusion, and componentwise non-regression. | PROVEN at model level, under the stated scope and baseline-retention premises; measurements and behavior certificates remain scoped inputs |
| 4′ | Overlapping intervals alone guarantee per-execution dominance | `Pareto.not_per_execution_dominance`: bounds [1, 100] against [2, 3] permit realizations 1 against 3 | DISPROVEN for overlapping intervals. This does not refute `separated_sound`, which proves dominance for every pair of in-bound realizations when its separation premise holds |
| 5 | Coverage universality: every execution crosses the kernel boundary, hence is witnessed (§19) | `Coverage.coverage`, conditional on `Coverage.PlatformPremise` | PREMISE — assumed, named, never counted as proven. The spec states this as a protection-model argument on three named assumptions (§19.4) with an exact falsification condition (§19.5, `Coverage.coverage_iff`). The mathematics adds nothing here and this repository says so: every coverage theorem takes the premise as an argument, so it cannot be smuggled in as a theorem |

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
  combined release admission.
* `SoftwareIsQuantifiable/Coverage.lean` — claim 5, as a premise
  with its falsification condition.

## Discipline

* Zero `sorry`s. Anything unproven would be listed in this table
  as OPEN with what is missing; at the recorded build, no claim is
  OPEN.
* A claim that needed a side condition (claim 3's universe
  condition) is proven in its conditioned form, with the condition
  stated in the table — never silently weakened.
* The build evidence (command, exit state, theorem inventory) is
  recorded in the lane record that accompanies this repository.
