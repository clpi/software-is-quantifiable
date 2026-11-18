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

## The claims and their verdicts

| # | Claim (spec source) | Lean form | Status |
|---|---|---|---|
| 1 | Finiteness: a qualification — named software, named criteria, the behavior intended under them — forms a finite problem space (§20.0 presentation lemma, §20.1) | `Finiteness.schedules_finite`, `Finiteness.valid_orderings_finite`: a qualification's runs and venues are lists by construction, and an explicit finite list enumerates every schedule / valid ordering over them | PROVEN |
| 2 | Fold correctness: the witness join is a semi-lattice, so the accounting fold is order- and duplication-independent and exactly recomputable (§17.4, §17.8, §22.D) | `Fold.join_assoc`, `Fold.join_comm`, `Fold.join_idem`, `Fold.account_eq_true_iff`, `Fold.account_ext`, `Fold.account_perm`, `Fold.account_append_self`, `Fold.account_append` | PROVEN |
| 3 | Coloring: relative to a named snapshot, the coloring computed as a least fixed point over ground Horn rules is sound and complete, and the iteration terminates (§5, §16.8, §20) | `Coloring.exists_fixed_point` (a fixed point is reached within `U.length` steps), `Coloring.coloring_fixed`, `Coloring.coloring_sound`, `Coloring.coloring_complete` | PROVEN, under one stated side condition: the snapshot's universe names every conclusion the rules can produce — that is what makes the snapshot a snapshot |
| 4 | Pareto: the computed ordering is Pareto optimal, never worse than the incumbent, regression-free (§20.1, §20.2, §21.3) | `Pareto.separated_sound` (separation under interval bounds decides dominance for every realization), `Pareto.frontier_nonempty`, `Pareto.frontier_not_dominated`, `Pareto.separated_of_refined` (refinement is monotone), `Pareto.accepts_iff` (the regression gate accepts exactly the candidates that drop no qualified behavior) | PROVEN at the level of bounds, which is the level the spec claims |
| 4′ | Per-execution dominance: a dominated schedule finishes worse on every single execution | `Pareto.not_per_execution_dominance`: concrete counterexample (bounds [1, 100] against [2, 3]; the dominated schedule can realize 1 against 3) | DISPROVEN — the spec itself names this boundary at §20.4; dominance is a statement about bounds, never about one execution |
| 5 | Coverage universality: every execution crosses the kernel boundary, hence is witnessed (§19) | `Coverage.coverage`, conditional on `Coverage.PlatformPremise` | PREMISE — assumed, named, never counted as proven. The spec states this as a protection-model argument on three named assumptions (§19.4) with an exact falsification condition (§19.5, `Coverage.coverage_iff`). The mathematics adds nothing here and this repository says so: every coverage theorem takes the premise as an argument, so it cannot be smuggled in as a theorem |

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

The five modules and root have also been compiled from the same sources with
Lean 4.15.0 and 4.19.0. The package remains pinned to 4.15.0.

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
