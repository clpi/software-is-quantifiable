# Pareto correction: scope and reproducible evidence

Date: 2026-11-18. Base: 37917a4195efb1d0423a422ee954d767a9be1cd3.

## Why a correction is needed

Non-domination alone does not imply no regression. The incumbent (1,10)
and candidate (10,1) are incomparable on the existing minimized time and
compute axes. Both belong to the frontier; the latter regresses time.
The old behavior-only gate also does not compare costs.

The unrestricted frontier remains available for exploration. The new
admitted frontier filters by componentwise noWorse. Retaining the
incumbent makes it nonempty; admitted_frontier_sound proves every
guarded frontier point is no worse and is nondominated among the
original candidates. No weighted scalarization or extra axis is added.

acceptsRelease checks a common context key, behavior-list inclusion,
and noWorse. These supplied context/behavior/measurement values are
model inputs, not automatically certified physical measurements.
The context key must bind axes, workload, venue and measurement semantics.
No guarantee is made about unseen candidates or empirically unvalidated
realizations. separated_sound retains its all-in-bound-realizations result.

## Reproduction

With the repository's pinned Lean 4.15.0 toolchain:

```sh
set -eu
lake build
lake env lean -DwarningAsError=true SoftwareIsQuantifiable/Pareto.lean
lake env lean -DwarningAsError=true verification/ParetoControls.lean
```

All three commands completed with exit 0 in the publication checkout.
The full build covers all five modules and the root importing them.
Unchanged Fold, Coloring and Coverage emit unused-variable/section
warnings; the corrected Pareto module and controls emit no warnings.

Independent review also checked the corrected module and controls with
Lean 4.19.0. Eight executable guards and four proof examples cover
incomparable frontier points, rejection of either regressing axis,
context mismatch, missing behavior, accepted ties and strict improvement,
and an empty guarded list when no baseline is retained.

New theorem axiom output:
- frontier_can_regress: propext, Quot.sound
- admitted_frontier_exists: propext, Classical.choice, Quot.sound
- admitted_frontier_sound: propext
- acceptsRelease_iff: propext, Quot.sound

No sorry, admit, new axiom, or unsafe declaration was introduced.
