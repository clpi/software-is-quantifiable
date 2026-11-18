# Occurrence, scope, and interval verification

This verification completes the occurrence/scope proof branch against main
`74565dab80a735888c637d39690bdc0ebc5b5bba`. It preserves that revision's full
profile interface, alignment rules, behavior gate, and both worked examples.

The source changes prove:

- `Finiteness.orderings_exact`: exact multiplicities and allowed venues.
- `Finiteness.orderings_reference_exact`: exact domain agreement with the
  former Cartesian filter, preserving schedule values rather than list order
  or repeated copies.
- `Finiteness.orderings_valid`: projection to the existing coverage contract.
- `Finiteness.combine_orderings`: tagged composition preserves multiplicities.
- `Coverage.scoped_recorded_exact`: exact lookup under supplied scope tags.
- `Coverage.audit_complete`: exact coverage given a complete handle manifest.
- `Coverage.scoped_audit_complete`: the same exactness for mixed-scope
  manifests, with scope projection and scope-specific validation at every row.
- `Coverage.scoped_platform_coverage`: same-scope row evidence through an
  abbreviation of the existing platform premise.
- `Pareto.separated_iff_all`: necessary and sufficient strict separation for
  independent rectangular realization sets.
- `Pareto.replacement_iff_all`: the existing context/behavior replacement gate
  is necessary and sufficient for nonregression over those realization sets.

## Replay

Use the repository-pinned Lean toolchain. Supply its directory explicitly and
choose an output directory outside this checkout:

```sh
python3 verification/occurrences/check.py \
  --toolchain-bin /absolute/path/to/lean-4.19.0-linux/bin \
  --output /absolute/path/to/occurrence-verification
```

The runner performs a clean default build with warnings as errors, the existing
Pareto controls, the new boundary controls, both existing worked examples, and
a dependency audit of every public theorem in the imported source modules.
It allows only `propext`, `Classical.choice`, and `Quot.sound` in those reports.

Each deliberately false claim must fail specifically because Lean's reduction
finds the proposition false. Syntax, import, missing-instance, timeout, and
other failures do not satisfy that check. The claims cover substituted
multiplicity, wrong scope, invalid witnesses, a missing execution hidden by
an empty manifest, overlapping bounds, lost behavior, and an equal-cost tie
misclassified as strict improvement.

Mixed-scope coverage and duplicate branch choices have separate deliberate
false-claim controls. The positive suite also checks the scope-specialized
platform premise and different validator policies in different scopes.

## Eliminated intermediate schedule space

| Qualification | Former Cartesian list size | Constructive output size |
|---|---:|---:|
| Runs `[A,A,B]`, one venue | 27 | 3 |
| Three distinct runs, two venues | 216 | 48 |
| Twelve equal run values, one venue | 8,916,100,448,256 | 1 |

The former sizes follow from `schedules_card`; the new sizes are executable
Lean reduction controls. The enormous former list was not materialized as a
timing experiment. `orderings_reference_exact` proves that this elimination
preserves exactly the admitted schedule values. Distinct invocation IDs remain
distinct choices; only duplicate equal values lose duplicate enumeration copies.
The returned list can still be large when there are many distinct schedules.

The committed `evidence/record.json` records the commands, source and log
hashes, toolchain identity, complete theorem inventory, and observed outcomes.
All verification subject hashes are checked again after execution.

## Exact boundary

Run values retain multiplicity. Distinct invocation lineage still requires
distinct admitted identifiers. Execution coverage is existential over opaque
handles, so a repeated equal handle can share one witness. Supplied scope tags
are filtered, not authenticated; validator soundness, scope binding, and the
independent manifest remain ingress obligations.

The interval converse assumes the full independent product of the supplied
boxes. Coupled physical realizations can exclude its extremal witness. Weak
replacement permits ties. Neither this verification nor an enumerated schedule
space establishes complete physical observation or universal Pareto optimality.
