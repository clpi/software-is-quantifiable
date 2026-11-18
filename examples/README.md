# Repairing a four-shard execution ledger

| Before | After |
|---|---|
| 4 records, 2 executions missing | 2 appended records, 0 missing |

The roster names shards 10, 20, 30, and 40. Shard 10 was recorded twice, 30 has a zero-event record, and 40 is absent. Comparing record counts would declare the campaign complete.

## Why the bound holds

The repository’s missing-roster checker identifies exactly 30 and 40. A record carries one execution ID. The proof quantifies over arbitrary patches and shows every successful append has at least two records. Appending two valid records for 30 still leaves 40 missing.

## Replay

Run from the repository root with Lean 4.15.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](LedgerRepair.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

This fixture accepts positive event counts and trusts the independent roster. Physical authenticity and completeness of the production sensor remain external obligations.
