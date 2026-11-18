# When can a missing reading be recovered exactly?

| Before | After |
|---|---|
| 55 individual readings for [0,55) | 2 existing interval receipts; no new source run |

The catalog contains [0,100) and [55,100). Their signed difference determines [0,55). The neighboring query [0,56) still has two compatible answers.

## Derivation

For any catalog, two worlds agreeing on all receipts must agree on the requested difference exactly when an undirected path connects its endpoints. Forward traversal adds, reverse traversal subtracts. If the endpoints disconnect, shifting an entire component preserves every observed difference and changes the query. Each of the two fixture edges is necessary to connect 0 to 55.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](Identifiable.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

The world is an arbitrary integer prefix potential. The theorem covers exact identifiability in this observation language. A disconnected result remains ambiguous; a statistical estimate needs distinct assumptions.
