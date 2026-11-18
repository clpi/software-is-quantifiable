# Scoped coverage and interval admission verification

This directory preserves the completed verification of the combined source
based on `ba27febf48c85bccaaccbace7cc3faba5eff879c`. The exact compiled files and
their SHA-256 digests are listed in [record.json](record.json). Its SHA-256 is
`00f1fd053ed532a520420d1afeae9284f47d7ebb747df09f0f9684b21c6b9d01`.

The record retains the original commands, absolute paths, timestamps, exit
codes, and stdout/stderr hashes. Paths describe the recorded run; moving the
logs into this repository does not relabel it as a later execution.

## Results

- Clean `lake --wfail build`: exit 0, no warnings.
- Upstream `verification/ParetoControls.lean`: exit 0; eight executable guards
  and four proof controls retained unchanged.
- All 68 declared theorems audited through `#print axioms`: exit 0. Dependencies
  are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- Four damaged-definition controls: each rejected with exit 1 and a proof
  error. They fabricate recorded coverage, bypass witness validation, remove
  the compute-cost check from the shared release gate, or remove behavior
  inclusion from that gate.

The controls are generated from the checked source by the replayer; full
source copies are not stored here. [Axioms.lean](Axioms.lean) contains the
audited theorem inventory. Every command's stdout and stderr is preserved,
including empty stderr files.

## Reproduction

Use the complete official Lean 4.15.0 Linux toolchain, compiler commit
`11651562caae`. The recorded executable SHA-256 is
`eacf754d25ae86ea076882a34b9444f2485659d9df4266b821443b28ca95a215`.

```sh
python3 verification/coverage/verify.py \
  --toolchain-bin /path/to/lean-4.15.0-linux/bin \
  --output /tmp/quantifiable-coverage-replay
```

The portable replayer runs the recorded verification sequence, first checking
the source digests and compiler version against the committed subject. It
writes a fresh receipt and logs to the separate output directory, retaining
the committed evidence unchanged. The replay checks the current sources against the pinned source manifest in `subject.json`.

This evidence checks the formal source and its stated premises. Actual
roster membership, witness authenticity, behavior interpretation,
and physical measurement validity remain the explicit input obligations of
the model.
