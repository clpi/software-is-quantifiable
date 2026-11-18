/-
  Claim 5 — Coverage universality (spec §19).

  Status: PREMISE. The spec itself states this claim as an argument
  at the level of the protection model, standing on three named
  assumptions (§19.4), with an exact falsification condition (§19.5).
  It is not a theorem of the mathematics, and this module does not
  pretend otherwise: the mediation premise appears as an explicitly
  named field of `PlatformPremise`, every coverage statement takes
  that premise as an argument, and no theorem in this repository
  derives coverage without it. The Lean content is the dependency
  discipline itself — the premise cannot be smuggled, because the
  type of every coverage theorem names it.
-/

namespace SoftwareIsQuantifiable
namespace Coverage

/-- An execution of arbitrary software, in any language, on any
    platform. The mathematics sees only an opaque handle; everything
    about an execution that matters here is whether it is witnessed. -/
structure Execution where
  /-- An opaque identity for the execution. -/
  id : Nat

/-- A boundary witness: a record, made at the platform boundary,
    of one execution. -/
structure Witness where
  /-- The execution this witness records. -/
  exec : Nat
  /-- The boundary events observed, as a count at the finest grain
      the platform affords (process lifecycle, syscall stream). -/
  events : Nat

/-- The witness records the execution. -/
def Witnessed (e : Execution) (w : Witness) : Prop :=
  w.exec = e.id

/-- The platform premise, named exactly as spec §19.4 names its
    assumptions. This is assumed, never proved, in this repository.

    * `sensorBelow`: the sensor sits strictly below the observed
      software in privilege.
    * `ledgerAppendOnly`: observed software can cause appends to
      the witness ledger, never edits or deletions.
    * `mediated`: the protection model holds — userland software
      holds no direct access to anything it affects, so every
      execution crosses the boundary and is witnessed (§19.2). -/
structure PlatformPremise where
  /-- The sensor sits strictly below the observed software. -/
  sensorBelow : Prop
  /-- The ledger is append-only from below. -/
  ledgerAppendOnly : Prop
  /-- Complete mediation: every execution is witnessed. -/
  mediated : ∀ e : Execution, ∃ w : Witness, Witnessed e w

/-- **Coverage, conditional on the named premise.** Under the
    mediation premise, every execution of arbitrary software is
    witnessed. The proof is one line because there is nothing to
    prove: the entire content of the claim is the premise, and the
    premise is physical, not mathematical. -/
theorem coverage (P : PlatformPremise) :
    ∀ e : Execution, ∃ w : Witness, Witnessed e w :=
  P.mediated

/-- The falsification condition (§19.5), stated exactly: coverage
    fails if and only if some execution is unwitnessed. Exhibiting
    one such execution on a named platform falsifies the premise
    for that platform — and, per the spec, nothing else. -/
theorem coverage_iff (P : PlatformPremise) :
    (∀ e : Execution, ∃ w : Witness, Witnessed e w) ↔
    ¬ ∃ e : Execution, ∀ w : Witness, ¬ Witnessed e w := by
  constructor
  · intro h hex
    cases hex with
    | intro e he =>
      cases h e with
      | intro w hw => exact he w hw
  · intro h e
    exact Classical.byContradiction
      (fun hne => h ⟨e, fun w hw => hne ⟨w, hw⟩⟩)

/-- Bare existence of a `Witness` whose `exec` field equals an
    execution id. This is a theorem, and it is not a discharge of
    §19: `Witness` is an unconstrained pair of naturals, so the pair
    can be built with no sensor and no ledger. `coverage` still takes
    `PlatformPremise`. Ledger membership below is the claim that
    stays a premise. -/
theorem unconstrained_witness_exists (e : Execution) :
    ∃ w : Witness, Witnessed e w :=
  ⟨{ exec := e.id, events := 0 }, rfl⟩

/-- A named ledger: the witnesses a platform actually recorded. -/
structure Ledger where
  records : List Witness

def ledgerWitnessed (L : Ledger) (e : Execution) : Prop :=
  ∃ w ∈ L.records, Witnessed e w

/-- Ledger coverage of every execution. This is the mediation claim
    with a bite: membership in a supplied ledger, not existence of a
    pair of naturals. It is assumed, never proved. -/
def LedgerPremise (L : Ledger) : Prop :=
  ∀ e : Execution, ledgerWitnessed L e

/-- An empty ledger covers nothing. Universality is not a theorem. -/
theorem not_ledger_coverage_empty :
    ¬ ledgerWitnessed { records := [] } { id := 0 } := by
  intro h
  rcases h with ⟨_, hw, _⟩
  cases hw

/-- Sensor-below and append-only do not yield ledger coverage.
    Both flags can hold (`True`) while the ledger misses an execution. -/
theorem not_ledger_from_placement :
    ¬ ∀ (sensorBelow ledgerAppendOnly : Prop) (L : Ledger),
        sensorBelow → ledgerAppendOnly → LedgerPremise L := by
  intro h
  exact not_ledger_coverage_empty
    ((h True True { records := [] } trivial trivial) { id := 0 })

def appendLedger (L1 L2 : Ledger) : Ledger where
  records := L1.records ++ L2.records

/-- **Composition of named coverage.** If each component's ledger
    covers that component's named executions, the appended ledger
    covers the concatenated execution list. This does not produce
    `LedgerPremise` for every `Execution`; that remains a premise. -/
theorem ledger_coverage_compose {E1 E2 : List Execution} {L1 L2 : Ledger}
    (h1 : ∀ e ∈ E1, ledgerWitnessed L1 e)
    (h2 : ∀ e ∈ E2, ledgerWitnessed L2 e) :
    ∀ e ∈ E1 ++ E2, ledgerWitnessed (appendLedger L1 L2) e := by
  intro e he
  cases List.mem_append.mp he with
  | inl hl =>
    rcases h1 e hl with ⟨w, hw, hww⟩
    exact ⟨w, List.mem_append_left _ hw, hww⟩
  | inr hr =>
    rcases h2 e hr with ⟨w, hw, hww⟩
    exact ⟨w, List.mem_append_right _ hw, hww⟩

end Coverage
end SoftwareIsQuantifiable
