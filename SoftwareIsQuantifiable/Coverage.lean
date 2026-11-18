/-
  Claim 5 — Coverage universality (spec §19).

  Coverage of real executions is a platform premise. The legacy Witnessed
  predicate tests only an ID. The recorded and missing functions below
  require membership in an actual ledger and a supplied validator.
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

/-- Logical dual of unrestricted existence under the legacy predicate. -/
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

/-- Constructing a matching record requires only the execution ID. -/
theorem unrestricted_witness (e : Execution) : ∃ w, Witnessed e w :=
  ⟨⟨e.id, 0⟩, rfl⟩

/-- Each result refers to a record actually present in this ledger. The caller
    supplies the evidence validator and the independently specified roster. -/
def recorded (valid : Witness → Bool) (ledger : List Witness) (e : Execution) : Bool :=
  ledger.any (fun w => valid w && decide (w.exec = e.id))

theorem recorded_exact (valid : Witness → Bool) (ledger : List Witness) (e : Execution) :
    recorded valid ledger e = true ↔ ∃ w ∈ ledger, valid w = true ∧ Witnessed e w := by
  simp [recorded, Witnessed, List.any_eq_true]

def missing (valid : Witness → Bool) (ledger : List Witness) (roster : List Execution) :=
  roster.filter (fun e => !recorded valid ledger e)

theorem missing_exact (valid : Witness → Bool) (ledger : List Witness)
    (roster : List Execution) (e : Execution) :
    e ∈ missing valid ledger roster ↔
      e ∈ roster ∧ ¬ ∃ w ∈ ledger, valid w = true ∧ Witnessed e w := by
  simp [missing, List.mem_filter, ← recorded_exact]

theorem recorded_append (valid : Witness → Bool) (left right : List Witness) (e : Execution) :
    recorded valid (left ++ right) e = (recorded valid left e || recorded valid right e) := by
  simp [recorded]

theorem missing_append (valid : Witness → Bool) (left right : List Witness)
    (roster : List Execution) (e : Execution) :
    e ∈ missing valid (left ++ right) roster ↔
      e ∈ missing valid left roster ∧ e ∈ missing valid right roster := by
  simp only [missing, List.mem_filter, Bool.not_eq_true', recorded_append,
    Bool.or_eq_false_iff]
  exact ⟨fun ⟨hr, hl, hd⟩ => ⟨⟨hr, hl⟩, hr, hd⟩,
    fun ⟨⟨hr, hl⟩, _, hd⟩ => ⟨hr, hl, hd⟩⟩

/-- An empty ledger leaves every named execution uncovered, even though
    unrestricted_witness holds for each one. -/
theorem missing_empty (valid : Witness → Bool) (roster : List Execution) :
    missing valid [] roster = roster := by simp [missing, recorded]

#guard !recorded (fun w => decide (w.events > 0)) [⟨3, 0⟩, ⟨4, 1⟩] ⟨3⟩
#guard recorded (fun w => decide (w.events > 0)) [⟨3, 1⟩] ⟨3⟩

#print axioms recorded_exact
#print axioms missing_exact
#print axioms missing_append

end Coverage
end SoftwareIsQuantifiable
