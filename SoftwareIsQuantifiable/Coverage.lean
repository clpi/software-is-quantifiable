/-
  Claim 5 — Coverage universality (spec §19).

  Coverage of real executions is a platform premise. The legacy Witnessed
  predicate tests only an ID. The recorded and missing functions below
  require membership in an actual ledger and a supplied validator.
-/

namespace SoftwareIsQuantifiable
namespace Coverage

/-- An execution handle. The independently supplied roster determines
    which handles name actual executions in this qualification. -/
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

/-- The witness value names the execution; this association alone does
    not establish that the witness was recorded or validated. -/
def Witnessed (e : Execution) (w : Witness) : Prop :=
  w.exec = e.id

/-- Each result refers to a record actually present in this ledger. The caller
    supplies the evidence validator and the independently specified roster. -/
def recorded (valid : Witness → Bool) (ledger : List Witness) (e : Execution) : Bool :=
  ledger.any (fun w => valid w && decide (w.exec = e.id))

/-- The platform premise, named exactly as spec §19.4 names its
    assumptions. This is assumed, never proved, in this repository.

    * `sensorBelow`: the sensor sits strictly below the observed
      software in privilege.
    * `ledgerAppendOnly`: observed software can cause appends to
      the witness ledger, never edits or deletions.
    * `mediated`: the protection model holds — userland software
      holds no direct access to anything it affects, so every
      execution crosses the boundary and is witnessed (§19.2). -/
structure PlatformPremise (valid : Witness → Bool) (ledger : List Witness)
    (roster : List Execution) where
  /-- The sensor sits strictly below the observed software. -/
  sensorBelow : Prop
  /-- The named sensor condition holds; naming a proposition is insufficient. -/
  sensorBelowHolds : sensorBelow
  /-- The ledger is append-only from below. -/
  ledgerAppendOnly : Prop
  /-- The named append-only condition holds. -/
  ledgerAppendOnlyHolds : ledgerAppendOnly
  /-- Complete mediation of this roster through the existing validated-ledger
      checker. No constructed handle or witness substitutes for membership. -/
  mediated : ∀ e ∈ roster, recorded valid ledger e = true

/-- **Coverage, conditional on the named premise.** Under the
    mediation premise, every named execution has a validated ledger
    record. The proof is one line because there is nothing to
    prove: the entire content of the claim is the premise, and the
    premise is physical, not mathematical. -/
theorem coverage {valid : Witness → Bool} {ledger : List Witness}
    {roster : List Execution} (P : PlatformPremise valid ledger roster) :
    ∀ e ∈ roster, recorded valid ledger e = true :=
  P.mediated

/-- Coverage fails exactly when a named actual execution lacks a validated
    ledger record. An unrecorded handle outside the roster is not a counterexample. -/
theorem coverage_iff (valid : Witness → Bool) (ledger : List Witness)
    (roster : List Execution) :
    (∀ e ∈ roster, recorded valid ledger e = true) ↔
    ¬ ∃ e, e ∈ roster ∧ recorded valid ledger e = false := by
  constructor
  · intro h hex
    obtain ⟨e, he, missing⟩ := hex
    have present := h e he
    simp [present] at missing
  · intro h e he
    cases hr : recorded valid ledger e with
    | false => exact False.elim (h ⟨e, he, hr⟩)
    | true => rfl

/-- Constructing a matching record requires only the execution ID. -/
theorem unrestricted_witness (e : Execution) : ∃ w, Witnessed e w :=
  ⟨⟨e.id, 0⟩, rfl⟩

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

/-- The existing missing-roster checker is exactly the coverage obligation;
    there is no separate coverage evaluator or witness-membership model. -/
theorem coverage_missing_iff (valid : Witness → Bool) (ledger : List Witness)
    (roster : List Execution) :
    (∀ e ∈ roster, recorded valid ledger e = true) ↔
      missing valid ledger roster = [] := by
  constructor
  · intro covered
    cases hm : missing valid ledger roster with
    | nil => rfl
    | cons e rest =>
      have he : e ∈ missing valid ledger roster := by
        rw [hm]
        exact List.Mem.head _
      obtain ⟨actual, absent⟩ := (missing_exact valid ledger roster e).mp he
      exact False.elim (absent ((recorded_exact valid ledger e).mp (covered e actual)))
  · intro empty e actual
    cases hr : recorded valid ledger e with
    | true => rfl
    | false =>
      have he : e ∈ missing valid ledger roster := by
        simp [missing, List.mem_filter, actual, hr]
      rw [empty] at he
      exact nomatch he

/-- Empty actual domains have vacuous coverage, including with an empty
    ledger. Merely constructible execution handles do not change the roster. -/
theorem empty_roster_covered (valid : Witness → Bool) (ledger : List Witness) :
    ∀ e ∈ ([] : List Execution), recorded valid ledger e = true := by
  intro _ h
  exact nomatch h

/-- A nonempty actual roster cannot be mediated by an empty ledger. -/
theorem empty_ledger_has_no_platform_premise (valid : Witness → Bool)
    (roster : List Execution) (nonempty : roster ≠ []) :
    ¬ Nonempty (PlatformPremise valid [] roster) := by
  intro h
  obtain ⟨P⟩ := h
  apply nonempty
  simpa only [missing_empty] using (coverage_missing_iff valid [] roster).mp (coverage P)

#guard !recorded (fun w => decide (w.events > 0)) [⟨3, 0⟩, ⟨4, 1⟩] ⟨3⟩
#guard recorded (fun w => decide (w.events > 0)) [⟨3, 1⟩] ⟨3⟩

#print axioms recorded_exact
#print axioms missing_exact
#print axioms missing_append

/-- A successful audit covers real occurrences when the independently supplied
    manifest contains exactly the occurred executions. -/
theorem audit_complete (occurred : Execution → Prop) (valid : Witness → Bool)
    (ledger : List Witness) (roster : List Execution) (manifest : ∀ e, occurred e ↔ e ∈ roster) :
    missing valid ledger roster = [] ↔ ∀ e, occurred e → recorded valid ledger e = true := by
  rw [← coverage_missing_iff]
  simp only [manifest]

/-- Project one named scope before invoking the existing ID-based checker.
    A record for the same local ID in a different scope cannot supply evidence. -/
def inScope (scope : Nat) (rows : List (Nat × Witness)) : List Witness :=
  (rows.filter (fun row => decide (row.1 = scope))).map Prod.snd

theorem scoped_recorded_exact (scope : Nat) (rows : List (Nat × Witness))
    (valid : Witness → Bool) (e : Execution) :
    recorded valid (inScope scope rows) e = true ↔
      ∃ w, (scope,w) ∈ rows ∧ valid w = true ∧ Witnessed e w := by
  rw [recorded_exact]
  simp only [inScope,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨w,⟨⟨s,v⟩,⟨hm,rfl⟩,rfl⟩,hv,he⟩
    exact ⟨v,hm,hv,he⟩
  · rintro ⟨w,hm,hv,he⟩
    exact ⟨w,⟨(scope,w),⟨hm,rfl⟩,rfl⟩,hv,he⟩

#guard !recorded (fun _ => true) (inScope 1 [(2,⟨7,1⟩)]) ⟨7⟩
#guard recorded (fun _ => true) (inScope 2 [(2,⟨7,1⟩)]) ⟨7⟩

#print axioms audit_complete
#print axioms scoped_recorded_exact
end Coverage
end SoftwareIsQuantifiable
