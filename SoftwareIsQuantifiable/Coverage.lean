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

end Coverage
end SoftwareIsQuantifiable
