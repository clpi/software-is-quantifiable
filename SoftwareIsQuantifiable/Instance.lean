import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Finiteness
import SoftwareIsQuantifiable.Fold
import SoftwareIsQuantifiable.Coloring
import SoftwareIsQuantifiable.Pareto
import SoftwareIsQuantifiable.Coverage

/-
  A synthetic two-component command service: `gate` checks a token,
  `commit` appends to a ledger, and the path is qualified only when
  both have happened. The numbers are chosen so the theorems apply.
  They are not measurements of a deployed system.

  What the instance checks, by applying the general theorems:

  * the schedule space is finite and the valid schedules are exactly
    the computed enumerator;
  * witness accounts of the two components compose by tagging;
  * coloring the components separately misses the cross-component
    fact `committed`, while closing the joined seed records it, and
    the compounding identity still holds;
  * separated component bounds stay separated when the path runs
    them in sequence;
  * dropping a required behavior rejects a candidate the cost order
    would otherwise prefer;
  * a ledger that covers each component's named requests covers the
    path, and a missing request is not covered.
-/

namespace SoftwareIsQuantifiable
namespace Instance

inductive Run where
  | check
  | append
  deriving DecidableEq, Repr

inductive Venue where
  | edge
  | core
  deriving DecidableEq, Repr

def service : Finiteness.Qualification Run Venue where
  runs := [.check, .append]
  venues := [.edge, .core]

/-- 2 runs × 2 venues is an alphabet of 4, and schedules of length 2
    number `4 ^ 2`. -/
theorem service_schedule_card :
    (Finiteness.listsOfLen (Finiteness.alphabet service) service.runs.length).length = 16 := by
  decide

/-- Eight of those sixteen schedules name both runs. -/
theorem service_valid_count :
    (Finiteness.validSchedules service).length = 8 := by
  decide

def pathSchedule : Finiteness.Schedule Run Venue :=
  [(.check, .edge), (.append, .core)]

theorem pathSchedule_valid : Finiteness.Valid service pathSchedule :=
  Finiteness.validB_iff.mp (by decide)

def gateWitnesses : List Nat := [11, 12]

def commitWitnesses : List Nat := [21]

theorem accounts_compose :
    Fold.account (gateWitnesses.map (@Sum.inl Nat Nat) ++
        commitWitnesses.map (@Sum.inr Nat Nat)) =
      Fold.embedAcct (Fold.account gateWitnesses) (Fold.account commitWitnesses) :=
  Fold.account_sum gateWitnesses commitWitnesses

theorem duplicate_witness_free :
    Fold.account (11 :: gateWitnesses) = Fold.account gateWitnesses :=
  Fold.account_cons_self 11 gateWitnesses (by simp [gateWitnesses])

inductive Fact where
  | tokenChecked
  | signatureValid
  | authzOk
  | entryHashed
  | committed
  deriving DecidableEq, Repr

open Coloring

def gateRule : Rule Fact where
  premises := [.tokenChecked, .signatureValid]
  conclusion := .authzOk

def crossRule : Rule Fact where
  premises := [.authzOk, .entryHashed]
  conclusion := .committed

def pathRules : List (Rule Fact) := [gateRule, crossRule]

def pathUniverse : List Fact :=
  [.tokenChecked, .signatureValid, .authzOk, .entryHashed, .committed]

def gateSeed : State Fact :=
  fun f => decide (f = .tokenChecked) || decide (f = .signatureValid)

def commitSeed : State Fact :=
  fun f => decide (f = .entryHashed)

theorem path_universe_closed : ∀ r ∈ pathRules, r.conclusion ∈ pathUniverse := by
  intro r hr
  simp [pathRules] at hr
  rcases hr with rfl | rfl
  · simp [gateRule, pathUniverse]
  · simp [crossRule, pathUniverse]

theorem gate_misses_committed :
    coloring pathRules pathUniverse gateSeed .committed = false := by
  decide

theorem commit_misses_committed :
    coloring pathRules pathUniverse commitSeed .committed = false := by
  decide

theorem joint_colors_committed :
    coloring pathRules pathUniverse (joinSt gateSeed commitSeed) .committed = true := by
  decide

/-- Separate colorings miss `committed`. Closing the joined seed
    records it. Distribution of coloring over join is false for this
    path; compounding (`service_compounds`) is the identity that holds.
    The booleans are kernel-reduced by `decide`. -/
theorem not_coloring_distributes_on_path :
    joinSt (coloring pathRules pathUniverse gateSeed)
        (coloring pathRules pathUniverse commitSeed) .committed = false ∧
      coloring pathRules pathUniverse (joinSt gateSeed commitSeed) .committed = true := by
  exact ⟨by decide, by decide⟩

theorem service_compounds :
    coloring pathRules pathUniverse (joinSt gateSeed commitSeed) =
      coloring pathRules pathUniverse
        (joinSt (coloring pathRules pathUniverse gateSeed)
          (coloring pathRules pathUniverse commitSeed)) :=
  coloring_compound pathRules pathUniverse gateSeed commitSeed path_universe_closed

def gateTimeCand : Pareto.Bounds where
  lo := 1
  hi := 2
  valid := by decide

def gateTimeInc : Pareto.Bounds where
  lo := 4
  hi := 6
  valid := by decide

def gateComputeCand : Pareto.Bounds where
  lo := 1
  hi := 1
  valid := by decide

def gateComputeInc : Pareto.Bounds where
  lo := 1
  hi := 2
  valid := by decide

def commitTimeCand : Pareto.Bounds where
  lo := 1
  hi := 2
  valid := by decide

def commitTimeInc : Pareto.Bounds where
  lo := 3
  hi := 5
  valid := by decide

def commitComputeCand : Pareto.Bounds where
  lo := 2
  hi := 2
  valid := by decide

def commitComputeInc : Pareto.Bounds where
  lo := 2
  hi := 4
  valid := by decide

theorem gate_separated :
    Pareto.separated gateTimeCand gateComputeCand gateTimeInc gateComputeInc := by
  refine ⟨by decide, by decide, Or.inl (by decide)⟩

theorem commit_separated :
    Pareto.separated commitTimeCand commitComputeCand commitTimeInc commitComputeInc := by
  refine ⟨by decide, by decide, Or.inl (by decide)⟩

/-- The path runs gate then commit. Separation of each component
    yields separation of the sums. -/
theorem path_separated :
    Pareto.separated
      (Pareto.addBounds gateTimeCand commitTimeCand)
      (Pareto.addBounds gateComputeCand commitComputeCand)
      (Pareto.addBounds gateTimeInc commitTimeInc)
      (Pareto.addBounds gateComputeInc commitComputeInc) :=
  Pareto.separated_sum gate_separated commit_separated

/-- Three deployments of the path. `(2, 2)` is undominated and is not
    the optimum of any positive weighted sum (`Pareto.not_scalarized`). -/
def deployments : List Pareto.Point := [(0, 3), (2, 2), (3, 0)]

theorem deployments_frontier :
    Pareto.frontier deployments = deployments := by
  decide

inductive Behavior where
  | denyMissing
  | allowValid
  | appendDurable
  | noSilentDrop
  deriving DecidableEq, Repr

def priorBehaviors : Pareto.PriorQualification Behavior where
  qualified := [.denyMissing, .allowValid, .appendDurable, .noSilentDrop]

def trimmedSubmission : Pareto.BehaviorSubmission Behavior where
  offered := [.denyMissing, .allowValid, .appendDurable]

def emptySubmission : Pareto.BehaviorSubmission Behavior where
  offered := []

def fullSubmission : Pareto.BehaviorSubmission Behavior where
  offered := [.denyMissing, .allowValid, .appendDurable, .noSilentDrop]

theorem trimmed_rejected :
    Pareto.noQualifiedBehaviorLost priorBehaviors trimmedSubmission = false := by
  decide

theorem empty_submission_rejected :
    Pareto.noQualifiedBehaviorLost priorBehaviors emptySubmission = false := by
  decide

theorem full_kept :
    Pareto.noQualifiedBehaviorLost priorBehaviors fullSubmission = true := by
  decide

inductive AxisId where
  | latency
  | memory
  deriving DecidableEq, Repr

def pathSpace : Interface.MeasureSpace AxisId :=
  [{ measure := .latency, polarity := .minimize },
   { measure := .memory, polarity := .minimize }]

def fastDrop : Interface.Profile Unit AxisId where
  symbol := ()
  readings := [0, 0]
  observed := false

def steady : Interface.Profile Unit AxisId where
  symbol := ()
  readings := [2, 2]
  observed := true

/-- A strictly better cost vector that drops observed behavior is not
    `noWorse`. The regression gate is not implied by the cost order. -/
theorem cost_does_not_excuse_behavior_drop :
    Interface.measuresLe pathSpace fastDrop steady ∧
      ¬ Interface.noWorse pathSpace fastDrop steady := by
  refine ⟨⟨rfl, ⟨Nat.zero_le _, ⟨Nat.zero_le _, trivial⟩⟩⟩, ?_⟩
  intro h
  have hobs : fastDrop.observed = true := h.2 rfl
  cases hobs

def validWitness (w : Coverage.Witness) : Bool :=
  decide (w.events > 0)

theorem request_two_uncovered :
    Coverage.recorded validWitness [{ exec := 1, events := 4 }] { id := 2 } = false := by
  decide

theorem path_requests_covered :
    let ledger := ([{ exec := 1, events := 2 }] ++ [{ exec := 2, events := 3 }])
    Coverage.recorded validWitness ledger { id := 1 } = true ∧
      Coverage.recorded validWitness ledger { id := 2 } = true := by
  decide

end Instance
end SoftwareIsQuantifiable
