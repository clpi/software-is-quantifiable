import SoftwareIsQuantifiable.Coverage

namespace LedgerRepair
open SoftwareIsQuantifiable.Coverage

-- An independent roster of shard jobs and the boundary records supplied for them.
def roster : List Execution := [⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩]
def valid (w : Witness) := decide (0 < w.events)
def old : List Witness := [⟨10,3⟩, ⟨10,3⟩, ⟨20,1⟩, ⟨30,0⟩]
def repair : List Witness := [⟨30,2⟩, ⟨40,1⟩]
def gaps (l : List Witness) := (missing valid l roster).map Execution.id

theorem before_after :
    old.length = roster.length ∧ gaps old = [30,40] ∧ gaps (old ++ repair) = [] := by decide

-- One record names one execution. No fabricated choice of event count or ID
-- makes a zero- or one-record patch cover both independent gaps.
theorem minimum_append (patch : List Witness) (covered : gaps (old ++ patch) = []) :
    repair.length ≤ patch.length := by
  change 2 ≤ patch.length
  have recordedBoth : recorded valid (old ++ patch) ⟨30⟩ = true ∧
      recorded valid (old ++ patch) ⟨40⟩ = true := by
    have hempty : missing valid (old ++ patch) roster = [] := by
      simpa [gaps] using covered
    have h := (coverage_missing_iff valid (old ++ patch) roster).mpr hempty
    exact ⟨h _ (by simp [roster]), h _ (by simp [roster])⟩
  rcases patch with _ | ⟨w, tail⟩
  · contradiction
  cases tail with
  | nil =>
    obtain ⟨a,b⟩ := recordedBoth
    rw [recorded_append] at a b
    change (false || (valid w && decide (w.exec = 30) || false)) = true at a
    change (false || (valid w && decide (w.exec = 40) || false)) = true at b
    simp at a b
    omega
  | cons v vs => simp

theorem duplicate_fails : gaps (old ++ [⟨30,2⟩, ⟨30,2⟩]) = [40] := by decide

#eval (gaps old, gaps (old ++ repair))
#print axioms before_after
#print axioms minimum_append
#print axioms duplicate_fails
end LedgerRepair
