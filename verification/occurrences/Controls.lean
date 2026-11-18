import SoftwareIsQuantifiable

open SoftwareIsQuantifiable

namespace OccurrenceControls

def repeated : Finiteness.Qualification Nat Nat := ⟨[0, 0, 1], [0]⟩
def correct : Finiteness.Schedule Nat Nat := [(0, 0), (1, 0), (0, 0)]
def substituted : Finiteness.Schedule Nat Nat := [(0, 0), (1, 0), (1, 0)]

example : Finiteness.Valid repeated substituted := by
  simp [Finiteness.Valid, repeated, substituted]
example : correct ∈ Finiteness.orderings repeated := by decide
example : substituted ∉ Finiteness.orderings repeated := by decide
example : [(0, 1), (0, 0), (1, 0)] ∉ Finiteness.orderings repeated := by decide

example : (Finiteness.orderings repeated).length = 3 := by decide
example : (Finiteness.alphabet repeated).length ^ repeated.runs.length = 27 := by decide
example : (Finiteness.orderings
    (⟨List.replicate 12 0, [0]⟩ : Finiteness.Qualification Nat Nat)).length = 1 := by decide
example : (12 : Nat) ^ 12 = 8916100448256 := by decide
example : (Finiteness.orderings
    (⟨[0, 1, 2], [0, 1]⟩ : Finiteness.Qualification Nat Nat)).length = 48 := by decide

example : Finiteness.combineSched correct correct ∈
    Finiteness.orderings (Finiteness.product repeated repeated) :=
  Finiteness.combine_orderings (by decide) (by decide)

def valid (w : Coverage.Witness) := decide (0 < w.events)

example : Coverage.recorded valid
    (Coverage.inScope 1 [(2, ⟨7, 1⟩)]) ⟨7⟩ = false := by decide
example : Coverage.recorded valid
    (Coverage.inScope 2 [(2, ⟨7, 1⟩)]) ⟨7⟩ = true := by decide
example : Coverage.recorded valid
    (Coverage.inScope 2 [(2, ⟨7, 0⟩)]) ⟨7⟩ = false := by decide

example : Coverage.scopedMissing (fun _ => valid)
    [(2, ⟨7, 1⟩)] [(1, ⟨7⟩)] = [(1, ⟨7⟩)] := rfl
example : Coverage.scopedMissing (fun _ => valid)
    [(2, ⟨7, 1⟩)] [(2, ⟨7⟩)] = [] := rfl
example : Coverage.scopedMissing (fun _ => valid)
    [(1, ⟨7, 1⟩), (2, ⟨8, 1⟩)] [(1, ⟨7⟩), (2, ⟨7⟩)] =
      [(2, ⟨7⟩)] := rfl
example : Coverage.scopedMissing (fun scope w => decide (w.events = scope))
    [(1, ⟨7, 1⟩), (2, ⟨7, 1⟩)] [(1, ⟨7⟩), (2, ⟨7⟩)] =
      [(2, ⟨7⟩)] := rfl

example : Coverage.missing valid (([(2, ⟨7, 1⟩)] : List (Nat × Coverage.Witness)).map Prod.snd)
    [⟨7⟩] = [] := rfl
example : ¬ Nonempty (Coverage.ScopedPlatformPremise 1 (fun _ => valid)
    [(2, ⟨7, 1⟩)] [⟨7⟩]) := by
  exact Coverage.empty_ledger_has_no_platform_premise valid [⟨7⟩] (by simp)

example : Coverage.missing valid [] [] = [] := rfl
example : Coverage.recorded valid [] ⟨7⟩ = false := rfl
example : Coverage.missing valid [⟨7, 1⟩] [⟨7⟩, ⟨7⟩] = [] := rfl

def candidate : Pareto.Bounds := ⟨8, 18, by decide⟩
def incumbent : Pareto.Bounds := ⟨10, 20, by decide⟩
def fixed : Pareto.Bounds := ⟨0, 0, by decide⟩

example : Pareto.realizes candidate fixed (18, 0) := by
  simp [Pareto.realizes, candidate, fixed]
example : Pareto.realizes incumbent fixed (10, 0) := by
  simp [Pareto.realizes, incumbent, fixed]
example : ¬ Pareto.noWorse (18, 0) (10, 0) := by decide

example : Pareto.acceptsReplacement "same" "same"
    ({ qualified := [1] } : Pareto.PriorQualification Nat)
    { offered := [1] } fixed fixed fixed fixed = true := by decide
example : ¬ Pareto.separated fixed fixed fixed fixed := by
  simp [Pareto.separated, fixed]
example : Pareto.acceptsReplacement "same" "same"
    ({ qualified := [1, 2] } : Pareto.PriorQualification Nat)
    { offered := [1] } fixed fixed fixed fixed = false := by decide

end OccurrenceControls
