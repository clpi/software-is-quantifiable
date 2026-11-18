/-
  Claim 1 — Finiteness (spec §20.0, the presentation lemma).

  A qualification is a finite presentation: a named artifact, a finite
  spec, a finite set of criteria, a finite set of named venues. Nothing
  else can be a qualification. In this formalization the presentation
  *is* lists — runs and venues are given as `List`s — so the problem
  space is finite by construction: below we exhibit, for any
  qualification, an explicit finite list that enumerates every
  schedule over it. Finiteness is a theorem about the definitions,
  never a hypothesis added to them.
-/

namespace SoftwareIsQuantifiable
namespace Finiteness

/-- A qualification: the finite presentation itself. The runs and the
    venues a qualification names are lists — there is no other way to
    present them, and no qualification exists before the naming. -/
structure Qualification (Run Venue : Type) where
  /-- The named runs of the qualification. -/
  runs : List Run
  /-- The named venues of the qualification. -/
  venues : List Venue

/-- A schedule over a qualification: a finite sequence of run–venue
    steps. -/
abbrev Schedule (Run Venue : Type) := List (Run × Venue)

/-- Every list of length exactly `n` over the alphabet `A`, enumerated. -/
def listsOfLen : List α → Nat → List (List α)
  | _, 0 => [[]]
  | A, n + 1 => (listsOfLen A n).flatMap (fun l => A.map (fun a => a :: l))

theorem mem_listsOfLen {A : List α} :
    ∀ {n : Nat} {l : List α},
      l ∈ listsOfLen A n ↔ l.length = n ∧ ∀ x ∈ l, x ∈ A := by
  intro n
  induction n with
  | zero =>
    intro l
    show (l ∈ [[]]) ↔ l.length = 0 ∧ ∀ x ∈ l, x ∈ A
    rw [List.mem_singleton]
    constructor
    · intro h
      subst h
      refine ⟨rfl, ?_⟩
      intro x hx
      cases hx
    · intro h
      cases l with
      | nil => rfl
      | cons a t => simp at h
  | succ n IH =>
    intro l
    constructor
    · intro h
      simp only [listsOfLen, List.mem_flatMap, List.mem_map] at h
      obtain ⟨l', hl', a, ha, rfl⟩ := h
      have IH' := IH.mp hl'
      refine ⟨by simp [IH'.1], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact IH'.2 x hx
    · intro h
      obtain ⟨hlen, hmem⟩ := h
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        have hl' : l'.length = n := by simpa using hlen
        have ha : a ∈ A := hmem a (by simp)
        have htail : ∀ x ∈ l', x ∈ A := fun x hx => hmem x (by simp [hx])
        have hmem' : l' ∈ listsOfLen A n := IH.mpr ⟨hl', htail⟩
        simp only [listsOfLen, List.mem_flatMap, List.mem_map]
        exact ⟨l', hmem', a, ha, rfl⟩

/-- The run–venue alphabet of a qualification, enumerated. -/
def alphabet (q : Qualification Run Venue) : List (Run × Venue) :=
  q.runs.flatMap (fun r => q.venues.map (fun v => (r, v)))

theorem mem_alphabet {q : Qualification Run Venue} {p : Run × Venue} :
    p ∈ alphabet q ↔ p.1 ∈ q.runs ∧ p.2 ∈ q.venues := by
  obtain ⟨r, v⟩ := p
  simp [alphabet]

/-- **Finiteness of the problem space.** For every qualification there
    is a finite list enumerating every schedule over it: every list of
    steps whose length is the run count and whose steps draw runs and
    venues from the presentation. The enumeration exists by
    construction from the presentation's own lists. -/
theorem schedules_finite (q : Qualification Run Venue) :
    ∃ L : List (Schedule Run Venue), ∀ s : Schedule Run Venue,
      s.length = q.runs.length →
      (∀ p ∈ s, p.1 ∈ q.runs ∧ p.2 ∈ q.venues) → s ∈ L := by
  refine ⟨listsOfLen (alphabet q) q.runs.length, fun s hlen hsteps => ?_⟩
  rw [mem_listsOfLen]
  refine ⟨hlen, fun p hp => ?_⟩
  rw [mem_alphabet]
  exact hsteps p hp

/-- A schedule is valid when it has one step per run, draws every step
    from the presentation, and covers every named run. -/
def Valid (q : Qualification Run Venue) (s : Schedule Run Venue) : Prop :=
  s.length = q.runs.length ∧
  (∀ p ∈ s, p.1 ∈ q.runs ∧ p.2 ∈ q.venues) ∧
  (∀ r ∈ q.runs, ∃ v ∈ q.venues, (r, v) ∈ s)

/-- **Finiteness of the valid orderings** (spec §20.1: "the set of
    valid orderings is finite"). The valid orderings are a
    subcollection of an explicitly enumerated finite list. -/
theorem valid_orderings_finite (q : Qualification Run Venue) :
    ∃ L : List (Schedule Run Venue), ∀ s : Schedule Run Venue,
      Valid q s → s ∈ L := by
  obtain ⟨L, hL⟩ := schedules_finite q
  exact ⟨L, fun s hs => hL s hs.1 hs.2.1⟩

end Finiteness
end SoftwareIsQuantifiable
