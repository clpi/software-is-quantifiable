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

/-- Length of a `flatMap` whose every image has the same length. -/
theorem length_flatMap_const {α β : Type _} (n : Nat) (l : List α) (f : α → List β)
    (h : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp [List.flatMap_nil]
  | cons a l IH =>
    have ha : (f a).length = n := h a List.mem_cons_self
    have htail : ∀ x ∈ l, (f x).length = n :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, List.length_append, IH htail, ha, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The enumerator has size `|A| ^ n`, counting duplicate entries of `A`. -/
theorem listsOfLen_length (A : List α) :
    ∀ n, (listsOfLen A n).length = A.length ^ n := by
  intro n
  induction n with
  | zero => simp [listsOfLen]
  | succ n IH =>
    have hEq : listsOfLen A (n + 1) =
        (listsOfLen A n).flatMap (fun l => List.map (fun a => a :: l) A) := rfl
    have hlen :=
      length_flatMap_const A.length (listsOfLen A n)
        (fun l => List.map (fun a => a :: l) A)
        (fun _ _ => by rw [List.length_map])
    rw [hEq, hlen, IH, ← Nat.pow_add_one]

/-- **Cardinality of the schedule space.** The explicit enumerator of
    length-`|runs|` schedules over the qualification's alphabet has
    size `|alphabet| ^ |runs|`. -/
theorem schedules_card (q : Qualification Run Venue) :
    (listsOfLen (alphabet q) q.runs.length).length =
      (alphabet q).length ^ q.runs.length :=
  listsOfLen_length (alphabet q) q.runs.length

section Executable
variable {Run Venue : Type} [DecidableEq Run] [DecidableEq Venue]

/-- Decidable form of `Valid`. -/
def validB (q : Qualification Run Venue) (s : Schedule Run Venue) : Bool :=
  decide (s.length = q.runs.length) &&
    s.all (fun p => decide (p.1 ∈ q.runs) && decide (p.2 ∈ q.venues)) &&
    q.runs.all (fun r => q.venues.any (fun v => decide ((r, v) ∈ s)))

theorem validB_iff {q : Qualification Run Venue} {s : Schedule Run Venue} :
    validB q s = true ↔ Valid q s := by
  simp only [validB, Bool.and_eq_true_iff, decide_eq_true_iff,
    List.all_eq_true, List.any_eq_true, Valid]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The valid schedules, as a computed sublist of the finite enumerator. -/
def validSchedules (q : Qualification Run Venue) : List (Schedule Run Venue) :=
  (listsOfLen (alphabet q) q.runs.length).filter (fun s => validB q s)

/-- **The enumerator is exact.** A schedule is valid if and only if it
    occurs in `validSchedules`. -/
theorem mem_validSchedules {q : Qualification Run Venue} {s : Schedule Run Venue} :
    s ∈ validSchedules q ↔ Valid q s := by
  constructor
  · intro h
    exact validB_iff.mp (List.mem_filter.mp h).2
  · intro hv
    apply List.mem_filter.mpr
    refine ⟨?_, validB_iff.mpr hv⟩
    rw [mem_listsOfLen]
    exact ⟨hv.1, fun p hp => mem_alphabet.mpr (hv.2.1 p hp)⟩

/-- There are at most `|alphabet| ^ |runs|` valid schedules. -/
theorem validSchedules_length_le (q : Qualification Run Venue) :
    (validSchedules q).length ≤ (alphabet q).length ^ q.runs.length := by
  unfold validSchedules
  rw [← schedules_card q]
  exact List.length_filter_le _ _

end Executable

/-- The product of two qualifications: runs and venues are tagged by
    which component they come from. -/
def product {R1 V1 R2 V2 : Type}
    (q1 : Qualification R1 V1) (q2 : Qualification R2 V2) :
    Qualification (R1 ⊕ R2) (V1 ⊕ V2) where
  runs := q1.runs.map Sum.inl ++ q2.runs.map Sum.inr
  venues := q1.venues.map Sum.inl ++ q2.venues.map Sum.inr

def tagLeft {R1 V1 R2 V2 : Type} (s : Schedule R1 V1) :
    Schedule (R1 ⊕ R2) (V1 ⊕ V2) :=
  s.map (fun p => (Sum.inl p.1, Sum.inl p.2))

def tagRight {R1 V1 R2 V2 : Type} (s : Schedule R2 V2) :
    Schedule (R1 ⊕ R2) (V1 ⊕ V2) :=
  s.map (fun p => (Sum.inr p.1, Sum.inr p.2))

/-- Side-respecting concatenation of a schedule from each component. -/
def combineSched {R1 V1 R2 V2 : Type}
    (s1 : Schedule R1 V1) (s2 : Schedule R2 V2) :
    Schedule (R1 ⊕ R2) (V1 ⊕ V2) :=
  tagLeft s1 ++ tagRight s2

/-- **Closure under composition.** Valid schedules of the components
    combine to a valid schedule of the product qualification. -/
theorem combine_valid {R1 V1 R2 V2 : Type}
    {q1 : Qualification R1 V1} {q2 : Qualification R2 V2}
    {s1 : Schedule R1 V1} {s2 : Schedule R2 V2}
    (h1 : Valid q1 s1) (h2 : Valid q2 s2) :
    Valid (product q1 q2) (combineSched s1 s2) := by
  obtain ⟨len1, steps1, cov1⟩ := h1
  obtain ⟨len2, steps2, cov2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · simp [combineSched, tagLeft, tagRight, product, len1, len2]
  · intro p hp
    rw [combineSched, List.mem_append] at hp
    cases hp with
    | inl hl =>
      rcases List.mem_map.mp hl with ⟨p1, hp1, rfl⟩
      have hs := steps1 p1 hp1
      refine ⟨?_, ?_⟩
      · simpa [product] using
          (List.mem_append_left _ (List.mem_map_of_mem hs.1) :
            Sum.inl p1.1 ∈ q1.runs.map Sum.inl ++ q2.runs.map Sum.inr)
      · simpa [product] using
          (List.mem_append_left _ (List.mem_map_of_mem hs.2) :
            Sum.inl p1.2 ∈ q1.venues.map Sum.inl ++ q2.venues.map Sum.inr)
    | inr hr =>
      rcases List.mem_map.mp hr with ⟨p2, hp2, rfl⟩
      have hs := steps2 p2 hp2
      refine ⟨?_, ?_⟩
      · simpa [product] using
          (List.mem_append_right _ (List.mem_map_of_mem hs.1) :
            Sum.inr p2.1 ∈ q1.runs.map Sum.inl ++ q2.runs.map Sum.inr)
      · simpa [product] using
          (List.mem_append_right _ (List.mem_map_of_mem hs.2) :
            Sum.inr p2.2 ∈ q1.venues.map Sum.inl ++ q2.venues.map Sum.inr)
  · intro r hr
    simp [product, List.mem_append, List.mem_map] at hr
    cases hr with
    | inl hex =>
      rcases hex with ⟨r1, hr1, rfl⟩
      obtain ⟨v, hv, hstep⟩ := cov1 r1 hr1
      refine ⟨Sum.inl v, ?_, ?_⟩
      · simpa [product] using
          (List.mem_append_left _ (List.mem_map_of_mem hv) :
            Sum.inl v ∈ q1.venues.map Sum.inl ++ q2.venues.map Sum.inr)
      · simpa [combineSched, tagLeft] using
          (List.mem_append_left _ (List.mem_map_of_mem hstep) :
            (Sum.inl r1, Sum.inl v) ∈ tagLeft s1 ++ tagRight s2)
    | inr hex =>
      rcases hex with ⟨r2, hr2, rfl⟩
      obtain ⟨v, hv, hstep⟩ := cov2 r2 hr2
      refine ⟨Sum.inr v, ?_, ?_⟩
      · simpa [product] using
          (List.mem_append_right _ (List.mem_map_of_mem hv) :
            Sum.inr v ∈ q1.venues.map Sum.inl ++ q2.venues.map Sum.inr)
      · simpa [combineSched, tagRight] using
          (List.mem_append_right _ (List.mem_map_of_mem hstep) :
            (Sum.inr r2, Sum.inr v) ∈ tagLeft s1 ++ tagRight s2)

/-- A schedule stays on the component it drew its run from. -/
def sideRespecting {R1 V1 R2 V2 : Type}
    (s : Schedule (R1 ⊕ R2) (V1 ⊕ V2)) : Prop :=
  ∀ p ∈ s,
    (∃ r v, p = (Sum.inl r, Sum.inl v)) ∨ (∃ r v, p = (Sum.inr r, Sum.inr v))

/-- **Not every valid product schedule is a component composition.**
    `Valid` on the product presentation allows a run of one component
    to be wired to a venue of the other. Composition is `combineSched`,
    the side-respecting subcollection, not the whole valid set. -/
theorem not_all_valid_side_respecting :
    ∃ s : Schedule (Unit ⊕ Unit) (Unit ⊕ Unit),
      Valid (product
          ({ runs := [()], venues := [()] } : Qualification Unit Unit)
          ({ runs := [()], venues := [()] } : Qualification Unit Unit)) s ∧
        ¬ sideRespecting s := by
  let q1 : Qualification Unit Unit := { runs := [()], venues := [()] }
  let q2 : Qualification Unit Unit := { runs := [()], venues := [()] }
  let s : Schedule (Unit ⊕ Unit) (Unit ⊕ Unit) :=
    [(Sum.inl (), Sum.inr ()), (Sum.inr (), Sum.inl ())]
  refine ⟨s, ⟨?len, ?steps, ?cov⟩, ?bad⟩
  case len =>
    simp [product, q1, q2, s]
  case steps =>
    intro p hp
    simp [s] at hp
    cases hp with
    | inl he =>
      cases he
      simp [product, q1, q2]
    | inr he =>
      cases he
      simp [product, q1, q2]
  case cov =>
    intro r hr
    simp [product, q1, q2] at hr
    cases hr with
    | inl he =>
      cases he
      exact ⟨Sum.inr (), by simp [product, q1, q2], by simp [s]⟩
    | inr he =>
      cases he
      exact ⟨Sum.inl (), by simp [product, q1, q2], by simp [s]⟩
  case bad =>
    intro h
    have hstep := h (Sum.inl (), Sum.inr ()) (by simp [s])
    cases hstep with
    | inl hex =>
      rcases hex with ⟨_, _, he⟩
      cases he
    | inr hex =>
      rcases hex with ⟨_, _, he⟩
      cases he

/-- Every side-respecting composite of two schedule lists. -/
def composites {R1 V1 R2 V2 : Type}
    (L1 : List (Schedule R1 V1)) (L2 : List (Schedule R2 V2)) :
    List (Schedule (R1 ⊕ R2) (V1 ⊕ V2)) :=
  L1.flatMap (fun s1 => L2.map (fun s2 => combineSched s1 s2))

theorem mem_composites {R1 V1 R2 V2 : Type}
    {L1 : List (Schedule R1 V1)} {L2 : List (Schedule R2 V2)}
    {z : Schedule (R1 ⊕ R2) (V1 ⊕ V2)} :
    z ∈ composites L1 L2 ↔ ∃ s1, s1 ∈ L1 ∧ ∃ s2, s2 ∈ L2 ∧ z = combineSched s1 s2 := by
  simp only [composites, List.mem_flatMap, List.mem_map]
  constructor
  · intro h
    rcases h with ⟨s1, hs1, s2, hs2, he⟩
    exact ⟨s1, hs1, s2, hs2, he.symm⟩
  · intro h
    rcases h with ⟨s1, hs1, s2, hs2, he⟩
    exact ⟨s1, hs1, s2, hs2, he.symm⟩

/-- A schedule preserving the multiplicity of every run value and assigning
    each entry an allowed venue. Distinct invocations require distinct run
    identities at ingress; repeated equal values carry no separate lineage. -/
def orderings [DecidableEq Run] [DecidableEq Venue] (q : Qualification Run Venue) :=
  (listsOfLen (alphabet q) q.runs.length).filter
    (fun s => decide ((s.map Prod.fst).Perm q.runs))

theorem orderings_exact [DecidableEq Run] [DecidableEq Venue]
    (q : Qualification Run Venue) (s : Schedule Run Venue) :
    s ∈ orderings q ↔ (s.map Prod.fst).Perm q.runs ∧ ∀ p ∈ s, p.2 ∈ q.venues := by
  simp only [orderings, List.mem_filter, decide_eq_true_eq, mem_listsOfLen]
  constructor
  · rintro ⟨⟨_,h⟩,perm⟩
    exact ⟨perm,fun p hp => (mem_alphabet.mp (h p hp)).2⟩
  · rintro ⟨perm,venues⟩
    refine ⟨⟨by simpa using perm.length_eq, ?_⟩,perm⟩
    intro p hp
    exact mem_alphabet.mpr ⟨perm.mem_iff.mp (List.mem_map.mpr ⟨p,hp,rfl⟩),venues p hp⟩

/-- Multiplicity-preserving schedules refine the existing distinct-name
    coverage contract, so old consumers can use the stronger producer. -/
theorem orderings_valid [DecidableEq Run] [DecidableEq Venue]
    {q : Qualification Run Venue} {s : Schedule Run Venue}
    (hs : s ∈ orderings q) : Valid q s := by
  obtain ⟨perm, venues⟩ := (orderings_exact q s).mp hs
  refine ⟨by simpa using perm.length_eq, ?_, ?_⟩
  · intro p hp
    exact ⟨perm.mem_iff.mp (List.mem_map.mpr ⟨p, hp, rfl⟩), venues p hp⟩
  · intro r hr
    rcases List.mem_map.mp (perm.mem_iff.mpr hr) with ⟨⟨r', v⟩, hp, he⟩
    cases he
    exact ⟨v, venues (r', v) hp, hp⟩

/-- The existing tagged composition preserves multiplicity on both sides. -/
theorem combine_orderings {R1 V1 R2 V2 : Type}
    [DecidableEq R1] [DecidableEq V1] [DecidableEq R2] [DecidableEq V2]
    {q1 : Qualification R1 V1} {q2 : Qualification R2 V2}
    {s1 : Schedule R1 V1} {s2 : Schedule R2 V2}
    (h1 : s1 ∈ orderings q1) (h2 : s2 ∈ orderings q2) :
    combineSched s1 s2 ∈ orderings (product q1 q2) := by
  apply (orderings_exact _ _).mpr
  have p1 := ((orderings_exact q1 s1).mp h1).1
  have p2 := ((orderings_exact q2 s2).mp h2).1
  refine ⟨?_, ?_⟩
  · simpa [combineSched, tagLeft, tagRight, product, List.map_map,
      Function.comp_def] using (p1.map Sum.inl).append (p2.map Sum.inr)
  · intro p hp
    exact ((combine_valid (orderings_valid h1) (orderings_valid h2)).2.1 p hp).2

private def repeated : Qualification Nat Nat := ⟨[0,0,1],[0]⟩
private def wrongMultiplicity : Schedule Nat Nat := [(0,0),(1,0),(1,0)]
example : Valid repeated wrongMultiplicity := by
  simp [Valid,repeated,wrongMultiplicity]
example : wrongMultiplicity ∉ orderings repeated := by decide

#print axioms orderings_exact
#print axioms orderings_valid
#print axioms combine_orderings
end Finiteness
end SoftwareIsQuantifiable
