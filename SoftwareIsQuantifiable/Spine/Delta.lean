/-
  The update and checker spine: the delta group, obligations 1 to 9.

  Obligation 1: the encoding is deterministic and injective.
  Obligation 2: application is deterministic and total-or-refusing.
  Obligation 3: the delta predicate is exactly byte-exact transition.
  Obligation 4: the delta predicate assumes nothing beyond transition.
  Obligation 5: tombstones and revocations mean removal of effect.
  Obligation 6: scope and version changes are ordinary transitions.
  Obligation 7: parser agreement.
  Obligation 8: executable checker agreement.
  Obligation 9: version binding.

  Premise P2 (collision resistance) appears only as an explicit
  hypothesis, in the form: the root map sends distinct states to
  distinct roots. It is never proved and never an axiom.
-/

import SoftwareIsQuantifiable.Spine.Core

namespace SoftwareIsQuantifiable
namespace Spine

/-! ## Facts about the two application functions -/

/-- The plain application function, one event at a time. -/
theorem applycons (s : State) (e : Event) (es : List Event) :
    apply s (e :: es) = (step s e).bind (fun s' => apply s' es) :=
  rfl

/-- The checked application function, one event at a time. -/
theorem capplycons (t : Tuple) (s : State) (e : Event) (es : List Event) :
    capply t s (e :: es) = (cstep t s e).bind (fun s' => capply t s' es) :=
  rfl

/-- The plain application function splits over a joined sequence. -/
theorem applyappend (s : State) (l₁ l₂ : List Event) :
    apply s (l₁ ++ l₂) = (apply s l₁).bind (fun s' => apply s' l₂) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons e es ih =>
    rw [List.cons_append, applycons, applycons]
    have hfun : (fun s' => apply s' (es ++ l₂)) =
        (fun s' => (apply s' es).bind (fun s'' => apply s'' l₂)) :=
      funext (fun s' => ih s')
    rw [hfun, Option.bind_assoc]

/-- The checked application function splits over a joined sequence. -/
theorem capplyappend (t : Tuple) (s : State) (l₁ l₂ : List Event) :
    capply t s (l₁ ++ l₂) = (capply t s l₁).bind (fun s' => capply t s' l₂) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons e es ih =>
    rw [List.cons_append, capplycons, capplycons]
    have hfun : (fun s' => capply t s' (es ++ l₂)) =
        (fun s' => (capply t s' es).bind (fun s'' => capply t s'' l₂)) :=
      funext (fun s' => ih s')
    rw [hfun, Option.bind_assoc]

/-! ## Obligation 1: the encoding is deterministic and injective -/

/-- Injectivity of the canonical encoding, all five kinds, with the
    cross-kind cases discharged by the distinct kind tags. -/
theorem inj : ∀ {a b : Event}, encode a = encode b → a = b := by
  intro a
  induction a with
  | add f =>
    intro b h
    cases b with
    | add g => simp [encode] at h; subst h; rfl
    | tomb g => simp [encode] at h
    | revoke e => simp [encode] at h
    | scope v => simp [encode] at h
    | version t => simp [encode] at h
  | tomb f =>
    intro b h
    cases b with
    | add g => simp [encode] at h
    | tomb g => simp [encode] at h; subst h; rfl
    | revoke e => simp [encode] at h
    | scope v => simp [encode] at h
    | version t => simp [encode] at h
  | revoke e ih =>
    intro b h
    cases b with
    | add g => simp [encode] at h
    | tomb g => simp [encode] at h
    | revoke e' =>
      simp only [encode, List.cons.injEq] at h
      exact congrArg Event.revoke (ih h.2)
    | scope v => simp [encode] at h
    | version t => simp [encode] at h
  | scope v =>
    intro b h
    cases b with
    | add g => simp [encode] at h
    | tomb g => simp [encode] at h
    | revoke e => simp [encode] at h
    | scope w => simp [encode] at h; subst h; rfl
    | version t => simp [encode] at h
  | version t =>
    intro b h
    cases b with
    | add g => simp [encode] at h
    | tomb g => simp [encode] at h
    | revoke e => simp [encode] at h
    | scope v => simp [encode] at h
    | version t' =>
      cases t with
      | mk a₁ a₂ a₃ a₄ a₅ =>
        cases t' with
        | mk b₁ b₂ b₃ b₄ b₅ =>
          simp only [encode, List.cons.injEq, and_imp] at h
          obtain ⟨_, h₁, h₂, h₃, h₄, h₅, _⟩ := h
          subst h₁; subst h₂; subst h₃; subst h₄; subst h₅; rfl

/-- The encoding of an event is a function of the event alone: two
    encodings of the same event, wherever it sits, are equal. -/
theorem alone (e : Event) (x y : List Nat) (hx : x = encode e) (hy : y = encode e) :
    x = y := by rw [hx, hy]

/-! ## Obligation 2: application is deterministic and total-or-refusing -/

/-- The plain application function is deterministic. -/
theorem det {s : State} {es : List Event} {a b : State}
    (ha : apply s es = some a) (hb : apply s es = some b) : a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

/-- The checked application function is deterministic. -/
theorem cdet {t : Tuple} {s : State} {es : List Event} {a b : State}
    (ha : capply t s es = some a) (hb : capply t s es = some b) : a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

/-- The plain application function is total-or-refusing: every input
    reaches a child state or the refusal branch, never an undefined
    case. -/
theorem total (s : State) (es : List Event) :
    apply s es = none ∨ ∃ s', apply s es = some s' := by
  cases h : apply s es with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

/-- The checked application function is total-or-refusing. -/
theorem ctotal (t : Tuple) (s : State) (es : List Event) :
    capply t s es = none ∨ ∃ s', capply t s es = some s' := by
  cases h : capply t s es with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

/-! ## Obligation 3: the delta predicate is exactly byte-exact transition -/

/-- The delta predicate: it holds of a delta under a hash and a tuple
    exactly when the state named by the parent root, under the checked
    application function, yields a child state whose recomputed root
    is byte-equal to the child root, and whose version declarations
    are the tuple in force. -/
def ValidDelta (h : List Nat → List Nat) (t : Tuple) (d : Delta) : Prop :=
  ∃ s s', root h s = d.parent ∧ capply t s d.events = some s' ∧
    root h s' = d.child ∧ s'.vers = t

/-- The predicate is exactly the byte-exact transition: both
    directions, with the child root recomputed from the child state
    (the root map applied to the child state), never compared from
    stored fields. -/
theorem exact (h : List Nat → List Nat) (t : Tuple) (d : Delta) :
    ValidDelta h t d ↔ ∃ s s', root h s = d.parent ∧
      capply t s d.events = some s' ∧ root h s' = d.child ∧ s'.vers = t :=
  Iff.rfl

/-- The uniqueness step, and the only place premise P2 enters this
    group: under P2, the parent root names a unique state, so the
    predicate checked at any state the parent root names is the
    predicate. -/
theorem named (h : List Nat → List Nat) (t : Tuple) (d : Delta)
    (hP2 : ∀ a b : State, root h a = root h b → a = b)
    (hv : ValidDelta h t d) {s : State} (hs : root h s = d.parent) :
    ∃ s', capply t s d.events = some s' ∧ root h s' = d.child ∧ s'.vers = t := by
  obtain ⟨s₀, s₁, h₀, h₁, h₂, h₃⟩ := hv
  have hseq : s = s₀ := hP2 s s₀ (by rw [hs, h₀])
  subst hseq
  exact ⟨s₁, h₁, h₂, h₃⟩

/-! ## Obligation 4: the delta predicate assumes nothing beyond transition -/

/-- The tuple in force for the two countermodels: every component 1. -/
def base : Tuple := ⟨1, 1, 1, 1, 1⟩

/-- First countermodel, parent state: no seeds, one rule that would
    derive the fact 2 from the fact 1. -/
def pstate : State := ⟨[], [⟨[1], 2⟩], 0, base⟩

/-- First countermodel, child state: the fact 1 added; the rule is
    present but its conclusion is not, so the child is not closed. -/
def cstate : State := ⟨[1], [⟨[1], 2⟩], 0, base⟩

/-- First countermodel, delta: one addition, roots recomputed. -/
def dmodel : Delta := ⟨root id pstate, [.add 1], root id cstate⟩

/-- The first child state is not closed under its own rule set. -/
theorem notclosed : ¬ Closed cstate := by
  intro h
  have h2 : (2 : Nat) ∈ cstate.seeds :=
    h ⟨[1], 2⟩ (by decide) (by intro p hp; simp at hp; subst hp; decide)
  exact absurd h2 (by decide)

/-- First countermodel, checked: the predicate holds and the child
    state is not closed. A standing control: any later strengthening
    of the predicate that breaks this reopens obligation 4. -/
theorem controlone : ValidDelta id base dmodel ∧ ¬ Closed cstate :=
  ⟨⟨pstate, cstate, rfl, rfl, rfl, rfl⟩, notclosed⟩

/-- Second countermodel, parent state: empty. -/
def pstatetwo : State := ⟨[], [], 0, base⟩

/-- Second countermodel, child state: one seed fact. -/
def cstatetwo : State := ⟨[5], [], 0, base⟩

/-- Second countermodel, delta: one addition, roots recomputed. -/
def dmodeltwo : Delta := ⟨root id pstatetwo, [.add 5], root id cstatetwo⟩

/-- Second countermodel, checked: the predicate holds and the child
    state has no coverage witnesses at all (the witness ledger is
    empty). A standing control, as above. -/
theorem controltwo : ValidDelta id base dmodeltwo ∧
    ∀ w ∈ ([] : List Witness),
      ¬ (w.fact ∈ cstatetwo.seeds ∧ w.root = root id cstatetwo) :=
  ⟨⟨pstatetwo, cstatetwo, rfl, rfl, rfl, rfl⟩, by simp⟩

/-! ## Obligation 5: tombstones and revocations mean removal of effect -/

/-- Cutting a fact changes the seed set and nothing else: the full
    resulting state is the old state with the seed set cut. -/
theorem cutfull (s : State) (f : Nat) :
    (cut s f).seeds = s.seeds.erase f ∧ (cut s f).rules = s.rules ∧
      (cut s f).scope = s.scope ∧ (cut s f).vers = s.vers :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Putting a fact changes the seed set and nothing else. -/
theorem putfull (s : State) (f : Nat) :
    (put s f).rules = s.rules ∧ (put s f).scope = s.scope ∧
      (put s f).vers = s.vers :=
  ⟨rfl, rfl, rfl⟩

/-- A tombstone in last position: the whole delta is the prefix delta
    followed by exactly the removal of the fact, over the full state. -/
theorem last (s : State) (es : List Event) (f : Nat) :
    apply s (es ++ [.tomb f]) = (apply s es).map (fun x => cut x f) := by
  rw [applyappend]
  cases h : apply s es with
  | none => rfl
  | some x => rfl

/-- A tombstone in first position: the rest of the delta runs on
    exactly the state with the fact removed. -/
theorem first (s : State) (es : List Event) (f : Nat) :
    apply s (.tomb f :: es) = apply (cut s f) es :=
  rfl

/-- A tombstone in middle position: the prefix runs, then exactly the
    removal, then the rest, by equality of the full resulting state. -/
theorem middle (s : State) (pre post : List Event) (f : Nat) :
    apply s (pre ++ .tomb f :: post) =
      (apply s pre).bind (fun x => apply (cut x f) post) := by
  rw [applyappend]
  have hfun : (fun x => apply x (.tomb f :: post)) =
      (fun x => apply (cut x f) post) := funext (fun x => rfl)
  rw [hfun]

/-- A revocation of an addition inside the same delta: at its
    position it is exactly the removal of the fact, over the full
    resulting state. -/
theorem revokesame (s : State) (pre post : List Event) (f : Nat) :
    apply s (pre ++ .revoke (.add f) :: post) =
      (apply s pre).bind (fun x => apply (cut x f) post) := by
  rw [applyappend]
  have hfun : (fun x => apply x (.revoke (.add f) :: post)) =
      (fun x => apply (cut x f) post) := funext (fun x => rfl)
  rw [hfun]

/-- A revocation of a tombstone inside the same delta: at its
    position it is exactly the restoration of the fact. -/
theorem revoketomb (s : State) (pre post : List Event) (f : Nat) :
    apply s (pre ++ .revoke (.tomb f) :: post) =
      (apply s pre).bind (fun x => apply (put x f) post) := by
  rw [applyappend]
  have hfun : (fun x => apply x (.revoke (.tomb f) :: post)) =
      (fun x => apply (put x f) post) := funext (fun x => rfl)
  rw [hfun]

/-- A revocation of an event in an earlier delta: the parent state is
    the earlier delta's result, whatever it is, and the revoking delta
    removes exactly that event's effect from it — the full state is
    the parent state with the fact cut, and by the cut fact above no
    other seed, rule, scope entry, or version entry changes. -/
theorem earlier (s : State) (f : Nat) :
    apply s [.revoke (.add f)] = some (cut s f) :=
  rfl

/-- A revocation of a tombstone from an earlier delta restores
    exactly the fact, over the full state. -/
theorem earlierput (s : State) (f : Nat) :
    apply s [.revoke (.tomb f)] = some (put s f) :=
  rfl

/-! ## Obligation 6: scope and version changes are ordinary transitions -/

/-- A scope change is applied by the same application function as
    every other kind, and changes exactly the scope declaration: the
    full resulting state is the old state with the scope replaced. -/
theorem scopechange (s : State) (v : Nat) :
    apply s [.scope v] = some { s with scope := v } :=
  rfl

/-- The scope-changed state agrees with the old state on seeds,
    rules, and version declarations. -/
theorem scopeonly (s : State) (v : Nat) :
    ({ s with scope := v } : State).seeds = s.seeds ∧
      ({ s with scope := v } : State).rules = s.rules ∧
      ({ s with scope := v } : State).vers = s.vers :=
  ⟨rfl, rfl, rfl⟩

/-- A version change under the tuple it names is an ordinary
    transition: it changes exactly the version declarations. -/
theorem versionok (s : State) (v : Tuple) :
    capply v s [.version v] = some { s with vers := v } := by
  show (cstep v s (.version v)).bind (fun s' => capply v s' []) = _
  simp [cstep, capply]

/-- The version-changed state agrees with the old state on seeds,
    rules, and scope. -/
theorem versiononly (s : State) (v : Tuple) :
    ({ s with vers := v } : State).seeds = s.seeds ∧
      ({ s with vers := v } : State).rules = s.rules ∧
      ({ s with vers := v } : State).scope = s.scope :=
  ⟨rfl, rfl, rfl⟩

/-- The refusal case: a version change that would alter the tuple
    under which the delta itself is being checked refuses the whole
    delta. -/
theorem versionrefuse (s : State) (t v : Tuple) (h : v ≠ t) :
    capply t s [.version v] = none := by
  show (cstep t s (.version v)).bind (fun s' => capply t s' []) = none
  simp [cstep, h]

/-! ## Obligation 7: parser agreement -/

/-- The computable parser for one event: read the kind tag, then the
    payload words of that kind. A revocation nests one inner event. -/
def parseevent : List Nat → Option (Event × List Nat)
  | [] => none
  | tag :: rest =>
    if tag = 1 then
      match rest with
      | f :: r => some (.add f, r)
      | [] => none
    else if tag = 2 then
      match rest with
      | f :: r => some (.tomb f, r)
      | [] => none
    else if tag = 3 then
      (parseevent rest).map (fun p => (.revoke p.1, p.2))
    else if tag = 4 then
      match rest with
      | v :: r => some (.scope v, r)
      | [] => none
    else if tag = 5 then
      match rest with
      | a :: b :: c :: d :: e :: r => some (.version ⟨a, b, c, d, e⟩, r)
      | _ => none
    else none

/-- Parsing the encoding of an event returns the event and leaves
    the rest of the input untouched. -/
theorem parseeventround : ∀ (e : Event) (rest : List Nat),
    parseevent (encode e ++ rest) = some (e, rest) := by
  intro e
  induction e with
  | add f => intro rest; rfl
  | tomb f => intro rest; rfl
  | revoke e ih => intro rest; simp [parseevent, encode, ih]
  | scope v => intro rest; rfl
  | version t => intro rest; rfl

/-- The parser for a counted sequence of events. -/
def parseevents : Nat → List Nat → Option (List Event × List Nat)
  | 0, b => some ([], b)
  | n + 1, b =>
    match parseevent b with
    | none => none
    | some (e, r) =>
      match parseevents n r with
      | none => none
      | some (es, r') => some (e :: es, r')

/-- Parsing the encoding of an event sequence returns the sequence. -/
theorem parseeventsround : ∀ (es : List Event) (rest : List Nat),
    parseevents es.length (es.flatMap encode ++ rest) = some (es, rest) := by
  intro es
  induction es with
  | nil => intro rest; rfl
  | cons e es ih =>
    intro rest
    simp [parseevents, List.flatMap_cons, List.append_assoc,
      parseeventround, ih]

/-- Parsing one event is sound: whatever it returns, the input was
    exactly the canonical encoding of that event followed by the
    leftover. Proved by cases on the tag word. -/
theorem parseeventsound : ∀ (b : List Nat) (e : Event) (r : List Nat),
    parseevent b = some (e, r) → b = encode e ++ r := by
  intro b
  induction b with
  | nil => intro e r h; simp [parseevent] at h
  | cons tag rest ih =>
    intro e r h
    rcases (by omega : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨
        tag = 5 ∨ 6 ≤ tag) with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst h0; simp [parseevent] at h
    · subst h1
      cases rest with
      | nil => simp [parseevent] at h
      | cons f r' =>
        simp [parseevent] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · subst h2
      cases rest with
      | nil => simp [parseevent] at h
      | cons f r' =>
        simp [parseevent] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · subst h3
      simp only [parseevent, if_neg (by decide : ¬ (3 : Nat) = 1),
        if_neg (by decide : ¬ (3 : Nat) = 2), if_pos rfl] at h
      cases hpe : parseevent rest with
      | none => simp [hpe] at h
      | some p =>
        obtain ⟨e', r'⟩ := p
        simp [hpe] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrec := ih e' r' hpe
        simp [encode, hrec]
    · subst h4
      cases rest with
      | nil => simp [parseevent] at h
      | cons v r' =>
        simp [parseevent] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · subst h5
      cases rest with
      | nil => simp [parseevent] at h
      | cons a rest₁ =>
        cases rest₁ with
        | nil => simp [parseevent] at h
        | cons b₁ rest₂ =>
          cases rest₂ with
          | nil => simp [parseevent] at h
          | cons c rest₃ =>
            cases rest₃ with
            | nil => simp [parseevent] at h
            | cons d rest₄ =>
              cases rest₄ with
              | nil => simp [parseevent] at h
              | cons e₅ r' =>
                simp [parseevent] at h
                obtain ⟨rfl, rfl⟩ := h
                rfl
    · simp [parseevent, show tag ≠ 1 by omega, show tag ≠ 2 by omega,
        show tag ≠ 3 by omega, show tag ≠ 4 by omega,
        show tag ≠ 5 by omega] at h

/-- Soundness of the counted sequence parser: the count matches and
    the input was exactly the concatenated encodings. -/
theorem parseeventssound : ∀ (n : Nat) (b : List Nat) (es : List Event)
    (r : List Nat), parseevents n b = some (es, r) →
    es.length = n ∧ b = es.flatMap encode ++ r := by
  intro n
  induction n with
  | zero =>
    intro b es r h
    simp [parseevents] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro b es r h
    simp only [parseevents] at h
    cases hpe : parseevent b with
    | none => simp [hpe] at h
    | some p =>
      obtain ⟨e, r₁⟩ := p
      simp [hpe] at h
      cases hps : parseevents n r₁ with
      | none => simp [hps] at h
      | some q =>
        obtain ⟨es', r'⟩ := q
        simp [hps] at h
        obtain ⟨rfl, rfl⟩ := h
        have h₁ := parseeventsound b e r₁ hpe
        have h₂ := ih r₁ es' r' hps
        obtain ⟨hlen, hb⟩ := h₂
        refine ⟨by simp [hlen], ?_⟩
        rw [h₁, hb, List.flatMap_cons, List.append_assoc]

/-- The parser for a length-headed list of words. -/
def parselist (b : List Nat) : Option (List Nat × List Nat) :=
  match b with
  | [] => none
  | n :: rest => if rest.length < n then none else some (rest.take n, rest.drop n)

/-- Taking a whole list off the front of a joined list. -/
theorem takel : ∀ (l r : List Nat), (l ++ r).take l.length = l := by
  intro l
  induction l with
  | nil => intro r; rfl
  | cons a l ih => intro r; simp [ih]

/-- Dropping a whole list off the front of a joined list. -/
theorem dropl : ∀ (l r : List Nat), (l ++ r).drop l.length = r := by
  intro l
  induction l with
  | nil => intro r; rfl
  | cons a l ih => intro r; simp [ih]

/-- Parsing the encoding of a word list returns the list. -/
theorem parselistround (l rest : List Nat) :
    parselist (encnats l ++ rest) = some (l, rest) := by
  have hlen : ¬ (l ++ rest).length < l.length := by
    rw [List.length_append]; omega
  unfold parselist encnats
  simp [hlen, takel, dropl]

/-- Soundness of the word list parser. -/
theorem parselistsound : ∀ (b : List Nat) (l : List Nat) (r : List Nat),
    parselist b = some (l, r) → b = encnats l ++ r := by
  intro b l r h
  cases b with
  | nil => simp [parselist] at h
  | cons n rest =>
    have hle : n ≤ rest.length := by
      cases Nat.lt_or_ge rest.length n with
      | inl hc => simp [parselist, hc] at h
      | inr hc => exact hc
    have h' : parselist (n :: rest) = some (rest.take n, rest.drop n) := by
      simp [parselist, show ¬ rest.length < n from by omega]
    rw [h'] at h
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    have hlen : (rest.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left hle]
    show n :: rest = encnats (rest.take n) ++ rest.drop n
    have e1 : encnats (rest.take n) = n :: rest.take n := by
      unfold encnats; rw [hlen]
    rw [e1, List.cons_append, List.take_append_drop]

/-- The canonical encoding of a whole delta: parent root, child
    root, then the counted event encodings. -/
def encdelta (d : Delta) : List Nat :=
  encnats d.parent ++ encnats d.child ++
    (d.events.length :: d.events.flatMap encode)

/-- The computable parser for a whole delta. It accepts only a
    canonical encoding consumed in full. -/
def parse (b : List Nat) : Option Delta :=
  match parselist b with
  | none => none
  | some (p, r₁) =>
    match parselist r₁ with
    | none => none
    | some (c, r₂) =>
      match r₂ with
      | [] => none
      | n :: r₃ =>
        match parseevents n r₃ with
        | some (es, []) => some ⟨p, es, c⟩
        | _ => none

/-- Parsing the encoding of a delta returns the delta: same events,
    same order, same parent and child roots. -/
theorem parseround (d : Delta) : parse (encdelta d) = some d := by
  cases d with
  | mk p es c =>
    have hr := parseeventsround es ([] : List Nat)
    rw [List.append_nil] at hr
    simp [parse, encdelta, parselistround, hr]

/-- Parsing is sound: whatever the parser accepts, the input was
    exactly that delta's canonical encoding. -/
theorem parsesound (b : List Nat) (d : Delta) :
    parse b = some d → b = encdelta d := by
  intro h
  unfold parse at h
  cases h₁ : parselist b with
  | none => simp [h₁] at h
  | some q₁ =>
    obtain ⟨p, r₁⟩ := q₁
    simp [h₁] at h
    cases h₂ : parselist r₁ with
    | none => simp [h₂] at h
    | some q₂ =>
      obtain ⟨c, r₂⟩ := q₂
      simp [h₂] at h
      cases r₂ with
      | nil => simp at h
      | cons n r₃ =>
        cases h₃ : parseevents n r₃ with
        | none => simp [h₃] at h
        | some q₃ =>
          obtain ⟨es, r₄⟩ := q₃
          cases r₄ with
          | nil =>
            simp [h₃] at h
            obtain rfl : (⟨p, es, c⟩ : Delta) = d := h
            have hs₁ := parselistsound b p r₁ h₁
            have hs₂ := parselistsound r₁ c (n :: r₃) h₂
            have hs₃ := parseeventssound n r₃ es [] h₃
            obtain ⟨hlen, hb⟩ := hs₃
            rw [hs₁, hs₂, hb]
            simp [encdelta, hlen]
          | cons x r₅ => simp [h₃] at h

/-- Obligation 7, closed: the parser accepts a byte string as a
    delta if and only if the semantics recognises it as one — that
    is, if and only if the byte string is the delta's canonical
    encoding, the recognition the definitions fix — and when it
    accepts, the delta it produces is that delta. -/
theorem parseagree (b : List Nat) (d : Delta) :
    parse b = some d ↔ b = encdelta d :=
  ⟨parsesound b d, fun h => by rw [h]; exact parseround d⟩

/-! ## Obligation 8: executable checker agreement -/

/-- The executable checker. It takes the parent state (the state the
    parent root names; a checker cannot invert a hash) and returns
    one of the three verdicts: unknown exactly when the delta's
    parent root does not name the supplied state, refuse when the
    checked application refuses or the recomputed child root differs
    from the child root or the child state's version declarations
    differ from the tuple in force, and accept otherwise. -/
def check (h : List Nat → List Nat) (t : Tuple) (s : State) (d : Delta) :
    Verdict :=
  if d.parent ≠ root h s then Verdict.unknown
  else
    match capply t s d.events with
    | none => Verdict.refuse
    | some s' =>
      if root h s' = d.child ∧ s'.vers = t then Verdict.accept
      else Verdict.refuse

/-- The checker's result, recorded with the version tuple it was
    produced under. -/
def recorded (h : List Nat → List Nat) (t : Tuple) (s : State) (d : Delta) :
    Verdict × Tuple :=
  (check h t s d, t)

/-- Checker agreement, against the semantics at the named state: the
    checker accepts if and only if the checked application of the
    delta to that state yields a child state whose recomputed root
    is the child root and whose version declarations are the tuple
    in force. -/
theorem checkaccept (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta) :
    check h t s d = Verdict.accept ↔
      d.parent = root h s ∧ ∃ s', capply t s d.events = some s' ∧
        root h s' = d.child ∧ s'.vers = t := by
  unfold check
  by_cases hp : d.parent = root h s
  · rw [if_neg (fun hne => hne hp)]
    cases hc : capply t s d.events with
    | none =>
      show Verdict.refuse = Verdict.accept ↔ _
      constructor
      · intro hcon; cases hcon
      · intro hcon
        obtain ⟨_, s', hs', _⟩ := hcon
        cases hs'
    | some s' =>
      show (if root h s' = d.child ∧ s'.vers = t then Verdict.accept
        else Verdict.refuse) = Verdict.accept ↔ _
      by_cases hq : root h s' = d.child ∧ s'.vers = t
      · rw [if_pos hq]
        constructor
        · intro _; exact ⟨hp, s', rfl, hq.1, hq.2⟩
        · intro _; rfl
      · rw [if_neg hq]
        constructor
        · intro hcon; cases hcon
        · intro hcon
          obtain ⟨_, s'', hs'', h₁, h₂⟩ := hcon
          have hseq : s' = s'' := Option.some.inj hs''
          subst hseq
          exact absurd ⟨h₁, h₂⟩ hq
  · rw [if_pos hp]
    constructor
    · intro hcon; cases hcon
    · intro hcon; exact absurd hcon.1 hp

/-- The checker does not accept exactly where the semantics form
    fails: refusal and unknown together cover exactly the false and
    outside-the-domain cases. -/
theorem checknot (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta) :
    check h t s d ≠ Verdict.accept ↔
      ¬ (d.parent = root h s ∧ ∃ s', capply t s d.events = some s' ∧
        root h s' = d.child ∧ s'.vers = t) := by
  constructor
  · intro hne hcon
    exact hne ((checkaccept h t s d).mpr hcon)
  · intro hn hacc
    exact hn ((checkaccept h t s d).mp hacc)

/-- The unknown verdict is returned exactly in the outside-the-domain
    case: the delta's parent root does not name the supplied state. -/
theorem checkunknown (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta) :
    check h t s d = Verdict.unknown ↔ d.parent ≠ root h s := by
  unfold check
  by_cases hp : d.parent ≠ root h s
  · rw [if_pos hp]
    exact ⟨fun _ => hp, fun _ => rfl⟩
  · rw [if_neg hp]
    constructor
    · intro hcon
      cases hc : capply t s d.events with
      | none =>
        rw [hc] at hcon
        change Verdict.refuse = Verdict.unknown at hcon
        cases hcon
      | some s' =>
        rw [hc] at hcon
        change (if root h s' = d.child ∧ s'.vers = t then Verdict.accept
          else Verdict.refuse) = Verdict.unknown at hcon
        by_cases hq : root h s' = d.child ∧ s'.vers = t
        · rw [if_pos hq] at hcon; cases hcon
        · rw [if_neg hq] at hcon; cases hcon
    · intro hcon; exact absurd hcon hp

/-- Checker agreement against the delta predicate itself. The step
    from the supplied state to the state the parent root names is
    premise P2, carried here as the explicit hypothesis it is. -/
theorem agree (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta)
    (hP2 : ∀ a b : State, root h a = root h b → a = b) :
    check h t s d = Verdict.accept ↔
      ValidDelta h t d ∧ d.parent = root h s := by
  rw [checkaccept]
  constructor
  · intro hcon
    obtain ⟨hp, s', h₁, h₂, h₃⟩ := hcon
    exact ⟨⟨s, s', hp.symm, h₁, h₂, h₃⟩, hp⟩
  · intro hcon
    obtain ⟨⟨s₀, s₁, h₀, h₁, h₂, h₃⟩, hp⟩ := hcon
    have hseq : s = s₀ := hP2 s s₀ (by rw [← hp, h₀])
    subst hseq
    exact ⟨hp, s₁, h₁, h₂, h₃⟩

/-- Obligation 6, closing form: a delta is never checked under a
    tuple different from the one its child state commits to — an
    acceptance exhibits the child state, and its version declarations
    are the tuple in force. -/
theorem commits (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta) (ha : check h t s d = Verdict.accept) :
    ∃ s', capply t s d.events = some s' ∧ root h s' = d.child ∧
      s'.vers = t :=
  ((checkaccept h t s d).mp ha).2

/-! ## Obligation 9: version binding -/

/-- The recorded tuple of a checker result is the tuple in force
    when the result was produced. -/
theorem recordedtuple (h : List Nat → List Nat) (t : Tuple) (s : State)
    (d : Delta) : (recorded h t s d).2 = t :=
  rfl

/-- The depth of an event: how deeply revocations nest. -/
def depth : Event → Nat
  | .add _ => 0
  | .tomb _ => 0
  | .revoke e => depth e + 1
  | .scope _ => 0
  | .version _ => 0

/-- A checked step that succeeds leaves the version declarations
    either untouched or set to the tuple in force. -/
theorem cstepvers (t : Tuple) : ∀ (n : Nat) (e : Event), depth e ≤ n →
    ∀ (s s' : State), cstep t s e = some s' →
    s'.vers = s.vers ∨ s'.vers = t := by
  intro n
  induction n with
  | zero =>
    intro e hd s s' h
    cases e with
    | add f =>
      have h' : s' = put s f := (Option.some.inj h).symm
      exact Or.inl (by rw [h']; rfl)
    | tomb f =>
      have h' : s' = cut s f := (Option.some.inj h).symm
      exact Or.inl (by rw [h']; rfl)
    | revoke e' =>
      have hd' : depth (Event.revoke e') = depth e' + 1 := rfl
      rw [hd'] at hd
      exact False.elim (Nat.not_succ_le_zero _ hd)
    | scope v =>
      have h' : s' = { s with scope := v } := (Option.some.inj h).symm
      exact Or.inl (by rw [h'])
    | version v =>
      by_cases hv : v = t
      · have h' : s' = { s with vers := v } := by
          have hcc : cstep t s (.version v) =
              some { s with vers := v } := by simp [cstep, hv]
          exact (Option.some.inj (hcc.symm.trans h)).symm
        exact Or.inr (by rw [h']; exact hv)
      · simp [cstep, hv] at h
  | succ n ih =>
    intro e hd s s' h
    cases e with
    | add f =>
      have h' : s' = put s f := (Option.some.inj h).symm
      exact Or.inl (by rw [h']; rfl)
    | tomb f =>
      have h' : s' = cut s f := (Option.some.inj h).symm
      exact Or.inl (by rw [h']; rfl)
    | revoke e' =>
      cases e' with
      | add f =>
        have h' : s' = cut s f := (Option.some.inj h).symm
        exact Or.inl (by rw [h']; rfl)
      | tomb f =>
        have h' : s' = put s f := (Option.some.inj h).symm
        exact Or.inl (by rw [h']; rfl)
      | revoke e'' =>
        have hd' : depth e'' ≤ n := by
          have h₁ : depth (Event.revoke (Event.revoke e'')) =
              depth e'' + 2 := rfl
          omega
        exact ih e'' hd' s s' h
      | scope v => simp [cstep] at h
      | version v => simp [cstep] at h
    | scope v =>
      have h' : s' = { s with scope := v } := (Option.some.inj h).symm
      exact Or.inl (by rw [h'])
    | version v =>
      by_cases hv : v = t
      · have h' : s' = { s with vers := v } := by
          have hcc : cstep t s (.version v) =
              some { s with vers := v } := by simp [cstep, hv]
          exact (Option.some.inj (hcc.symm.trans h)).symm
        exact Or.inr (by rw [h']; exact hv)
      · simp [cstep, hv] at h

/-- Two checked steps of the same event under two tuples, both
    succeeding, agree on the resulting state — or the tuples were
    the same all along. -/
theorem cstepagree (t t' : Tuple) : ∀ (n : Nat) (e : Event),
    depth e ≤ n → ∀ (s x y : State), cstep t s e = some x →
    cstep t' s e = some y → x = y ∨ t = t' := by
  intro n
  induction n with
  | zero =>
    intro e hd s x y hx hy
    cases e with
    | add f =>
      have h₁ : x = put s f := (Option.some.inj hx).symm
      have h₂ : y = put s f := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | tomb f =>
      have h₁ : x = cut s f := (Option.some.inj hx).symm
      have h₂ : y = cut s f := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | revoke e' =>
      have hd' : depth (Event.revoke e') = depth e' + 1 := rfl
      rw [hd'] at hd
      exact False.elim (Nat.not_succ_le_zero _ hd)
    | scope v =>
      have h₁ : x = { s with scope := v } := (Option.some.inj hx).symm
      have h₂ : y = { s with scope := v } := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | version v =>
      have hvt : v = t := by
        by_cases hc : v = t
        · exact hc
        · simp [cstep, hc] at hx
      have hvt' : v = t' := by
        by_cases hc : v = t'
        · exact hc
        · simp [cstep, hc] at hy
      exact Or.inr (hvt.symm.trans hvt')
  | succ n ih =>
    intro e hd s x y hx hy
    cases e with
    | add f =>
      have h₁ : x = put s f := (Option.some.inj hx).symm
      have h₂ : y = put s f := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | tomb f =>
      have h₁ : x = cut s f := (Option.some.inj hx).symm
      have h₂ : y = cut s f := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | revoke e' =>
      cases e' with
      | add f =>
        have h₁ : x = cut s f := (Option.some.inj hx).symm
        have h₂ : y = cut s f := (Option.some.inj hy).symm
        exact Or.inl (h₁.trans h₂.symm)
      | tomb f =>
        have h₁ : x = put s f := (Option.some.inj hx).symm
        have h₂ : y = put s f := (Option.some.inj hy).symm
        exact Or.inl (h₁.trans h₂.symm)
      | revoke e'' =>
        have hd' : depth e'' ≤ n := by
          have h₁ : depth (Event.revoke (Event.revoke e'')) =
              depth e'' + 2 := rfl
          omega
        exact ih e'' hd' s x y hx hy
      | scope v => simp [cstep] at hx
      | version v => simp [cstep] at hx
    | scope v =>
      have h₁ : x = { s with scope := v } := (Option.some.inj hx).symm
      have h₂ : y = { s with scope := v } := (Option.some.inj hy).symm
      exact Or.inl (h₁.trans h₂.symm)
    | version v =>
      have hvt : v = t := by
        by_cases hc : v = t
        · exact hc
        · simp [cstep, hc] at hx
      have hvt' : v = t' := by
        by_cases hc : v = t'
        · exact hc
        · simp [cstep, hc] at hy
      exact Or.inr (hvt.symm.trans hvt')

/-- The same agreement for whole event sequences. -/
theorem capplyagree (t t' : Tuple) (s : State) :
    ∀ (es : List Event) (a b : State), capply t s es = some a →
    capply t' s es = some b → a = b ∨ t = t' := by
  intro es
  induction es generalizing s with
  | nil =>
    intro a b ha hb
    have h₁ : a = s := (Option.some.inj ha).symm
    have h₂ : b = s := (Option.some.inj hb).symm
    exact Or.inl (h₁.trans h₂.symm)
  | cons e es ih =>
    intro a b ha hb
    rw [capplycons] at ha hb
    cases hx : cstep t s e with
    | none => simp [hx] at ha
    | some x =>
      cases hy : cstep t' s e with
      | none => simp [hy] at hb
      | some y =>
        simp [hx] at ha
        simp [hy] at hb
        rcases cstepagree t t' (depth e) e (Nat.le_refl _) s x y hx hy with
          hxy | htt
        · subst hxy
          exact ih x a b ha hb
        · exact Or.inr htt

/-- Version binding, voidness: one delta, one parent state, and one
    pair of roots cannot be accepted under two different tuples. A
    result produced under a tuple that differs in any component from
    the tuple in force is void — re-presented under the changed
    tuple, the verdict is not accept. The control case is executed
    in the corpus run recorded for this lane. -/
theorem void (h : List Nat → List Nat) (t t' : Tuple) (s : State)
    (d : Delta) (ha : check h t s d = Verdict.accept)
    (hb : check h t' s d = Verdict.accept) : t = t' := by
  obtain ⟨-, a, h₁, -, h₃⟩ := (checkaccept h t s d).mp ha
  obtain ⟨-, b, h₄, -, h₆⟩ := (checkaccept h t' s d).mp hb
  rcases capplyagree t t' s d.events a b h₁ h₄ with hab | htt
  · exact h₃.symm.trans ((congrArg State.vers hab).trans h₆)
  · exact htt

/-! ## Axiom audit for the closing theorems of obligations 1 to 9 -/

#print axioms inj
#print axioms alone
#print axioms det
#print axioms cdet
#print axioms total
#print axioms ctotal
#print axioms exact
#print axioms named
#print axioms controlone
#print axioms controltwo
#print axioms cutfull
#print axioms putfull
#print axioms last
#print axioms first
#print axioms middle
#print axioms revokesame
#print axioms revoketomb
#print axioms earlier
#print axioms earlierput
#print axioms scopechange
#print axioms scopeonly
#print axioms versionok
#print axioms versiononly
#print axioms versionrefuse
#print axioms parseagree
#print axioms checkaccept
#print axioms checknot
#print axioms checkunknown
#print axioms agree
#print axioms commits
#print axioms recordedtuple
#print axioms void

end Spine
end SoftwareIsQuantifiable
