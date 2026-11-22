/-
  The update and checker spine: shared definitions.

  This module carries the definitions every spine lane needs: the five
  canonical event kinds, their canonical encoding, the snapshot state,
  the root, the delta, the two application functions (plain and
  tuple-checked), and the witness shape. The proof obligations that
  rest on these definitions live in the delta module beside this one.

  The hash function is a parameter throughout. Collision resistance
  (premise P2 of the spine spec) is a hypothesis wherever it is used,
  never a definition and never an axiom.
-/

namespace SoftwareIsQuantifiable
namespace Spine

/-- The version tuple: the ordered list of the five version components,
    in the order the spec fixes. -/
structure Tuple where
  /-- The semantics version. -/
  sem : Nat
  /-- The parser version. -/
  par : Nat
  /-- The checker version. -/
  chk : Nat
  /-- The encoding version. -/
  enc : Nat
  /-- The hash version. -/
  hsh : Nat
deriving DecidableEq, Repr

/-- A canonical event: exactly five kinds. A revocation carries the
    event it revokes. -/
inductive Event where
  /-- An addition of a fact. -/
  | add : Nat → Event
  /-- A tombstone over a fact. -/
  | tomb : Nat → Event
  /-- A revocation of a prior event. -/
  | revoke : Event → Event
  /-- A scope change: the new scope declaration. -/
  | scope : Nat → Event
  /-- A version change: the new version declarations. -/
  | version : Tuple → Event
deriving DecidableEq, Repr

/-- The canonical encoding of an event, as a list of words. The first
    word is the kind tag: 1, 2, 3, 4, or 5. The encoding is a function
    of the event alone. -/
def encode : Event → List Nat
  | .add f => [1, f]
  | .tomb f => [2, f]
  | .revoke e => 3 :: encode e
  | .scope v => [4, v]
  | .version t => [5, t.sem, t.par, t.chk, t.enc, t.hsh]

/-- A ground rule: from all of its premises jointly, its conclusion. -/
structure Rule where
  /-- The premise facts. -/
  premises : List Nat
  /-- The conclusion fact. -/
  conclusion : Nat
deriving DecidableEq, Repr

/-- A snapshot state: exactly the four parts the spec names. The seed
    list is read as a set of facts. -/
structure State where
  /-- The seed set. -/
  seeds : List Nat
  /-- The rule set. -/
  rules : List Rule
  /-- The scope declaration. -/
  scope : Nat
  /-- The version declarations. -/
  vers : Tuple
deriving DecidableEq, Repr

/-- A delta: a finite sequence of canonical events together with a
    parent root and a child root. Order in the sequence is part of
    the delta. -/
structure Delta where
  /-- The parent root. -/
  parent : List Nat
  /-- The event sequence. -/
  events : List Event
  /-- The child root. -/
  child : List Nat
deriving DecidableEq, Repr

/-- The encoding of a list of words: its length, then the words. -/
def encnats (l : List Nat) : List Nat := l.length :: l

/-- The encoding of one rule. -/
def encrule (r : Rule) : List Nat := encnats r.premises ++ [r.conclusion]

/-- The encoding of a rule list: its length, then each rule. -/
def encrules (rs : List Rule) : List Nat := rs.length :: rs.flatMap encrule

/-- The encoding of a version tuple: its five components in order. -/
def enctuple (t : Tuple) : List Nat := [t.sem, t.par, t.chk, t.enc, t.hsh]

/-- The canonical encoding of a complete state, in the fixed order:
    seeds, rules, scope, version declarations. -/
def encstate (s : State) : List Nat :=
  encnats s.seeds ++ encrules s.rules ++ [s.scope] ++ enctuple s.vers

/-- The root of a state: the named hash function, applied to the
    canonical encoding of the state. -/
def root (h : List Nat → List Nat) (s : State) : List Nat := h (encstate s)

/-- Put a fact into the seed set. -/
def put (s : State) (f : Nat) : State :=
  { s with seeds := if f ∈ s.seeds then s.seeds else f :: s.seeds }

/-- Cut a fact from the seed set: the removal of its effect. -/
def cut (s : State) (f : Nat) : State :=
  { s with seeds := s.seeds.erase f }

/-- One application step of the plain application function. A
    revocation of a scope or version change refuses: the prior value
    is not recoverable from the state alone. -/
def step (s : State) : Event → Option State
  | .add f => some (put s f)
  | .tomb f => some (cut s f)
  | .revoke (.add f) => some (cut s f)
  | .revoke (.tomb f) => some (put s f)
  | .revoke (.revoke e) => step s e
  | .revoke (.scope _) => none
  | .revoke (.version _) => none
  | .scope v => some { s with scope := v }
  | .version t => some { s with vers := t }

/-- The plain application function: apply the steps over the event
    sequence. Every input yields a child state or a refusal. -/
def apply (s : State) : List Event → Option State
  | [] => some s
  | e :: es => (step s e).bind (fun s' => apply s' es)

/-- One application step of the checked application function: as the
    plain step, except that a version change whose payload differs
    from the tuple in force refuses the whole delta. -/
def cstep (t : Tuple) (s : State) : Event → Option State
  | .add f => some (put s f)
  | .tomb f => some (cut s f)
  | .revoke (.add f) => some (cut s f)
  | .revoke (.tomb f) => some (put s f)
  | .revoke (.revoke e) => cstep t s e
  | .revoke (.scope _) => none
  | .revoke (.version _) => none
  | .scope v => some { s with scope := v }
  | .version v => if v = t then some { s with vers := v } else none

/-- The checked application function, under the tuple in force. -/
def capply (t : Tuple) (s : State) : List Event → Option State
  | [] => some s
  | e :: es => (cstep t s e).bind (fun s' => capply t s' es)

/-- A coverage witness: a record naming a fact, the root of the
    snapshot it belongs to, a mediation path (a list of sites), and
    the sensor evidence it rests on (an evidence code). -/
structure Witness where
  /-- The fact witnessed. -/
  fact : Nat
  /-- The root of the snapshot the witness belongs to. -/
  root : List Nat
  /-- The mediation path: a list of sites. -/
  path : List Nat
  /-- The sensor evidence code. -/
  evid : Nat
deriving DecidableEq, Repr

/-- Closed under the state's own rule set: every rule whose full
    premise list sits in the seed set has its conclusion there too. -/
def Closed (s : State) : Prop :=
  ∀ r ∈ s.rules, (∀ p ∈ r.premises, p ∈ s.seeds) → r.conclusion ∈ s.seeds

/-- The three verdicts of every spine procedure: accept, refuse, or
    unknown. Unknown is a verdict, not the absence of one. -/
inductive Verdict where
  /-- The procedure accepts. -/
  | accept : Verdict
  /-- The procedure refuses. -/
  | refuse : Verdict
  /-- The procedure returns unknown. -/
  | unknown : Verdict
deriving DecidableEq, Repr

end Spine
end SoftwareIsQuantifiable
