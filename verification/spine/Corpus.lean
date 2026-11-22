/-
  The differential corpus for the delta group: obligations 7, 8, 9.

  Run with: lake env lean --run verification/spine/Corpus.lean

  The corpus is generated, not hand-picked case by case: parent
  states crossed with event sequences give the valid deltas; from
  their encodings come truncations, trailing-word extensions, and
  the reordered-event encodings; hand-built wrong-kind and
  count-mismatch byte strings are added. Checker triples include
  child roots differing in exactly one byte and parent roots
  differing in exactly one byte. Every case is a boolean check; the
  program prints the corpus size and a verdict, and exits nonzero
  on any disagreement.
-/

import SoftwareIsQuantifiable.Spine.Core
import SoftwareIsQuantifiable.Spine.Delta

open SoftwareIsQuantifiable.Spine

/-- The concrete hash used for the executable run: a rolling word
    hash plus the length. The theorems are about an arbitrary hash;
    the corpus runs this one. -/
def hashw (b : List Nat) : List Nat :=
  [b.foldl (fun a w => (a * 257 + w + 1) % 4294967296) 0, b.length]

/-- The tuple in force for the corpus: the base tuple of the delta
    module. -/
def tuplea : Tuple := base

/-- The control tuple for obligation 9: the base tuple with exactly
    one component changed (the checker version). -/
def tupleb : Tuple := ⟨1, 1, 2, 1, 1⟩

/-- Corpus parent states. -/
def states : List State :=
  [ ⟨[], [], 0, base⟩
  , ⟨[1, 2], [⟨[1], 2⟩], 3, base⟩
  , ⟨[7], [], 1, base⟩
  , ⟨[5, 5, 9], [⟨[5], 9⟩, ⟨[9, 5], 1⟩], 2, base⟩ ]

/-- Corpus event sequences: every kind, nestings, removals,
    restorations, and a version change under its own tuple. -/
def sequences : List (List Event) :=
  [ []
  , [.add 1]
  , [.add 1, .tomb 1]
  , [.tomb 9]
  , [.scope 4]
  , [.version base]
  , [.add 3, .revoke (.add 3)]
  , [.revoke (.tomb 2)]
  , [.revoke (.revoke (.add 5))]
  , [.add 2, .add 8, .tomb 2, .revoke (.tomb 8)]
  , [.scope 0, .version base, .add 4] ]

/-- Build the valid delta for a parent state and an event sequence,
    when the checked application succeeds. -/
def build (s : State) (es : List Event) : Option (State × Delta) :=
  (capply tuplea s es).map (fun s' => (s, ⟨root hashw s, es, root hashw s'⟩))

/-- All valid (parent state, delta) pairs of the corpus. -/
def pairs : List (State × Delta) :=
  states.flatMap (fun s => sequences.filterMap (build s))

/-- All valid deltas of the corpus. -/
def deltas : List Delta := pairs.map Prod.snd

/-- Change exactly the first byte of a root (or supply one byte
    where there was none). -/
def alter (b : List Nat) : List Nat :=
  match b with
  | [] => [0]
  | w :: rest => (w + 1) :: rest

/-- The semantics side of checker agreement, as a boolean: the
    parent root names the state, the checked application succeeds,
    the recomputed child root matches, and the child state's
    version declarations are the tuple in force. -/
def semform (s : State) (d : Delta) : Bool :=
  decide (d.parent = root hashw s) &&
    match capply tuplea s d.events with
    | none => false
    | some s' => decide (root hashw s' = d.child ∧ s'.vers = tuplea)

/-- Valid encodings. -/
def validbytes : List (List Nat) := deltas.map encdelta

/-- Corrupted encodings: truncations at two depths and a trailing
    extra word, for every valid encoding. -/
def corrupted : List (List Nat) :=
  validbytes.flatMap (fun b => [b.take (b.length - 1), b.take 1, b ++ [0]])

/-- Hand-built invalid byte strings: a wrong-kind tag, a truncated
    revocation, a count that overruns the events present, an event
    count with no event bytes, and a lone length word. -/
def handbuilt : List (List Nat) :=
  [[0, 0, 1, 9, 5], [0, 0, 1, 3], [0, 0, 2, 1, 5], [0, 0, 1, 1], [5], []]

/-- Every byte string the parser is tested on. -/
def allbytes : List (List Nat) := validbytes ++ corrupted ++ handbuilt

/-- Checker triples: the valid pairs, the same pairs with the child
    root altered in exactly one byte, the same pairs with the
    parent root altered in exactly one byte, and version-refusal
    deltas whose version change alters the tuple in force. -/
def triples : List (State × Delta) :=
  pairs ++
    pairs.map (fun (s, d) => (s, ⟨d.parent, d.events, alter d.child⟩)) ++
    pairs.map (fun (s, d) => (s, ⟨alter d.parent, d.events, d.child⟩)) ++
    states.map (fun s =>
      (s, ⟨root hashw s, [.version ⟨2, 1, 1, 1, 1⟩], [0]⟩))

/-- Parser round-trip cases: every valid delta parses back to
    itself, events, order, and roots intact. -/
def parsetests : List Bool :=
  deltas.map (fun d => decide (parse (encdelta d) = some d))

/-- Parser agreement cases over every byte string. -/
def agreetests : List Bool :=
  allbytes.map (fun b =>
    match parse b with
    | none => true
    | some d => decide (encdelta d = b))

/-- The hand-built invalid strings are all refused. -/
def nonetests : List Bool :=
  handbuilt.map (fun b => decide (parse b = none))

/-- Trailing extra words are refused. -/
def trailingtests : List Bool :=
  deltas.map (fun d => decide (parse (encdelta d ++ [0]) = none))

/-- Checker cases over every triple: the verdict is accept exactly
    when the semantics form holds — the executable differential
    agreement of obligation 8. -/
def checktests : List Bool :=
  triples.map (fun (s, d) =>
    decide (check hashw tuplea s d = Verdict.accept) = semform s d)

/-- Every valid pair is accepted. -/
def accepttests : List Bool :=
  pairs.map (fun (s, d) => decide (check hashw tuplea s d = Verdict.accept))

/-- A child root differing in exactly one byte is refused. -/
def childtests : List Bool :=
  pairs.map (fun (s, d) =>
    decide (check hashw tuplea s ⟨d.parent, d.events, alter d.child⟩ =
      Verdict.refuse))

/-- A parent root differing in exactly one byte returns unknown. -/
def parenttests : List Bool :=
  pairs.map (fun (s, d) =>
    decide (check hashw tuplea s ⟨alter d.parent, d.events, d.child⟩ =
      Verdict.unknown))

/-- Obligation 9 control cases: every accepted triple, re-presented
    with exactly one tuple component changed, is not accepted. -/
def tupletests : List Bool :=
  pairs.map (fun (s, d) =>
    decide (check hashw tupleb s d ≠ Verdict.accept))

/-- The recorded tuple is the tuple in force. -/
def recordedtests : List Bool :=
  pairs.map (fun (s, d) =>
    decide ((recorded hashw tuplea s d).2 = tuplea ∧
      (recorded hashw tupleb s d).2 = tupleb))

/-- Every test in the corpus. -/
def tests : List Bool :=
  parsetests ++ agreetests ++ nonetests ++ trailingtests ++
    checktests ++ accepttests ++ childtests ++ parenttests ++
    tupletests ++ recordedtests

/-- Run the corpus, print its size and verdict, and exit nonzero on
    any disagreement. -/
def main : IO UInt32 := do
  let total := tests.length
  let passed := (tests.filter (fun b => b)).length
  IO.println s!"valid pairs: {pairs.length}"
  IO.println s!"byte strings: {allbytes.length}"
  IO.println s!"checker triples: {triples.length}"
  IO.println s!"corpus {total} cases, {passed} passed"
  if passed = total then
    IO.println "PASS"
    return 0
  else
    IO.println "FAIL"
    return 1
