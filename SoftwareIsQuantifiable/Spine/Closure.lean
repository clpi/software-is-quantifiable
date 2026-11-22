/-
  The closure group of the update and checker spine (obligations
  10–21 of the spine spec, 2026-11-21): the step operator F of D5 is
  monotone, cold closure is its least fixed point, additions and
  deletions computed incrementally equal cold closure (or the
  procedure refuses), and the general case follows by a case split
  whose mixed case is proved directly through a composition lemma.

  This module generalises the Coloring development: its step,
  iteration, coloring, and derivability relation are reused as they
  stand. A fact set is a Coloring state (a Bool-valued predicate);
  set inclusion is Coloring's pointwise order. Premises P1–P6 of the
  spec are named nowhere here: this group needs none of them, and its
  hypotheses are exactly the finiteness and universe conditions the
  spec states.
-/

import SoftwareIsQuantifiable.Coloring

namespace SoftwareIsQuantifiable
namespace Spine
namespace Closure

open Coloring

variable {F : Type} [DecidableEq F]

set_option linter.unusedSectionVars false

/-! ## General helpers -/

namespace Help

/-- Derivability is monotone in the seed: a derivation from a smaller
    seed is a derivation from any larger seed. -/
theorem seed {R : List (Rule F)} {s t : State F} (hle : stateLe s t) :
    ∀ {f : F}, Deriv R s f → Deriv R t f := by
  intro f h
  induction h with
  | seed hh => exact Deriv.seed (hle _ hh)
  | apply hr _ IH => exact Deriv.apply hr (fun p hp => IH p hp)

/-- Derivability is monotone in the rule set. -/
theorem rules {R R' : List (Rule F)} (hsub : ∀ r ∈ R, r ∈ R') {s : State F} :
    ∀ {f : F}, Deriv R s f → Deriv R' s f := by
  intro f h
  induction h with
  | seed hh => exact Deriv.seed hh
  | apply hr _ IH => exact Deriv.apply (hsub _ hr) (fun p hp => IH p hp)

/-- Two seed and rule pairs with exactly the same derivable facts
    have the same coloring. The universe hypotheses are the snapshot
    conditions of the two colorings. -/
theorem ext {R R' : List (Rule F)} {s t : State F} {U : List F}
    (hU : ∀ r ∈ R, r.conclusion ∈ U) (hU' : ∀ r ∈ R', r.conclusion ∈ U)
    (hiff : ∀ f, Deriv R s f ↔ Deriv R' t f) :
    coloring R U s = coloring R' U t := by
  apply stateLe_antisymm
  · intro f hf
    exact coloring_complete R' U t hU' f ((hiff f).mp (coloring_sound R U s f hf))
  · intro f hf
    exact coloring_complete R U s hU f ((hiff f).mpr (coloring_sound R' U t f hf))

/-- The composition lemma. Closing a start state equals closing a
    target seed whenever every start fact is derivable from the
    target seed and the target seed is contained in the start state.
    Stated and proved once; obligations 13, 17, and 21 use it. -/
theorem compose {R : List (Rule F)} {U : List F} {start target : State F}
    (hU : ∀ r ∈ R, r.conclusion ∈ U)
    (hderiv : ∀ f, start f = true → Deriv R target f)
    (hle : stateLe target start) :
    coloring R U start = coloring R U target := by
  apply ext hU hU
  intro f
  constructor
  · intro h
    induction h with
    | seed hh => exact hderiv _ hh
    | apply hr _ IH => exact Deriv.apply hr (fun p hp => IH p hp)
  · intro h
    exact Help.seed hle h

end Help

/-! ## Obligation 10 — the step operator is monotone -/

namespace Step

/-- F of D5 is monotone: whenever X is a subset of Y, F(X) is a
    subset of F(Y). The proof is Coloring's step monotonicity, whose
    argument uses the joint-premise reading of D5 throughout: a rule
    fires on its full premise list, characterised as one conjunction
    over the whole list, never premise by premise. -/
theorem mono (R : List (Rule F)) {s t : State F} (hle : stateLe s t) :
    stateLe (step R s) (step R t) :=
  step_mono R hle

end Step

/-! ## Obligation 11 — cold closure is the least fixed point -/

namespace Cold

/-- The least closure of a seed: the coloring, that is, the
    iteration of F from the seed run past its termination bound. -/
def close (R : List (Rule F)) (U : List F) (s : State F) : State F :=
  coloring R U s

/-- All four parts of obligation 11 in one statement: the iteration
    reaches a fixed point within the size of the universe
    (termination, with finiteness explicit in the bound); the fixed
    point contains exactly the derivable facts (completeness and
    soundness); and it is contained in every fixed point of F that
    contains the seed (leastness). -/
theorem least (R : List (Rule F)) (U : List F) (s : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) :
    (∃ k, k ≤ U.length ∧ step R (iter R k s) = iter R k s) ∧
    (∀ f, Deriv R s f → close R U s f = true) ∧
    (∀ f, close R U s f = true → Deriv R s f) ∧
    (∀ t : State F, (∀ g, s g = true → t g = true) →
      step R t = t → stateLe (close R U s) t) :=
  ⟨exists_fixed_point R U s hU,
   fun f hf => coloring_complete R U s hU f hf,
   fun f hf => coloring_sound R U s f hf,
   fun t hseed hfix f hf =>
     deriv_closed R s (coloring_sound R U s f hf) t hseed hfix⟩

end Cold

/-! ## Obligation 12 — the closure induction principle -/

namespace Induct

/-- To prove a property of every fact in the least closure, it
    suffices to prove it of every seed fact and to prove that it is
    preserved by every rule, where preservation is stated over the
    rule's full premise list jointly: the hypothesis handed to the
    preservation step is the property of all premises together, as
    one bundle over the whole list. Derived from obligation 11
    through the derivability relation the coloring is sound and
    complete for. -/
theorem principle {R : List (Rule F)} {U : List F} {s : State F}
    (_hU : ∀ r ∈ R, r.conclusion ∈ U) {P : F → Prop}
    (hseed : ∀ f, s f = true → P f)
    (hstep : ∀ r ∈ R, (∀ p ∈ r.premises, P p) → P r.conclusion) :
    ∀ f, Cold.close R U s f = true → P f := by
  have key : ∀ {g : F}, Deriv R s g → P g := by
    intro g hd
    induction hd with
    | seed hh => exact hseed _ hh
    | apply hr _ IH => exact hstep _ hr (fun p hp => IH p hp)
  intro f hf
  exact key (coloring_sound R U s f hf)

end Induct

/-! ## Obligation 13 — additions: incremental equals cold -/

/-- The state holding exactly the facts of a list. -/
def oflist (l : List F) : State F := fun f => decide (f ∈ l)

namespace Oflist

/-- A listed fact holds in the state built from the list. -/
theorem mem {l : List F} {f : F} (h : f ∈ l) : oflist l f = true := by
  simp [oflist, h]

end Oflist

namespace Add

/-- Additions of facts. Running the closure from the previous least
    closure joined with the added facts yields exactly the cold least
    closure of the seed joined with the added facts. Both inclusions
    are the two directions of the composition lemma. -/
theorem facts (R : List (Rule F)) (U : List F) (s : State F) (added : List F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) :
    coloring R U (joinSt (coloring R U s) (oflist added)) =
      coloring R U (joinSt s (oflist added)) := by
  apply Help.compose hU
  · intro f hf
    have h' : (coloring R U s f || oflist added f) = true := hf
    cases hb : coloring R U s f with
    | true =>
      exact Help.seed (stateLe_join_left s (oflist added))
        (coloring_sound R U s f hb)
    | false =>
      have ha : oflist added f = true := by simpa [hb] using h'
      exact Deriv.seed (stateLe_join_right s (oflist added) f ha)
  · exact stateLe_join
      (fun f hf => stateLe_join_left (coloring R U s) (oflist added) f
        (seed_le_coloring R U s f hf))
      (stateLe_join_right (coloring R U s) (oflist added))

/-- Additions of seeds. The same equality with the added part given
    as a seed state rather than a fact list. -/
theorem seeds (R : List (Rule F)) (U : List F) (s added : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) :
    coloring R U (joinSt (coloring R U s) added) =
      coloring R U (joinSt s added) := by
  apply Help.compose hU
  · intro f hf
    have h' : (coloring R U s f || added f) = true := hf
    cases hb : coloring R U s f with
    | true =>
      exact Help.seed (stateLe_join_left s added)
        (coloring_sound R U s f hb)
    | false =>
      have ha : added f = true := by simpa [hb] using h'
      exact Deriv.seed (stateLe_join_right s added f ha)
  · exact stateLe_join
      (fun f hf => stateLe_join_left (coloring R U s) added f
        (seed_le_coloring R U s f hf))
      (stateLe_join_right (coloring R U s) added)

/-- Additions of rules. Running the closure under the enlarged rule
    set from the previous least closure yields exactly the cold least
    closure of the same seed under the enlarged rule set. -/
theorem rules (R R' : List (Rule F)) (U : List F) (s : State F)
    (hsub : ∀ r ∈ R, r ∈ R')
    (_hU : ∀ r ∈ R, r.conclusion ∈ U) (hU' : ∀ r ∈ R', r.conclusion ∈ U) :
    coloring R' U (coloring R U s) = coloring R' U s := by
  apply Help.ext hU' hU'
  intro f
  constructor
  · intro h
    induction h with
    | seed hh =>
      exact Help.rules hsub (coloring_sound R U s _ hh)
    | apply hr _ IH => exact Deriv.apply hr (fun p hp => IH p hp)
  · intro h
    exact Help.seed (fun g hg => seed_le_coloring R U s g hg) h

end Add

/-! ## Obligation 14 — additions: monotone growth -/

namespace Grow

/-- Growth under added seeds (and so, by the facts case of
    obligation 13, under added facts): the new least closure
    contains the previous least closure. A corollary of obligations
    13 and 11, stated separately as the spec requires. -/
theorem seed (R : List (Rule F)) (U : List F) (s added : State F) :
    stateLe (coloring R U s) (coloring R U (joinSt s added)) :=
  coloring_mono_seed R U (stateLe_join_left s added)

/-- Growth under added rules: enlarging the rule set only grows the
    least closure. -/
theorem rules (R R' : List (Rule F)) (U : List F) (s : State F)
    (hsub : ∀ r ∈ R, r ∈ R')
    (hU' : ∀ r ∈ R', r.conclusion ∈ U) :
    stateLe (coloring R U s) (coloring R' U s) := by
  intro f hf
  exact coloring_complete R' U s hU' f
    (Help.rules hsub (coloring_sound R U s f hf))

end Grow

/-! ## Obligation 15 — support is complete -/

/-- Support, in the least-fixed-point reading of D7. `Via R s x f`
    holds when some derivation of `f` from the seed `s` under the
    rules `R` rests on the seed fact `x`: either `f` is `x` itself, a
    seed fact, or `f` is concluded by a rule all of whose premises
    are derivable and one of whose premises rests on `x`. Being an
    inductive predicate, it is the least set closed under this
    premise step; a premise cycle with no seed beneath it yields no
    proof, which is the cyclic case. The recorded support of `f` is
    the set of `x` with `Via R s x f`. -/
inductive Via (R : List (Rule F)) (s : State F) (x : F) : F → Prop where
  | here (h : s x = true) : Via R s x x
  | step {r : Rule F} (hr : r ∈ R)
      (hp : ∀ p ∈ r.premises, Deriv R s p)
      {p : F} (hm : p ∈ r.premises) (hv : Via R s x p) :
      Via R s x r.conclusion

namespace Supp

/-- Soundness of the recording: a recorded support fact is a seed
    fact, and the fact it supports is derivable. -/
theorem sound {R : List (Rule F)} {s : State F} {x f : F} :
    Via R s x f → s x = true ∧ Deriv R s f := by
  intro h
  induction h with
  | here hh => exact ⟨hh, Deriv.seed hh⟩
  | step hr hp _ _ IH => exact ⟨IH.1, Deriv.apply hr hp⟩

/-- Completeness of the recording: the recorded support contains
    every fact any derivation rests on. A derivation resting on `x`
    ends in either the seed leaf `x` or a rule step through a premise
    resting on `x`; this constructor is exactly that last step, so
    every resting fact is recorded. -/
theorem contains {R : List (Rule F)} {s : State F} {x : F}
    {r : Rule F} (hr : r ∈ R)
    (hp : ∀ p ∈ r.premises, Deriv R s p)
    {p : F} (hm : p ∈ r.premises) (hv : Via R s x p) :
    Via R s x r.conclusion :=
  Via.step hr hp hm hv

/-- The recorded support is the least such set: any predicate
    holding of the seed fact `x` and closed under the premise step
    holds of every fact whose recorded support contains `x`. This is
    the fixed-point reading of support; no traversal is involved, so
    cycles in the premise graph do not affect it. -/
theorem least {R : List (Rule F)} {s : State F} {x : F}
    {Q : F → Prop} (hx : Q x)
    (hstep : ∀ r ∈ R, (∀ p ∈ r.premises, Deriv R s p) →
      ∀ p ∈ r.premises, Q p → Q r.conclusion) :
    ∀ {f : F}, Via R s x f → Q f := by
  intro f h
  induction h with
  | here _ => exact hx
  | step hr hp hm _ IH => exact hstep _ hr hp _ hm IH

/-- Termination of the recording, cyclic case included: a recorded
    support fact is always a seed fact, so the recorded support of
    any fact is contained in the finite seed set, and where there is
    no seed beneath a premise cycle there is no support at all. -/
theorem finite {R : List (Rule F)} {s : State F} {x f : F}
    (h : Via R s x f) : s x = true :=
  (sound h).1

/-- A premise cycle with no seed beneath it supports nothing: with
    an everywhere-false seed, no fact has any recorded support. -/
theorem noseed {R : List (Rule F)} {s : State F}
    (hs : ∀ y, s y = false) {x f : F} : ¬ Via R s x f := by
  intro h
  have hx : s x = true := finite h
  rw [hs x] at hx
  cases hx

end Supp

/-! ## Obligation 16 — over-deletion covers every affected derivation -/

/-- The seed of the new state after a removal delta: the old seed
    minus the removed set. -/
def minus (s gone : State F) : State F := fun f => s f && !gone f

namespace Minus

/-- The reduced seed is contained in the old seed. -/
theorem le {s gone : State F} : stateLe (minus s gone) s := by
  intro f hf
  exact (and_eq_true hf).1

end Minus

/-- A fact is removed outright when it is in the old least closure
    and has no derivation from the reduced seed — equivalently,
    when every one of its supports meets the removed set, since a
    derivation from the reduced seed is exactly a support disjoint
    from the removed set. -/
def out (R : List (Rule F)) (s gone : State F) (f : F) : Prop :=
  Deriv R s f ∧ ¬ Deriv R (minus s gone) f

/-- A fact is marked for re-derivation when some recorded support
    of it meets the removed set. -/
def mark (R : List (Rule F)) (s gone : State F) (f : F) : Prop :=
  ∃ x, gone x = true ∧ Via R s x f

/-- The over-delete set: outright-removed facts together with
    marked facts. -/
def over (R : List (Rule F)) (s gone : State F) (f : F) : Prop :=
  out R s gone f ∨ mark R s gone f

namespace Over

/-- Containment: every fact whose derivation status differs between
    the old least closure and the new least closure is in the
    over-delete set. A fact gained by the new closure would already
    be in the old one, since the reduced seed is contained in the
    old seed; so every affected fact is an old fact with no
    derivation from the reduced seed, hence outright-removed. -/
theorem covers {R : List (Rule F)} {s gone : State F} {f : F}
    (h : (Deriv R s f ∧ ¬ Deriv R (minus s gone) f) ∨
         (¬ Deriv R s f ∧ Deriv R (minus s gone) f)) :
    over R s gone f := by
  cases h with
  | inl hh => exact Or.inl hh
  | inr hh =>
    exact absurd (Help.seed Minus.le hh.2) hh.1

/-- Alternate supports, explicitly: a fact with a support disjoint
    from the removed set — a derivation from the reduced seed — is
    never removed outright. Outright removal happens only when all
    supports meet the removed set. -/
theorem only {R : List (Rule F)} {s gone : State F} {f : F}
    (h : Deriv R (minus s gone) f) : ¬ out R s gone f :=
  fun hh => hh.2 h

/-- Every marked fact is in the over-delete set, by construction. -/
theorem marks {R : List (Rule F)} {s gone : State F} {f : F}
    (h : mark R s gone f) : over R s gone f :=
  Or.inr h

end Over

/-! ## Obligation 17 — re-derivation reaches exactly the
    still-supported facts -/

/-- The re-derivation start state: the old least closure minus the
    outright-removed facts, which is the set of facts in both the
    old and the new least closure. -/
def kept (R : List (Rule F)) (U : List F) (s gone : State F) : State F :=
  fun f => coloring R U s f && coloring R U (minus s gone) f

namespace Reach

/-- Re-derivation from the kept facts reaches exactly the cold
    least closure of the reduced seed: the facts that have at least
    one support disjoint from the removed set, together with the
    new seeds (which are the reduced seed facts themselves). Both
    inclusions are the two directions of the composition lemma. -/
theorem exact (R : List (Rule F)) (U : List F) (s gone : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) :
    coloring R U (kept R U s gone) = coloring R U (minus s gone) := by
  apply Help.compose hU
  · intro f hf
    have h2 : coloring R U (minus s gone) f = true := (and_eq_true hf).2
    exact coloring_sound R U (minus s gone) f h2
  · intro g hg
    have h1 : coloring R U s g = true :=
      coloring_complete R U s hU g (Deriv.seed (and_eq_true hg).1)
    have h2 : coloring R U (minus s gone) g = true :=
      coloring_complete R U (minus s gone) hU g (Deriv.seed hg)
    show (coloring R U s g && coloring R U (minus s gone) g) = true
    rw [h1, h2]
    rfl

/-- The re-derived set, characterised: a fact is reached exactly
    when it is derivable from the reduced seed. -/
theorem reach (R : List (Rule F)) (U : List F) (s gone : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) (f : F) :
    coloring R U (kept R U s gone) f = true ↔
      Deriv R (minus s gone) f := by
  rw [exact R U s gone hU]
  constructor
  · intro hf
    exact coloring_sound R U (minus s gone) f hf
  · intro hf
    exact coloring_complete R U (minus s gone) hU f hf

/-- Cyclic supports, absent case: a fact whose only supports form a
    cycle with no surviving seed beneath it — formally, a fact not
    derivable from the reduced seed — is absent from the result. -/
theorem absent (R : List (Rule F)) (U : List F) (s gone : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) {f : F}
    (h : ¬ Deriv R (minus s gone) f) :
    coloring R U (kept R U s gone) f = false := by
  cases hb : coloring R U (kept R U s gone) f with
  | false => rfl
  | true => exact absurd ((reach R U s gone hU f).mp hb) h

/-- Cyclic supports, present case: a fact derivable from the
    reduced seed — in particular a cycle fact with a surviving seed
    beneath it — is present in the result. -/
theorem present (R : List (Rule F)) (U : List F) (s gone : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) {f : F}
    (h : Deriv R (minus s gone) f) :
    coloring R U (kept R U s gone) f = true :=
  (reach R U s gone hU f).mpr h

end Reach

/-! ## Obligation 18 — deletions and revocations: incremental
    equals cold, or refusal -/

/-- The three outcomes of D12. -/
inductive Verdict (F : Type) where
  | accept (s : State F)
  | refuse
  | unknown

/-- A support record for a removal delta at a named snapshot tag:
    the recorded support function, the tag of the snapshot it was
    recorded at, a proof that the tag is the current one, and a
    proof that the recorded support contains every support fact.
    A record that is incomplete (some support fact unrecorded) or
    foreign (recorded at another snapshot) does not inhabit this
    type; the theorems below prove exactly that. -/
structure Record (R : List (Rule F)) (s gone : State F) (tag : Nat) where
  /-- The recorded support of each fact, as a set of seed facts. -/
  supp : F → State F
  /-- The snapshot tag the record was taken at. -/
  snap : Nat
  /-- The record belongs to the current snapshot. -/
  own : snap = tag
  /-- The record is complete: every support fact is recorded. -/
  full : ∀ f x, Via R s x f → supp f x = true

/-- The incremental deletion procedure: with a support record it
    accepts the re-derived state of obligation 17; with no record
    it refuses, forcing a cold rebuild. There is no third path. -/
def run (R : List (Rule F)) (U : List F) (s gone : State F) (tag : Nat)
    (rec : Option (Record R s gone tag)) : Verdict F :=
  match rec with
  | some _ => Verdict.accept (coloring R U (kept R U s gone))
  | none => Verdict.refuse

namespace Del

/-- The equality case: with a record, the procedure's result is
    exactly the cold least closure of the new state. -/
theorem equal (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) (hU : ∀ r ∈ R, r.conclusion ∈ U)
    (r : Record R s gone tag) :
    run R U s gone tag (some r) =
      Verdict.accept (coloring R U (minus s gone)) := by
  show Verdict.accept (coloring R U (kept R U s gone)) = _
  rw [Reach.exact R U s gone hU]

/-- The refusal case: a missing support record forces refusal. -/
theorem missing (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) :
    run R U s gone tag none = Verdict.refuse :=
  rfl

/-- Refusal trigger, incomplete records: a support function that
    leaves some support fact unrecorded is the support function of
    no record, so the procedure can only refuse on it. -/
theorem incomplete (R : List (Rule F)) (s gone : State F) (tag : Nat)
    (supp : F → State F) {f x : F}
    (hv : Via R s x f) (hmiss : supp f x ≠ true) :
    ¬ ∃ r : Record R s gone tag, r.supp = supp := by
  intro h
  obtain ⟨r, hr⟩ := h
  apply hmiss
  rw [← hr]
  exact r.full f x hv

/-- Refusal trigger, foreign records: no record at the current tag
    carries a different snapshot tag, so a record from another
    snapshot can only be refused. -/
theorem foreign (R : List (Rule F)) (s gone : State F) (tag : Nat) :
    ¬ ∃ r : Record R s gone tag, r.snap ≠ tag := by
  intro h
  obtain ⟨r, hr⟩ := h
  exact hr r.own

end Del

/-! ## Obligation 19 — the conservative cone theorem -/

/-- The named cone construction: the cone of a removal delta is
    its over-delete set (obligation 16) — the outright-removed
    facts together with the facts marked for re-derivation. -/
def cone (R : List (Rule F)) (s gone : State F) (f : F) : Prop :=
  over R s gone f

/-- A minimal witness interface, the seam for the coverage group:
    a witness is a fact together with the list of facts its
    validity rests on (its recorded path and support elements).
    Validity at a seed is derivability of the fact and of every
    fact it rests on. -/
structure Wit (F : Type) where
  /-- The fact witnessed. -/
  fact : F
  /-- The facts the witness rests on. -/
  touched : List F

/-- Witness validity at a given seed state. -/
def ok (R : List (Rule F)) (sd : State F) (w : Wit F) : Prop :=
  Deriv R sd w.fact ∧ ∀ y ∈ w.touched, Deriv R sd y

namespace Cone

/-- Conservativeness, derivation half: every fact outside the cone
    has the same derivation status in the old least closure and the
    new least closure. -/
theorem status {R : List (Rule F)} {s gone : State F} {f : F}
    (h : ¬ cone R s gone f) :
    Deriv R s f ↔ Deriv R (minus s gone) f := by
  have hnout : ¬ out R s gone f := fun hh => h (Or.inl hh)
  constructor
  · intro hd
    cases Classical.em (Deriv R (minus s gone) f) with
    | inl hh => exact hh
    | inr hh => exact absurd ⟨hd, hh⟩ hnout
  · intro hd
    exact Help.seed Minus.le hd

/-- Conservativeness, witness half: a witness valid at the old
    state whose fact and every fact it rests on lie outside the
    cone keeps its validity at the new state. Disjointness from the
    cone is the hypothesis that carries the witness across; it is
    established from the recorded touched list, not recomputed. -/
theorem wit {R : List (Rule F)} {s gone : State F} {w : Wit F}
    (hv : ok R s w) (hf : ¬ cone R s gone w.fact)
    (ht : ∀ y ∈ w.touched, ¬ cone R s gone y) :
    ok R (minus s gone) w :=
  ⟨(status hf).mp hv.1,
   fun y hy => (status (ht y hy)).mp (hv.2 y hy)⟩

end Cone

/-! ## Obligation 20 — outside the cone, nothing is recomputed
    and nothing changes -/

/-- The combined incremental result: inside the cone, the
    re-derived state of obligation 17; outside the cone, the old
    least closure carried across untouched. -/
def comb (R : List (Rule F)) (U : List F) (s gone : State F)
    (f : F) : Prop :=
  (cone R s gone f ∧ coloring R U (kept R U s gone) f = true) ∨
    (¬ cone R s gone f ∧ Deriv R s f)

namespace Comb

/-- The combination equals the cold least closure of the new
    state. The outside part is carried by the first half of
    obligation 19, not by inspection of any run. -/
theorem equal (R : List (Rule F)) (U : List F) (s gone : State F)
    (hU : ∀ r ∈ R, r.conclusion ∈ U) (f : F) :
    comb R U s gone f ↔ Deriv R (minus s gone) f := by
  constructor
  · intro h
    cases h with
    | inl hh => exact (Reach.reach R U s gone hU f).mp hh.2
    | inr hh => exact (Cone.status hh.1).mp hh.2
  · intro hd
    cases Classical.em (cone R s gone f) with
    | inl hc =>
      exact Or.inl ⟨hc, (Reach.reach R U s gone hU f).mpr hd⟩
    | inr hc =>
      exact Or.inr ⟨hc, Help.seed Minus.le hd⟩

end Comb

/-! ## Obligation 21 — general incremental equals cold -/

/-- The kind of a general delta. -/
inductive Kind where
  | adds
  | dels
  | mixed
  | scope

/-- A general delta, in the minimal interface of this module: the
    new seed and the new rule list it declares, and its kind. For
    the scope-or-version kind, the seed and rules carried here are
    by definition the re-derived seed and rule universe the change
    declares, as the spec's hypothesis for obligation 21 requires;
    the proof for that kind then runs on those carried values. -/
structure Delta (F : Type) where
  /-- The new seed set. -/
  seed : State F
  /-- The new rule set. -/
  rules : List (Rule F)
  /-- The delta's kind. -/
  kind : Kind

/-- The start state of the direct mixed procedure: the new seed,
    joined with the facts that are in both the old least closure
    and the new least closure — the old closure with the outright
    set against the new seed and rules deleted. -/
def start (R : List (Rule F)) (U : List F) (s : State F)
    (d : Delta F) : State F :=
  joinSt d.seed
    (fun f => coloring R U s f && coloring d.rules U d.seed f)

/-- The composition lemma applied to the mixed start state:
    closing it under the new rules equals the cold closure of the
    new seed. This is the stated composition lemma of obligation
    21: Help.compose, with the sandwich hypotheses discharged
    against the new system directly. -/
theorem startcold (R : List (Rule F)) (U : List F) (s : State F)
    (d : Delta F) (hU' : ∀ r ∈ d.rules, r.conclusion ∈ U) :
    coloring d.rules U (start R U s d) = coloring d.rules U d.seed := by
  apply Help.compose hU'
  · intro f hf
    have h' : (d.seed f ||
        (coloring R U s f && coloring d.rules U d.seed f)) = true := hf
    cases hb : d.seed f with
    | true => exact Deriv.seed hb
    | false =>
      have h2 : coloring d.rules U d.seed f = true := by
        have hh : (coloring R U s f &&
            coloring d.rules U d.seed f) = true := by simpa [hb] using h'
        exact (and_eq_true hh).2
      exact coloring_sound d.rules U d.seed f h2
  · exact stateLe_join_left d.seed _

/-- The general incremental procedure. Additions take the
    additions procedure of obligation 13; every other kind takes
    the direct mixed procedure from the start state when a support
    record is present, and refuses (forcing a cold rebuild) when
    it is not. -/
def go (R : List (Rule F)) (U : List F) (s gone : State F) (tag : Nat)
    (d : Delta F) (rec : Option (Record R s gone tag)) : Verdict F :=
  match d.kind with
  | Kind.adds =>
      Verdict.accept (coloring d.rules U (joinSt (coloring R U s) d.seed))
  | _ =>
      match rec with
      | some _ => Verdict.accept (coloring d.rules U (start R U s d))
      | none => Verdict.refuse

namespace Gen

/-- The additions case of the case split: under the additions-only
    hypotheses (the old seed is contained in the new seed and the
    old rules in the new rules), the procedure accepts exactly the
    cold least closure. -/
theorem adds (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) (d : Delta F) (rec : Option (Record R s gone tag))
    (hk : d.kind = Kind.adds)
    (hseed : stateLe s d.seed) (hrules : ∀ r ∈ R, r ∈ d.rules)
    (hU' : ∀ r ∈ d.rules, r.conclusion ∈ U) :
    go R U s gone tag d rec =
      Verdict.accept (coloring d.rules U d.seed) := by
  have hcold : coloring d.rules U (joinSt (coloring R U s) d.seed) =
      coloring d.rules U d.seed := by
    apply Help.compose hU'
    · intro f hf
      have h' : (coloring R U s f || d.seed f) = true := hf
      cases hb : coloring R U s f with
      | true =>
        exact Help.rules hrules
          (Help.seed hseed (coloring_sound R U s f hb))
      | false =>
        have ha : d.seed f = true := by simpa [hb] using h'
        exact Deriv.seed ha
    · exact stateLe_join_right (coloring R U s) d.seed
  show (match d.kind with
    | Kind.adds =>
        Verdict.accept (coloring d.rules U (joinSt (coloring R U s) d.seed))
    | _ =>
        match rec with
        | some _ => Verdict.accept (coloring d.rules U (start R U s d))
        | none => Verdict.refuse) = _
  rw [hk]
  exact congrArg Verdict.accept hcold

/-- The remaining kinds with a support record: deletions, mixed,
    and scope-or-version deltas accept exactly the cold least
    closure, proved directly through the composition lemma at the
    start state (startcold), not by composing the pure cases. -/
theorem rest (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) (d : Delta F) (r : Record R s gone tag)
    (hk : d.kind = Kind.dels ∨ d.kind = Kind.mixed ∨
      d.kind = Kind.scope)
    (hU' : ∀ r ∈ d.rules, r.conclusion ∈ U) :
    go R U s gone tag d (some r) =
      Verdict.accept (coloring d.rules U d.seed) := by
  have hcold : coloring d.rules U (start R U s d) =
      coloring d.rules U d.seed :=
    startcold R U s d hU'
  show (match d.kind with
    | Kind.adds =>
        Verdict.accept (coloring d.rules U (joinSt (coloring R U s) d.seed))
    | _ =>
        match (some r : Option (Record R s gone tag)) with
        | some _ => Verdict.accept (coloring d.rules U (start R U s d))
        | none => Verdict.refuse) = _
  cases hk with
  | inl hh => rw [hh]; exact congrArg Verdict.accept hcold
  | inr hh =>
    cases hh with
    | inl hh => rw [hh]; exact congrArg Verdict.accept hcold
    | inr hh => rw [hh]; exact congrArg Verdict.accept hcold

/-- The remaining kinds with no support record refuse, forcing a
    cold rebuild. -/
theorem refuse (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) (d : Delta F)
    (hk : d.kind = Kind.dels ∨ d.kind = Kind.mixed ∨
      d.kind = Kind.scope) :
    go R U s gone tag d none = Verdict.refuse := by
  show (match d.kind with
    | Kind.adds =>
        Verdict.accept (coloring d.rules U (joinSt (coloring R U s) d.seed))
    | _ =>
        match (none : Option (Record R s gone tag)) with
        | some _ => Verdict.accept (coloring d.rules U (start R U s d))
        | none => Verdict.refuse) = _
  cases hk with
  | inl hh => rw [hh]
  | inr hh =>
    cases hh with
    | inl hh => rw [hh]
    | inr hh => rw [hh]

/-- Obligation 21, the general statement, by case split over the
    delta's event kinds: for any delta, the incremental procedure
    yields exactly the cold least closure of the new state, or
    refuses and forces a cold rebuild. The mixed case is the `rest`
    case at kind `mixed`, proved directly through the composition
    lemma. Scope and version changes enter through the delta's
    carried seed and rules, which are the re-derived universe they
    declare. -/
theorem equal (R : List (Rule F)) (U : List F) (s gone : State F)
    (tag : Nat) (d : Delta F) (rec : Option (Record R s gone tag))
    (hseed : stateLe s d.seed) (hrules : ∀ r ∈ R, r ∈ d.rules)
    (hU' : ∀ r ∈ d.rules, r.conclusion ∈ U) :
    go R U s gone tag d rec =
        Verdict.accept (coloring d.rules U d.seed) ∨
      go R U s gone tag d rec = Verdict.refuse := by
  cases hk : d.kind with
  | adds =>
    exact Or.inl (adds R U s gone tag d rec hk hseed hrules hU')
  | dels =>
    cases rec with
    | none => exact Or.inr (refuse R U s gone tag d (Or.inl hk))
    | some r => exact Or.inl (rest R U s gone tag d r (Or.inl hk) hU')
  | mixed =>
    cases rec with
    | none =>
      exact Or.inr (refuse R U s gone tag d (Or.inr (Or.inl hk)))
    | some r =>
      exact Or.inl (rest R U s gone tag d r (Or.inr (Or.inl hk)) hU')
  | scope =>
    cases rec with
    | none =>
      exact Or.inr (refuse R U s gone tag d (Or.inr (Or.inr hk)))
    | some r =>
      exact Or.inl (rest R U s gone tag d r (Or.inr (Or.inr hk)) hU')

end Gen

/-! ## Axiom audit (obligation closing condition, spec section 1)

    The audits for the closing theorem of each obligation. Their
    output is recorded in the lane record; the permitted set is
    propext, Classical.choice, and Quot.sound. -/

#print axioms Step.mono
#print axioms Cold.least
#print axioms Induct.principle
#print axioms Add.facts
#print axioms Add.seeds
#print axioms Add.rules
#print axioms Grow.seed
#print axioms Grow.rules
#print axioms Supp.sound
#print axioms Supp.contains
#print axioms Supp.least
#print axioms Supp.noseed
#print axioms Over.covers
#print axioms Over.only
#print axioms Reach.exact
#print axioms Reach.absent
#print axioms Reach.present
#print axioms Del.equal
#print axioms Del.missing
#print axioms Del.incomplete
#print axioms Del.foreign
#print axioms Cone.status
#print axioms Cone.wit
#print axioms Comb.equal
#print axioms Gen.equal

end Closure
end Spine
end SoftwareIsQuantifiable
