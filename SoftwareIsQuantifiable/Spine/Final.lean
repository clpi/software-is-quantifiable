/- The end-to-end group of the update/checker spine: obligations
   33 and 34. The checker decomposition and the end-to-end theorem,
   composed from the delta group (obligations 1–9), the closure
   group (obligations 10–21), and the coverage group (obligations
   22–32), all at this one pin. -/

import SoftwareIsQuantifiable.Spine.Delta
import SoftwareIsQuantifiable.Spine.Sense

namespace SoftwareIsQuantifiable
namespace Spine
namespace Final

/-- One step of a certificate's chain: a named parent state, the
    delta, and a named child state. The states are named, not
    merely rooted — the checker of the delta group works at a
    supplied state, and the chain binds the named child to the
    checked application. -/
structure Step where
  /-- The parent state of the step. -/
  parent : State
  /-- The delta applied at this step. -/
  delta : Delta
  /-- The child state of the step. -/
  child : State

/-- The step test: the delta's parent root is the named parent
    state's root, the checked application of the delta to the
    named parent yields exactly the named child, the child's
    recomputed root is the delta's child root, and the child's
    version declarations are the tuple in force. -/
def stepb (h : List Nat → List Nat) (t : Tuple) (s : Step) : Bool :=
  decide (s.delta.parent = root h s.parent ∧
    capply t s.parent s.delta.events = some s.child ∧
    root h s.child = s.delta.child ∧ s.child.vers = t)

/-- The step test is exactly its four components. -/
theorem stepb_iff {h : List Nat → List Nat} {t : Tuple} {s : Step} :
    stepb h t s = true ↔ s.delta.parent = root h s.parent ∧
      capply t s.parent s.delta.events = some s.child ∧
      root h s.child = s.delta.child ∧ s.child.vers = t := by
  simp only [stepb, decide_eq_true_eq]

/-- The step test decomposes through the delta group's checker:
    the checker accepts the step at the named parent, and the
    named child is the checked application's result. Acceptance
    under obligations 8 and 9 is what the first component is; the
    second is the chain's own binding of the named states. -/
theorem stepb_check {h : List Nat → List Nat} {t : Tuple}
    {s : Step} :
    stepb h t s = true ↔
      check h t s.parent s.delta = Verdict.accept ∧
        capply t s.parent s.delta.events = some s.child := by
  rw [stepb_iff, checkaccept]
  constructor
  · intro hcon
    exact ⟨⟨hcon.1, s.child, hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩,
      hcon.2.1⟩
  · intro hcon
    obtain ⟨⟨hp, s', hcap, hroot, hvers⟩, hcap'⟩ := hcon
    have hsub : s' = s.child := cdet hcap hcap'
    subst hsub
    exact ⟨hp, hcap', hroot, hvers⟩

/-- The linking test: every step's named child is the next step's
    named parent, checked over the zipped consecutive pairs. -/
def linkb (steps : List Step) : Bool :=
  (steps.zip steps.tail).all
    (fun p => decide (p.1.child = p.2.parent))

/-- The linking predicate: every consecutive pair links. -/
def Linked (steps : List Step) : Prop :=
  ∀ p ∈ steps.zip steps.tail, p.1.child = p.2.parent

/-- The linking test is exactly the linking predicate. -/
theorem linkb_iff {steps : List Step} :
    linkb steps = true ↔ Linked steps := by
  simp only [linkb, Linked, List.all_eq_true, decide_eq_true_eq]

/-- The chain test: every step passes the step test under the one
    tuple in force, and the steps link. -/
def chainb (h : List Nat → List Nat) (t : Tuple)
    (steps : List Step) : Bool :=
  steps.all (stepb h t) && linkb steps

/-- The state a chain reaches from its first state: the last
    step's named child, or the first state when there are no
    steps. -/
def endstate (first : State) (steps : List Step) : State :=
  steps.foldl (fun _ s => s.child) first

/-- A certificate: one version tuple in force, a chain from
    snapshot 0, the final snapshot's full record (state and sensor
    side together), the named qualified set, and the witnesses the
    certificate relies on. -/
structure Cert where
  /-- The version tuple in force for the whole certificate. -/
  tuple : Tuple
  /-- Snapshot 0's state. -/
  first : State
  /-- The chain of steps from snapshot 0 to snapshot k. -/
  steps : List Step
  /-- Snapshot k: the state the chain reaches, with its sensor
      records. -/
  snap : Sense.Snap
  /-- The named qualified set. -/
  q : List Nat
  /-- The witnesses the certificate relies on. -/
  wits : List Sense.Wit

/-- The end-to-end checker: the chain passes under the one tuple,
    the final snapshot's state is the state the chain reaches, the
    named set is exactly the cold closure enumeration of the final
    snapshot (the filter of its declared fact universe by the
    decidable least closure), and every relied-on witness passes
    the coverage check at the final snapshot. One snapshot, one
    tuple, one root function throughout. -/
def verify (h : List Nat → List Nat) (c : Cert) : Bool :=
  chainb h c.tuple c.steps &&
    decide (c.snap.state = endstate c.first c.steps) &&
    decide (c.q = (Sense.facts c.snap).filter
      (fun f => Sense.leastb c.snap f)) &&
    c.wits.all (fun w => Sense.check h c.snap w)

/-- Obligation 33 — checker acceptance decomposes. The checker
    accepts a certificate if and only if all of the following hold
    of the same certificate, the same final snapshot, and the same
    tuple in force: every chain step is the byte-exact transition
    at its named states under that tuple (section 2, through
    obligations 3, 8, and 9); the steps link into one chain
    reaching the final snapshot's state; the named set is the cold
    closure enumeration of the final snapshot (the production
    equality of section 3, obligations 20 and 21, is what licenses
    checking the named set against cold closure however it was
    produced); and every relied-on witness passes section 4 at the
    final snapshot. Because acceptance is this conjunction
    evaluated at one certificate, acceptance with components drawn
    from different snapshots, roots, or tuples is impossible, not
    merely unobserved: there is no second snapshot, root, or tuple
    in the check to draw them from. -/
theorem verify_iff {h : List Nat → List Nat} {c : Cert} :
    verify h c = true ↔
      ((((∀ s ∈ c.steps, s.delta.parent = root h s.parent ∧
        capply c.tuple s.parent s.delta.events = some s.child ∧
        root h s.child = s.delta.child ∧
        s.child.vers = c.tuple) ∧
      Linked c.steps) ∧
      c.snap.state = endstate c.first c.steps) ∧
      c.q = (Sense.facts c.snap).filter
        (fun f => Sense.leastb c.snap f)) ∧
      ∀ w ∈ c.wits, Sense.check h c.snap w = true := by
  simp only [verify, chainb, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, stepb_iff, linkb_iff]

/-- The chain component of an accepted certificate, read through
    section 2's predicate: every step's delta is a valid delta
    under the tuple in force. -/
theorem verify_valid {h : List Nat → List Nat} {c : Cert}
    (hv : verify h c = true) :
    ∀ s ∈ c.steps, ValidDelta h c.tuple s.delta := by
  intro s hs
  have hsteps := ((verify_iff).1 hv).1.1.1.1 s hs
  exact ⟨s.parent, s.child, hsteps.1.symm, hsteps.2.1,
    hsteps.2.2.1, hsteps.2.2.2⟩

/-- Every fact of the least closure lies in the declared fact
    universe, by induction on its derivation: seeds are in the
    universe's seed part, conclusions in its rule part. -/
theorem least_mem_facts {snap : Sense.Snap} {f : Nat}
    (hf : Sense.Least snap f) : f ∈ Sense.facts snap := by
  induction hf with
  | seed hh =>
    rename_i q
    have hq : decide (q ∈ snap.state.seeds) = true := hh
    exact List.mem_append.2 (Or.inl (of_decide_eq_true hq))
  | apply hr hp IH =>
    rename_i r
    obtain ⟨r₀, hr₀, hreq⟩ := List.mem_map.1 hr
    have hcon : r.conclusion = r₀.conclusion :=
      congrArg Coloring.Rule.conclusion hreq.symm
    rw [hcon]
    exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨r₀, hr₀,
      List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))⟩))

/-- Obligation 34 — the end-to-end theorem. If the checker accepts
    certificate k, then (a) the qualified set of certificate k
    equals the least closure of snapshot k, as a membership
    equivalence over facts; and the relied-on witnesses are
    receipts at snapshot k. Part (a) is composed of obligation
    33's set component with the coverage group's agreement of the
    decidable least closure with derivability (the cold closure
    being the least fixed point is obligation 11, and the
    production equality of obligation 21 is what makes the cold
    check the right check for an incrementally produced set).
    Premises: the statement is at the checker's supplied states,
    exactly as obligation 8 landed; the root-only reading of the
    chain enters through premise P2 at the delta group's agreement
    theorem, and no other premise is consumed by this part. -/
theorem final {h : List Nat → List Nat} {c : Cert}
    (hv : verify h c = true) :
    (∀ f, f ∈ c.q ↔ Sense.Least c.snap f) ∧
      ∀ w ∈ c.wits, Sense.Receipt h c.snap w := by
  have hq := ((verify_iff).1 hv).1.2
  refine ⟨fun f => ?_, fun w hw => ((verify_iff).1 hv).2 w hw⟩
  rw [hq]
  constructor
  · intro hf
    have hf' := List.mem_filter.1 hf
    exact (Sense.leastb_iff).1 hf'.2
  · intro hf
    exact List.mem_filter.2
      ⟨least_mem_facts hf, (Sense.leastb_iff).2 hf⟩

/-- Obligation 34, part (b): under the coverage hypotheses of
    obligation 27 for snapshot k — every seed of snapshot k
    observed at snapshot k, and every rule of snapshot k carrying
    observed premises to an observed conclusion — every fact of
    the qualified set is covered at snapshot k in the sense of
    obligation 27: it has a receipt at snapshot k. These two
    hypotheses are where the sensor premises enter this part: the
    seed hypothesis is observation by deployed, healthy, faithful
    sensors with mediation paths in snapshot k (premises P5 and
    P6 are the health and fidelity evidence those observations
    rest on, carried as snapshot k's own records and never
    discharged), and the rule hypothesis is preservation along
    snapshot k's own rules. -/
theorem final_covered {h : List Nat → List Nat} {c : Cert}
    (hv : verify h c = true)
    (hseed : ∀ f ∈ c.snap.state.seeds, Sense.Observed c.snap f)
    (hpres : ∀ r ∈ c.snap.state.rules,
      (∀ p ∈ r.premises, Sense.Observed c.snap p) →
        Sense.Observed c.snap r.conclusion) :
    ∀ f, f ∈ c.q → ∃ w, w.fact = f ∧ Sense.Receipt h c.snap w :=
  fun f hf => Sense.covered_of_preserved hseed hpres f
    (((final hv).1 f).1 hf)

/-- The control certificate: the delta group's own model step,
    from its parent state to its child state, with the final
    snapshot built on the child state, the qualified set the cold
    closure enumeration of that state, and no relied-on
    witnesses. -/
def certone : Cert where
  tuple := base
  first := pstate
  steps := [{ parent := pstate, delta := dmodel, child := cstate }]
  snap := { state := cstate, edges := [], deploys := [], healthy := [], faithful := [], places := [], sites := [1, 2], now := 0 }
  q := [1, 1, 2]
  wits := []

/-- Executed control: the control certificate is accepted. -/
theorem control_verify : verify id certone = true := by decide

/-- Executed control: the same certificate with a wrong qualified
    set — one fact of the closure missing — is not accepted. -/
theorem control_verify_bad :
    verify id { certone with q := [1] } = false := by decide

end Final
end Spine
end SoftwareIsQuantifiable

#print axioms SoftwareIsQuantifiable.Spine.Final.verify_iff
#print axioms SoftwareIsQuantifiable.Spine.Final.final
#print axioms SoftwareIsQuantifiable.Spine.Final.final_covered
#print axioms SoftwareIsQuantifiable.Spine.Final.stepb_check
