/-
  The coverage group of the update and checker spine (obligations
  22–32 of the spine spec, 2026-11-21): the stronger sensor model.

  The audited coverage module of this repo lets a ledger record count
  as coverage with no sensor behind it: the validator is supplied,
  the witness is two numbers, and nothing binds the record to a
  deployment. This module builds the model the audit specified as
  new development. A snapshot carries its own mediation graph, its
  deployed sensors, and three separate evidence lists — deployment,
  health, fidelity — no component standing in for another. A fact is
  observed only when a real deployed sensor, healthy and faithful,
  has a mediation path to the fact's site. Coverage is per fact, per
  snapshot, by receipts that passed the component checks against
  that snapshot alone.

  Premises of the spec enter exactly where the obligations name
  them: P2 at obligation 22, P4 and P5 at 24 and 26, P6 at 26 and
  31, P3 at 31. Each appears as an explicit hypothesis. None is
  discharged here.
-/

import SoftwareIsQuantifiable.Coloring
import SoftwareIsQuantifiable.Spine.Core
import SoftwareIsQuantifiable.Spine.Closure
import SoftwareIsQuantifiable.Coverage

namespace SoftwareIsQuantifiable
namespace Spine
namespace Sense

/-- A sensor: an identity, a kind, and the site it is mounted at. -/
structure Sensor where
  /-- The sensor identity. -/
  id : Nat
  /-- The sensor kind. -/
  kind : Nat
  /-- The site the sensor is mounted at. -/
  mount : Nat
deriving DecidableEq, Repr

/-- A snapshot for coverage: the spine state together with the
    per-snapshot data the coverage claim speaks about — the
    mediation graph, the deployed sensors, the health and fidelity
    lists, the placement of facts at sites, the declared site set,
    and the snapshot's stated time. -/
structure Snap where
  /-- The spine state (seeds, rules, scope, version declarations). -/
  state : State
  /-- The declared mediation steps of this snapshot. -/
  edges : List (Nat × Nat)
  /-- The deployed sensors of this snapshot. -/
  deploys : List Sensor
  /-- Sensors within the declared failure model at this time. -/
  healthy : List Nat
  /-- Sensors whose reports mean what the model takes them to mean. -/
  faithful : List Nat
  /-- The site of each placed fact. -/
  places : List (Nat × Nat)
  /-- The declared site set. -/
  sites : List Nat
  /-- The snapshot's stated time. -/
  now : Nat
deriving DecidableEq, Repr

/-- The encoding of an edge list: its length, then each pair. -/
def encedges (es : List (Nat × Nat)) : List Nat :=
  es.length :: es.flatMap (fun e => [e.1, e.2])

/-- The encoding of a sensor list: its length, then each sensor. -/
def encsensors (ss : List Sensor) : List Nat :=
  ss.length :: ss.flatMap (fun s => [s.id, s.kind, s.mount])

/-- The encoding of a whole coverage snapshot, in a fixed order. -/
def encsnap (s : Snap) : List Nat :=
  encstate s.state ++ encedges s.edges ++ encsensors s.deploys ++
    encnats s.healthy ++ encnats s.faithful ++ encedges s.places ++
    encnats s.sites ++ [s.now]

/-- The coverage root of a snapshot: the named hash of its full
    encoding. A witness names this root, so a witness is bound to
    the whole snapshot — graph, sensors, and evidence included —
    not to the spine state alone. -/
def sroot (h : List Nat → List Nat) (s : Snap) : List Nat :=
  h (encsnap s)

/-! ## Mediation paths and reachability (obligation 23) -/

/-- A mediation path in a graph: a directed chain of declared
    steps from one site to another. -/
inductive Path (edges : List (Nat × Nat)) : Nat → Nat → Prop where
  /-- A path of length zero from a site to itself. -/
  | refl (a : Nat) : Path edges a a
  /-- A declared step followed by a path. -/
  | step (a b c : Nat) (h : (a, b) ∈ edges) (t : Path edges b c) :
      Path edges a c

/-- Paths compose: a path from a to b and a path from b to c give
    a path from a to c. -/
theorem Path.trans {edges : List (Nat × Nat)} {a b c : Nat}
    (p : Path edges a b) (q : Path edges b c) : Path edges a c := by
  induction p with
  | refl _ => exact q
  | step x y z h _ IH => exact Path.step x y c h (IH q)

/-- Whether consecutive sites of a recorded path are all declared
    steps of the graph: the checker's reading of a recorded path. -/
def chainb (edges : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide ((a, b) ∈ edges) && chainb edges (b :: rest)

/-- A pair of sites is consecutive in a recorded path when it
    appears as neighbouring entries. -/
def consec (a b : Nat) : List Nat → Prop
  | [] => False
  | [_] => False
  | x :: y :: rest => (x = a ∧ y = b) ∨ consec a b (y :: rest)

/-- Every consecutive pair of a chain that passes the check is a
    declared step. -/
theorem mem_of_chainb {edges : List (Nat × Nat)} {a b : Nat} :
    ∀ (p : List Nat), chainb edges p = true → consec a b p →
      (a, b) ∈ edges := by
  intro p
  induction p with
  | nil => intro _ h; exact h.elim
  | cons x p IH =>
    cases p with
    | nil => intro _ h; exact h.elim
    | cons y rest =>
      intro hc h
      simp only [chainb, Bool.and_eq_true, decide_eq_true_eq] at hc
      cases h with
      | inl he => rw [he.1, he.2] at hc; exact hc.1
      | inr hr => exact IH hc.2 hr

/-- A recorded path that passes the chain check is a mediation
    path from its first site to its last. -/
theorem Path.ofchain {edges : List (Nat × Nat)} :
    ∀ (p : List Nat) (m s : Nat), chainb edges p = true →
      p.head? = some m → p.getLast? = some s → Path edges m s := by
  intro p
  induction p with
  | nil => intro m s _ hh _; simp at hh
  | cons x p IH =>
    cases p with
    | nil =>
      intro m s _ hh hl
      have h1 : x = m := by simpa using hh
      have h2 : x = s := by simpa using hl
      subst h1
      subst h2
      exact Path.refl x
    | cons y rest =>
      intro m s hc hh hl
      simp only [chainb, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hh' : x = m := by simp at hh; exact hh
      have hl' : (y :: rest).getLast? = some s := by
        have : (x :: y :: rest).getLast? = (y :: rest).getLast? := rfl
        rw [this] at hl; exact hl
      have step : Path edges y s :=
        IH y s hc.2 rfl hl'
      rw [← hh']
      exact Path.step x y s hc.1 step

/-- The transitive-closure rules over site pairs: from (a, b) and
    (b, c), conclude (a, c), for every triple of declared sites. -/
def trules (sites : List Nat) : List (Coloring.Rule (Nat × Nat)) :=
  sites.flatMap fun a => sites.flatMap fun b => sites.map fun c =>
    { premises := [(a, b), (b, c)], conclusion := (a, c) }

/-- A rule of the transitive-closure set has the stated shape. -/
theorem trules_shape {sites : List Nat} {r : Coloring.Rule (Nat × Nat)}
    (hr : r ∈ trules sites) :
    ∃ a ∈ sites, ∃ b ∈ sites, ∃ c ∈ sites,
      r.premises = [(a, b), (b, c)] ∧ r.conclusion = (a, c) := by
  simp only [trules, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨a, ha, b, hb, c, hc, hcr⟩ := hr
  exact ⟨a, ha, b, hb, c, hc, by rw [← hcr], by rw [← hcr]⟩

/-- Every site pair over the declared sites. -/
def pairs (sites : List Nat) : List (Nat × Nat) :=
  sites.flatMap fun a => sites.map fun b => (a, b)

/-- A pair of declared sites is in the pair list. -/
theorem mem_pairs {sites : List Nat} {a c : Nat}
    (ha : a ∈ sites) (hc : c ∈ sites) : (a, c) ∈ pairs sites := by
  simp only [pairs, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, c, hc, rfl⟩

/-- Every transitive-closure rule concludes a declared pair. -/
theorem trules_concl {sites : List Nat}
    {r : Coloring.Rule (Nat × Nat)} (hr : r ∈ trules sites) :
    r.conclusion ∈ pairs sites := by
  obtain ⟨a, ha, _, _, c, hc, _, hcon⟩ := trules_shape hr
  rw [hcon]
  exact mem_pairs ha hc

/-- The seed state of the reachability closure: the declared steps
    themselves, together with every diagonal pair. -/
def seedpairs (edges : List (Nat × Nat)) :
    Coloring.State (Nat × Nat) :=
  fun p => decide (p ∈ edges ∨ p.1 = p.2)

/-- Reachability as the checker computes it: membership of the pair
    in the cold closure of the steps under the transitive rules. -/
def reachb (snap : Snap) (a b : Nat) : Bool :=
  Closure.Cold.close (trules snap.sites) (pairs snap.sites)
    (seedpairs snap.edges) (a, b)

/-- Reachability as a derivation: the pair is derivable from the
    steps under the transitive rules. -/
def reach (snap : Snap) (a b : Nat) : Prop :=
  Coloring.Deriv (trules snap.sites) (seedpairs snap.edges) (a, b)

/-- The computed reachability and the derivability agree. -/
theorem reachb_iff_reach (snap : Snap) (a b : Nat) :
    reachb snap a b = true ↔ reach snap a b :=
  ⟨fun h => (Closure.Cold.least _ _ _ (fun r hr => trules_concl hr)).2.2.1 _ h,
   fun h => (Closure.Cold.least _ _ _ (fun r hr => trules_concl hr)).2.1 _ h⟩

/-- Every derivation in the reachability closure is a mediation
    path. This direction needs no hypothesis on the graph. -/
theorem path_of_deriv {edges : List (Nat × Nat)} {sites : List Nat} :
    ∀ (p : Nat × Nat),
      Coloring.Deriv (trules sites) (seedpairs edges) p →
        Path edges p.1 p.2 := by
  intro p h
  induction h with
  | seed hh =>
    rename_i q
    have hp : q ∈ edges ∨ q.1 = q.2 := by
      have hh' : decide (q ∈ edges ∨ q.1 = q.2) = true := hh
      exact of_decide_eq_true hh'
    cases hp with
    | inl he =>
      have he' : (q.1, q.2) ∈ edges := by
        cases q with
        | mk a b => exact he
      exact Path.step q.1 q.2 q.2 he' (Path.refl q.2)
    | inr he => rw [he]; exact Path.refl q.2
  | apply hr _ IH =>
    obtain ⟨x, _, y, _, z, _, hprem, hcon⟩ := trules_shape hr
    have e1 : Path edges x y := by
      have h1 := IH (x, y) (by simp [hprem])
      simpa using h1
    have e2 : Path edges y z := by
      have h2 := IH (y, z) (by simp [hprem])
      simpa using h2
    have hxz : Path edges x z := Path.trans e1 e2
    rw [hcon]
    exact hxz

/-- Every derivation in the reachability closure is a mediation
    path, stated at a snapshot. -/
theorem path_of_reach {snap : Snap} {a b : Nat} :
    reach snap a b → Path snap.edges a b :=
  fun h => path_of_deriv (a, b) h

/-- Every mediation path between declared sites of a well-formed
    graph is a derivation in the reachability closure. -/
theorem reach_of_path {snap : Snap}
    (hwf : ∀ e ∈ snap.edges, e.1 ∈ snap.sites ∧ e.2 ∈ snap.sites) :
    ∀ {a b : Nat}, Path snap.edges a b →
      a ∈ snap.sites → b ∈ snap.sites → reach snap a b := by
  intro a b h
  induction h with
  | refl x =>
    intro _ _
    apply Coloring.Deriv.seed
    simp [seedpairs]
  | step s m e he ht IH =>
    intro ha hb
    have hm : m ∈ snap.sites := (hwf _ he).2
    have ih : reach snap m e := IH hm hb
    have e1 : reach snap s m := by
      apply Coloring.Deriv.seed
      simp [seedpairs, he]
    have hrule : ({ premises := [(s, m), (m, e)], conclusion := (s, e) } : Coloring.Rule (Nat × Nat)) ∈ trules snap.sites := by
      simp only [trules, List.mem_flatMap, List.mem_map]
      exact ⟨s, ha, m, hm, e, hb, rfl⟩
    exact Coloring.Deriv.apply hrule (fun p hp => by
      simp only [List.mem_cons, List.mem_singleton] at hp
      cases hp with
      | inl hpp => rw [hpp]; exact e1
      | inr hpp =>
        cases hpp with
        | inl hpp => rw [hpp]; exact ih
        | inr hpp => exact (List.not_mem_nil hpp).elim)

/-- Obligation 23 — reachability is exactly path existence: for
    declared sites of a well-formed graph, the reachability the
    checker computes holds if and only if a directed mediation path
    exists in that snapshot's graph. -/
theorem reach_iff_path {snap : Snap} {a b : Nat}
    (hwf : ∀ e ∈ snap.edges, e.1 ∈ snap.sites ∧ e.2 ∈ snap.sites)
    (ha : a ∈ snap.sites) (hb : b ∈ snap.sites) :
    reachb snap a b = true ↔ Path snap.edges a b :=
  ⟨fun h => path_of_reach ((reachb_iff_reach snap a b).1 h),
   fun h => (reachb_iff_reach snap a b).2 (reach_of_path hwf h ha hb)⟩

/-- A coverage witness as recorded against a snapshot: the fact it
    vouches for, the root of the snapshot it was checked against, the
    sensor whose reading it rests on, the recorded mediation path
    from the sensor mount to the fact site, the time bound the
    reading was taken under, and the reachability graph the path
    check was run against, when one was supplied. -/
structure Wit where
  /-- The fact vouched for. -/
  fact : Nat
  /-- The snapshot root the witness was checked against. -/
  root : List Nat
  /-- The sensor whose reading the witness rests on. -/
  sensor : Nat
  /-- The recorded path: sites from the sensor mount to the fact
      site. -/
  path : List Nat
  /-- The time bound the reading was taken under. -/
  bound : Nat
  /-- The reachability graph supplied for the path check, if any. -/
  graph : Option (List (Nat × Nat))

-- The component checks a witness must pass against a snapshot.
-- Each is a decidable test on the snapshot's own records, so a
-- failure names the component that failed.
namespace Ok

/-- The root component: the witness names this snapshot's root. -/
def root (h : List Nat → List Nat) (snap : Snap) (w : Wit) : Bool :=
  decide (w.root = sroot h snap)

/-- The deployment component: the named sensor is deployed in this
    snapshot. -/
def dep (snap : Snap) (w : Wit) : Bool :=
  decide (w.sensor ∈ snap.deploys.map Sensor.id)

/-- The health component: the named sensor is in this snapshot's
    health evidence. -/
def health (snap : Snap) (w : Wit) : Bool :=
  decide (w.sensor ∈ snap.healthy)

/-- The fidelity component: the named sensor is in this snapshot's
    fidelity evidence. -/
def faith (snap : Snap) (w : Wit) : Bool :=
  decide (w.sensor ∈ snap.faithful)

/-- The path component: the recorded path is a chain over this
    snapshot's mediation edges from the named sensor's mount to a
    placement of the vouched fact. -/
def path (snap : Snap) (w : Wit) : Bool :=
  snap.deploys.any (fun s => decide (s.id = w.sensor) &&
    chainb snap.edges w.path &&
    decide (w.path.head? = some s.mount) &&
    snap.places.any (fun q => decide (q.1 = w.fact) &&
      decide (w.path.getLast? = some q.2)))

/-- The freshness component: the reading's bound has not passed at
    this snapshot's time. -/
def fresh (snap : Snap) (w : Wit) : Bool :=
  decide (w.bound ≤ snap.now)

/-- The graph component: the reachability graph the path check ran
    against, when one was supplied, is this snapshot's own edge
    set. -/
def graph (snap : Snap) (w : Wit) : Bool :=
  match w.graph with
  | none => true
  | some g => decide (g = snap.edges)

end Ok

/-- The full witness check: every component passes against this
    snapshot. -/
def check (h : List Nat → List Nat) (snap : Snap) (w : Wit) : Bool :=
  Ok.root h snap w && Ok.dep snap w && Ok.health snap w &&
    Ok.faith snap w && Ok.path snap w && Ok.fresh snap w &&
    Ok.graph snap w

/-- A receipt: a witness that passes the full check against this
    snapshot. Receipts are per-snapshot by construction — the check
    is a function of the snapshot. -/
def Receipt (h : List Nat → List Nat) (snap : Snap) (w : Wit) : Prop :=
  check h snap w = true

/-- Obligation 22, first half: a receipt binds the witness to this
    snapshot's root — the root component of the check is the
    equality with the snapshot's recomputed root. -/
theorem receipt_root {h : List Nat → List Nat} {snap : Snap} {w : Wit}
    (hr : Receipt h snap w) : w.root = sroot h snap := by
  have h1 : decide (w.root = sroot h snap) = true := by
    have h2 := hr
    simp only [Receipt, check, Bool.and_eq_true] at h2
    exact h2.1.1.1.1.1.1
  exact of_decide_eq_true h1

/-- Obligation 22, second half: a witness naming any other root is
    refused by this snapshot — no receipt exists for it here. -/
theorem receipt_root_refuses {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hne : w.root ≠ sroot h snap) :
    check h snap w = false := by
  have h1 : Ok.root h snap w = false := by
    simp only [Ok.root, ne_eq, decide_eq_false_iff_not]
    exact hne
  simp [check, h1]

/-- The concrete rolling hash for the executed controls: a
    two-word digest, the fold over the code words and the length. -/
def hashw : List Nat → List Nat :=
  fun ws => [ws.foldl (fun a w => (a * 257 + w + 1) % 4294967296) 0,
    ws.length]

/-- Control snapshot one: a fact 9 seeded in the state, one sensor
    (id 1, mount 5) deployed, healthy, and faithful, the fact placed
    at the mount site, one mediation edge, time 10. -/
def snapone : Snap where
  state := { seeds := [9], rules := [], scope := 0, vers := { sem := 1, par := 1, chk := 1, enc := 1, hsh := 1 } }
  edges := [(5, 9)]
  deploys := [{ id := 1, kind := 0, mount := 5 }]
  healthy := [1]
  faithful := [1]
  places := [(9, 9)]
  sites := [5, 9]
  now := 10

/-- Control snapshot two: identical to snapshot one except the
    seeded fact is 8 instead of 9. -/
def snaptwo : Snap where
  state := { seeds := [8], rules := [], scope := 0, vers := { sem := 1, par := 1, chk := 1, enc := 1, hsh := 1 } }
  edges := [(5, 9)]
  deploys := [{ id := 1, kind := 0, mount := 5 }]
  healthy := [1]
  faithful := [1]
  places := [(9, 9)]
  sites := [5, 9]
  now := 10

/-- The good witness for snapshot one: the fact 9, the snapshot's
    own root under the concrete hash, sensor 1, the path from the
    mount 5 to the fact site 9, bound 10, no supplied graph. -/
def witone : Wit where
  fact := 9
  root := sroot hashw snapone
  sensor := 1
  path := [5, 9]
  bound := 10
  graph := none

/-- Obligation 22, executed control: the two control snapshots have
    different roots under the concrete hash — a one-fact change in
    the snapshot moves the root, so a witness bound to one is
    refused by the other. -/
theorem control_roots_differ :
    sroot hashw snapone ≠ sroot hashw snaptwo := by decide

/-- Obligation 22, executed control: the good witness is a receipt
    at its own snapshot. -/
theorem control_good_receipt : Receipt hashw snapone witone := by
  show check hashw snapone witone = true
  decide

/-- Obligation 22, executed control: the same witness is refused at
    the snapshot that differs in one seeded fact. -/
theorem control_other_root_refused :
    check hashw snaptwo witone = false := by decide

/-- The observed predicate: a fact is observed at a snapshot when
    some sensor deployed in the snapshot, present in both the
    health and fidelity evidence, has a mediation path in the
    snapshot from its mount to a site where the fact is placed.
    Premises P5 (sensor fidelity) and P6 (sensor health model) are
    the snapshot's own evidence lists; this predicate reads them,
    it does not discharge them. -/
def Observed (snap : Snap) (f : Nat) : Prop :=
  ∃ s ∈ snap.deploys, s.id ∈ snap.healthy ∧ s.id ∈ snap.faithful ∧
    ∃ t, (f, t) ∈ snap.places ∧ Path snap.edges s.mount t

/-- The decidable form of observed: a fold over the deployed
    sensors testing the health and fidelity evidence, a placement
    of the fact, and reachability from the mount to the placement
    site. -/
def observedb (snap : Snap) (f : Nat) : Bool :=
  snap.deploys.any (fun s =>
    decide (s.id ∈ snap.healthy) && decide (s.id ∈ snap.faithful) &&
      snap.places.any (fun q =>
        decide (q.1 = f) && reachb snap s.mount q.2))

/-- Snapshot sanity: every mediation edge runs between declared
    sites, every placement is at a declared site, and every
    deployed sensor is mounted at a declared site. The reachability
    closure ranges over declared sites, so the decidable observed
    form agrees with the predicate on sane snapshots. -/
def Sane (snap : Snap) : Prop :=
  (∀ e ∈ snap.edges, e.1 ∈ snap.sites ∧ e.2 ∈ snap.sites) ∧
    (∀ q ∈ snap.places, q.2 ∈ snap.sites) ∧
    (∀ s ∈ snap.deploys, s.mount ∈ snap.sites)

/-- The decidable form of observed agrees with the predicate on a
    sane snapshot, both directions. -/
theorem observedb_iff {snap : Snap} {f : Nat} (hs : Sane snap) :
    observedb snap f = true ↔ Observed snap f := by
  constructor
  · intro hb
    simp only [observedb, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hb
    obtain ⟨s, hsm, h12, q, hqbody⟩ := hb
    obtain ⟨h1, h2⟩ := h12
    obtain ⟨hq, hq1, hq2⟩ := hqbody
    refine ⟨s, hsm, h1, h2, q.2, ?_, ?_⟩
    · rw [← hq1]; exact hq
    · exact path_of_reach ((reachb_iff_reach snap s.mount q.2).1 hq2)
  · intro ho
    obtain ⟨s, hsm, h1, h2, t, ht, hpath⟩ := ho
    have hrb : reachb snap s.mount t = true :=
      (reachb_iff_reach snap s.mount t).2
        (reach_of_path hs.1 hpath (hs.2.2 s hsm)
          (hs.2.1 (f, t) ht))
    refine List.any_eq_true.2 ⟨s, hsm, ?_⟩
    show (decide (s.id ∈ snap.healthy) &&
      decide (s.id ∈ snap.faithful) &&
      snap.places.any (fun q =>
        decide (q.1 = f) && reachb snap s.mount q.2)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h1, h2⟩, ?_⟩
    refine List.any_eq_true.2 ⟨(f, t), ht, ?_⟩
    show (decide ((f, t).1 = f) && reachb snap s.mount (f, t).2) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by simp, hrb⟩

/-- Obligation 24: a witness naming a sensor that is not deployed
    in the snapshot is refused — the deployment component fails, so
    the whole check fails, whatever the other components say. -/
theorem nodep_refused {h : List Nat → List Nat} {snap : Snap} {w : Wit}
    (hw : w.sensor ∉ snap.deploys.map Sensor.id) :
    check h snap w = false := by
  have hd : Ok.dep snap w = false := by
    simp only [Ok.dep, decide_eq_false_iff_not]
    exact hw
  simp [check, hd]

/-- Obligation 25: a receipt at a snapshot implies the deployment
    evidence is present in that snapshot. -/
theorem receipt_dep {h : List Nat → List Nat} {snap : Snap} {w : Wit}
    (hr : Receipt h snap w) :
    w.sensor ∈ snap.deploys.map Sensor.id := by
  have h1 : decide (w.sensor ∈ snap.deploys.map Sensor.id) = true := by
    have h2 := hr
    simp only [Receipt, check, Bool.and_eq_true] at h2
    exact h2.1.1.1.1.1.2
  exact of_decide_eq_true h1

/-- Obligation 25: a receipt at a snapshot implies the health
    evidence is present in that snapshot. -/
theorem receipt_health {h : List Nat → List Nat} {snap : Snap} {w : Wit}
    (hr : Receipt h snap w) : w.sensor ∈ snap.healthy := by
  have h1 : decide (w.sensor ∈ snap.healthy) = true := by
    have h2 := hr
    simp only [Receipt, check, Bool.and_eq_true] at h2
    exact h2.1.1.1.1.2
  exact of_decide_eq_true h1

/-- Obligation 25: a receipt at a snapshot implies the fidelity
    evidence is present in that snapshot. -/
theorem receipt_faith {h : List Nat → List Nat} {snap : Snap} {w : Wit}
    (hr : Receipt h snap w) : w.sensor ∈ snap.faithful := by
  have h1 : decide (w.sensor ∈ snap.faithful) = true := by
    have h2 := hr
    simp only [Receipt, check, Bool.and_eq_true] at h2
    exact h2.1.1.1.2
  exact of_decide_eq_true h1

/-- Control snapshot with no health evidence: identical to
    snapshot one except the health list is empty. -/
def snapnohealth : Snap where
  state := { seeds := [9], rules := [], scope := 0, vers := { sem := 1, par := 1, chk := 1, enc := 1, hsh := 1 } }
  edges := [(5, 9)]
  deploys := [{ id := 1, kind := 0, mount := 5 }]
  healthy := []
  faithful := [1]
  places := [(9, 9)]
  sites := [5, 9]
  now := 10

/-- Control snapshot with no fidelity evidence: identical to
    snapshot one except the fidelity list is empty. -/
def snapnofaith : Snap where
  state := { seeds := [9], rules := [], scope := 0, vers := { sem := 1, par := 1, chk := 1, enc := 1, hsh := 1 } }
  edges := [(5, 9)]
  deploys := [{ id := 1, kind := 0, mount := 5 }]
  healthy := [1]
  faithful := []
  places := [(9, 9)]
  sites := [5, 9]
  now := 10

/-- The witness for the no-health control snapshot: the good
    witness's shape, rooted at that snapshot. -/
def witnohealth : Wit where
  fact := 9
  root := sroot hashw snapnohealth
  sensor := 1
  path := [5, 9]
  bound := 10
  graph := none

/-- The witness for the no-fidelity control snapshot. -/
def witnofaith : Wit where
  fact := 9
  root := sroot hashw snapnofaith
  sensor := 1
  path := [5, 9]
  bound := 10
  graph := none

/-- The witness naming an undeployed sensor at snapshot one. -/
def witnodep : Wit where
  fact := 9
  root := sroot hashw snapone
  sensor := 2
  path := [5, 9]
  bound := 10
  graph := none

/-- Obligation 25, executed control: with the health evidence
    missing, the otherwise good witness is refused. -/
theorem control_nohealth_refused :
    check hashw snapnohealth witnohealth = false := by decide

/-- Obligation 25, executed control: with the fidelity evidence
    missing, the otherwise good witness is refused. -/
theorem control_nofaith_refused :
    check hashw snapnofaith witnofaith = false := by decide

/-- Obligation 24, executed control: a witness naming a sensor
    that is not deployed is refused. -/
theorem control_nodep_refused :
    check hashw snapone witnodep = false := by decide

/-! ## The snapshot's own closure (obligations 26–27) -/

/-- A true proposition has its decidable form true. -/
theorem decide_true_of {p : Prop} [Decidable p] (h : p) :
    decide p = true := by
  rw [decide_eq_true_eq]; exact h

/-- Every mediation path has a recorded form: a list of sites that
    starts at the path's start, ends at the path's end, and chains
    over the same edge set. Stated as an existence over lists,
    since the path itself is a proof. -/
theorem path_witness {edges : List (Nat × Nat)} {a b : Nat}
    (p : Path edges a b) :
    ∃ l : List Nat, l.head? = some a ∧ l.getLast? = some b ∧
      chainb edges l = true := by
  induction p with
  | refl x => exact ⟨[x], rfl, rfl, rfl⟩
  | step x y z h t ih =>
    obtain ⟨l, hl1, hl2, hl3⟩ := ih
    refine ⟨x :: l, rfl, ?_, ?_⟩
    · cases l with
      | nil => simp at hl1
      | cons u us => exact hl2
    · cases l with
      | nil => simp at hl1
      | cons u us =>
        have hu : u = y := by
          have h1 := hl1
          simp only [List.head?_cons, Option.some.injEq] at h1
          exact h1
        subst hu
        show (decide ((x, u) ∈ edges) && chainb edges (u :: us)) = true
        rw [Bool.and_eq_true]
        exact ⟨decide_true_of h, hl3⟩

/-- A spine rule read as a closure rule over facts: same premises,
    same conclusion. -/
def crule (r : Rule) : Coloring.Rule Nat :=
  ⟨r.premises, r.conclusion⟩

/-- The finite fact universe of a snapshot's state: the seeds and
    every fact any rule mentions. -/
def facts (snap : Snap) : List Nat :=
  snap.state.seeds ++ snap.state.rules.flatMap
    (fun r => r.premises ++ [r.conclusion])

/-- The seed state of a snapshot's closure: exactly its seeds. -/
def seedst (snap : Snap) : Nat → Bool :=
  fun f => decide (f ∈ snap.state.seeds)

/-- The least closure of a snapshot's own state: the facts
    derivable from its seeds by its rules. -/
abbrev Least (snap : Snap) (f : Nat) : Prop :=
  Coloring.Deriv (snap.state.rules.map crule) (seedst snap) f

/-- The decidable least closure: the cold closure computation over
    the snapshot's rules, universe, and seeds. -/
def leastb (snap : Snap) (f : Nat) : Bool :=
  Closure.Cold.close (snap.state.rules.map crule) (facts snap)
    (seedst snap) f

/-- Every mapped rule's conclusion lies in the declared universe,
    by construction of the universe. -/
theorem facts_sound {snap : Snap} :
    ∀ r ∈ snap.state.rules.map crule, r.conclusion ∈ facts snap := by
  intro r hr
  obtain ⟨r₀, hr₀, hreq⟩ := List.mem_map.1 hr
  rw [← hreq]
  exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨r₀, hr₀,
    List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))⟩))

/-- The decidable least closure agrees with the derivability
    predicate, both directions — the cold closure is the least
    fixed point, applied to the snapshot's own state. -/
theorem leastb_iff {snap : Snap} {f : Nat} :
    leastb snap f = true ↔ Least snap f :=
  ⟨fun h => (Closure.Cold.least _ _ _ facts_sound).2.2.1 f h,
   fun h => (Closure.Cold.least _ _ _ facts_sound).2.1 f h⟩

/-- Boolean implication, for the executable rule check. -/
def bimp (a b : Bool) : Bool := !a || b

/-- Boolean implication is implication of the two truth values. -/
theorem bimp_iff {a b : Bool} :
    bimp a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

/-- The executable rule-preservation check: every rule of the
    snapshot whose premises all read observed also reads its
    conclusion observed, under the decidable observed form. -/
def presb (snap : Snap) : Bool :=
  snap.state.rules.all (fun r =>
    bimp (r.premises.all (fun p => observedb snap p))
      (observedb snap r.conclusion))

/-- The executable rule-preservation check agrees with the
    predicate form on a sane snapshot, both directions. -/
theorem presb_iff {snap : Snap} (hs : Sane snap) :
    presb snap = true ↔
      ∀ r ∈ snap.state.rules, (∀ p ∈ r.premises, Observed snap p) →
        Observed snap r.conclusion := by
  simp only [presb, List.all_eq_true]
  constructor
  · intro h r hr hp
    have hr' := h r hr
    rw [bimp_iff, List.all_eq_true] at hr'
    exact (observedb_iff hs).1 (hr' (fun p hp' =>
      (observedb_iff hs).2 (hp p hp')))
  · intro h r hr
    rw [bimp_iff, List.all_eq_true]
    intro hp
    exact (observedb_iff hs).2 (h r hr (fun p hp' =>
      (observedb_iff hs).1 (hp p hp')))

/-- Obligation 26: observed-ness is preserved along the snapshot's
    own closure. If every seed is observed and every rule carries
    observed premises to an observed conclusion, then every fact
    of the least closure is observed. The induction is the closure
    induction principle at the observed predicate. -/
theorem least_observed {snap : Snap}
    (hseed : ∀ f ∈ snap.state.seeds, Observed snap f)
    (hpres : ∀ r ∈ snap.state.rules,
      (∀ p ∈ r.premises, Observed snap p) → Observed snap r.conclusion)
    {f : Nat} (hf : Least snap f) : Observed snap f := by
  induction hf with
  | seed hh =>
    rename_i q
    have hq : decide (q ∈ snap.state.seeds) = true := hh
    exact hseed q (of_decide_eq_true hq)
  | apply hr hp IH =>
    rename_i r
    obtain ⟨r₀, hr₀, hreq⟩ := List.mem_map.1 hr
    have hcon : r.conclusion = r₀.conclusion :=
      congrArg Coloring.Rule.conclusion hreq.symm
    rw [hcon]
    exact hpres r₀ hr₀ (fun p hp' => IH p (by rw [← hreq]; exact hp'))

/-- A witness assembled from parts that each pass is a receipt:
    the components of the check, taken one by one. -/
theorem check_of_components {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hroot : w.root = sroot h snap)
    (hdep : w.sensor ∈ snap.deploys.map Sensor.id)
    (hhealth : w.sensor ∈ snap.healthy)
    (hfaith : w.sensor ∈ snap.faithful)
    (hpath : Ok.path snap w = true)
    (hfresh : w.bound ≤ snap.now)
    (hgraph : Ok.graph snap w = true) : Receipt h snap w := by
  simp only [Receipt, check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨decide_true_of hroot, decide_true_of hdep⟩,
    decide_true_of hhealth⟩, decide_true_of hfaith⟩, hpath⟩,
    decide_true_of hfresh⟩, hgraph⟩

/-- Obligation 27, the receipt direction: an observed fact has a
    receipt at the same snapshot — the witness assembled from the
    observing sensor, the recorded form of its mediation path, the
    snapshot's own root, and the snapshot's time as the bound. -/
theorem receipt_of_observed {h : List Nat → List Nat} {snap : Snap}
    {f : Nat} (ho : Observed snap f) :
    ∃ w, w.fact = f ∧ Receipt h snap w := by
  obtain ⟨s, hsm, h1, h2, t, ht, hpath⟩ := ho
  obtain ⟨l, hl1, hl2, hl3⟩ := path_witness hpath
  have hpathc : Ok.path snap { fact := f, root := sroot h snap, sensor := s.id, path := l, bound := snap.now, graph := none } = true := by
    refine List.any_eq_true.2 ⟨s, hsm, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨trivial, hl3⟩, hl1⟩, ?_⟩
    refine List.any_eq_true.2 ⟨(f, t), ht, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨trivial, hl2⟩
  exact ⟨{ fact := f, root := sroot h snap, sensor := s.id, path := l, bound := snap.now, graph := none }, rfl,
    check_of_components rfl (List.mem_map.2 ⟨s, hsm, rfl⟩) h1 h2
      hpathc (Nat.le_refl _) rfl⟩

/-- Coverage at a snapshot: every fact of the least closure has a
    receipt at that snapshot. -/
def Covered (h : List Nat → List Nat) (snap : Snap) : Prop :=
  ∀ f, Least snap f → ∃ w, w.fact = f ∧ Receipt h snap w

/-- Obligation 27: under the preservation hypotheses of obligation
    26, the snapshot is covered — every least-closure fact is
    observed, and every observed fact has a receipt. -/
theorem covered_of_preserved {h : List Nat → List Nat} {snap : Snap}
    (hseed : ∀ f ∈ snap.state.seeds, Observed snap f)
    (hpres : ∀ r ∈ snap.state.rules,
      (∀ p ∈ r.premises, Observed snap p) → Observed snap r.conclusion) :
    Covered h snap :=
  fun f hf => receipt_of_observed (least_observed hseed hpres hf)

/-! ## Invalidation and carry-over (obligations 28–29) -/

/-- A recorded path fails the chain test at any snapshot whose
    edge set misses one of the path's consecutive pairs. -/
theorem chainb_false_of_missing {edges : List (Nat × Nat)}
    {p : List Nat} {a b : Nat} (hc : consec a b p)
    (hm : (a, b) ∉ edges) : chainb edges p = false := by
  cases h : chainb edges p with
  | false => rfl
  | true => exact absurd (mem_of_chainb p h hc) hm

/-- Obligation 28, the path kind: a mediation change that removes
    an edge the recorded path steps on invalidates the path
    component at the new snapshot. -/
theorem path_invalidated {snap : Snap} {w : Wit} {a b : Nat}
    (hc : consec a b w.path) (hm : (a, b) ∉ snap.edges) :
    Ok.path snap w = false := by
  have hch : chainb snap.edges w.path = false :=
    chainb_false_of_missing hc hm
  simp [Ok.path, hch]

/-- Obligation 28, the graph kind: when the witness carries the
    reachability graph its path check ran against and that graph
    is not the snapshot's own edge set, the graph component
    fails. -/
theorem graph_stale {snap : Snap} {w : Wit}
    {g : List (Nat × Nat)} (hg : w.graph = some g)
    (hne : g ≠ snap.edges) : Ok.graph snap w = false := by
  simp only [Ok.graph, hg, decide_eq_false_iff_not]
  exact hne

/-- A failed path component fails the whole check. -/
theorem check_false_of_path {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hp : Ok.path snap w = false) :
    check h snap w = false := by
  simp [check, hp]

/-- A failed graph component fails the whole check. -/
theorem check_false_of_graph {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hg : Ok.graph snap w = false) :
    check h snap w = false := by
  simp [check, hg]

/-- A failed health component fails the whole check. -/
theorem check_false_of_health {h : List Nat → List Nat}
    {snap : Snap} {w : Wit} (hh : Ok.health snap w = false) :
    check h snap w = false := by
  simp [check, hh]

/-- A failed fidelity component fails the whole check. -/
theorem check_false_of_faith {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hf : Ok.faith snap w = false) :
    check h snap w = false := by
  simp [check, hf]

/-- The carry-over test of obligation 29, by direct comparison:
    every component of the check except the root test, evaluated
    at the new snapshot. A receipt survives a snapshot change
    exactly when it passes this test at the new snapshot and names
    the new snapshot's root. (The direct-comparison route: the
    spec allows it in place of an affected-cone computation.) -/
def carryb (snap : Snap) (w : Wit) : Bool :=
  Ok.dep snap w && Ok.health snap w && Ok.faith snap w &&
    Ok.path snap w && Ok.fresh snap w && Ok.graph snap w

/-- The carry-over test is the conjunction of its six components. -/
theorem carryb_iff {snap : Snap} {w : Wit} :
    carryb snap w = true ↔
      ((((Ok.dep snap w = true ∧ Ok.health snap w = true) ∧
        Ok.faith snap w = true) ∧ Ok.path snap w = true) ∧
        Ok.fresh snap w = true) ∧ Ok.graph snap w = true := by
  simp only [carryb, Bool.and_eq_true]

/-- Obligation 29, one direction: a receipt passes the carry-over
    test at its own snapshot. -/
theorem receipt_carry {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hr : Receipt h snap w) : carryb snap w = true := by
  have h2 := hr
  simp only [Receipt, check, Bool.and_eq_true] at h2
  simp only [carryb, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h2.1.1.1.1.1.2, h2.1.1.1.1.2⟩, h2.1.1.1.2⟩, h2.1.1.2⟩,
    h2.1.2⟩, h2.2⟩

/-- Obligation 29, the survival characterization: a witness that
    passes the carry-over test at a new snapshot and names the new
    snapshot's root is a receipt at the new snapshot. -/
theorem receipt_of_carry {h : List Nat → List Nat} {snap : Snap}
    {w : Wit} (hc : carryb snap w = true)
    (hroot : w.root = sroot h snap) : Receipt h snap w := by
  have h2 := hc
  simp only [carryb, Bool.and_eq_true] at h2
  simp only [Receipt, check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨decide_true_of hroot, h2.1.1.1.1.1⟩, h2.1.1.1.1.2⟩,
    h2.1.1.1.2⟩, h2.1.1.2⟩, h2.1.2⟩, h2.2⟩

/-! ## Verdicts for cones and coverage (obligations 30–31) -/

/-- A three-way verdict: accept, rebuild, or unknown. -/
inductive Verdict where
  | accept
  | rebuild
  | unknown
  deriving DecidableEq, Repr

/-- Obligation 30: the verdict for a claimed affected cone. No
    cone supplied means rebuild; a supplied cone whose
    establishment check fails means unknown; only a supplied,
    established cone accepts. -/
def cverdict (cone : Option (List Nat)) (established : Bool) :
    Verdict :=
  match cone with
  | none => Verdict.rebuild
  | some _ => if established then Verdict.accept else Verdict.unknown

/-- No cone, no acceptance: the verdict is rebuild. -/
theorem cverdict_none (e : Bool) :
    cverdict none e = Verdict.rebuild := rfl

/-- An unestablished cone gives unknown, never accept. -/
theorem cverdict_unknown (c : List Nat) :
    cverdict (some c) false = Verdict.unknown := rfl

/-- A supplied, established cone accepts. -/
theorem cverdict_accept (c : List Nat) :
    cverdict (some c) true = Verdict.accept := rfl

/-- The no-cone verdict is never accept. -/
theorem cverdict_none_not_accept (e : Bool) :
    cverdict none e ≠ Verdict.accept := by
  intro h
  exact Verdict.noConfusion h

/-- Obligation 30, executed control: the missing-cone case
    rebuilds. -/
theorem control_cverdict : cverdict none true = Verdict.rebuild :=
  rfl

/-- Obligation 31: the coverage verdict for one fact from a list
    of witnesses at one snapshot. A passing receipt accepts; a
    claim for the fact that does not pass — stale root, failed
    component, any mismatch against this snapshot — gives unknown;
    no claim at all gives rebuild. -/
def coverb (h : List Nat → List Nat) (snap : Snap) (ws : List Wit)
    (f : Nat) : Verdict :=
  if ws.any (fun w => decide (w.fact = f) && check h snap w) then
    Verdict.accept
  else if ws.any (fun w => decide (w.fact = f)) then
    Verdict.unknown
  else Verdict.rebuild

/-- A receipt among the witnesses accepts. -/
theorem coverb_accept {h : List Nat → List Nat} {snap : Snap}
    {ws : List Wit} {f : Nat} {w : Wit} (hw : w ∈ ws)
    (hf : w.fact = f) (hr : Receipt h snap w) :
    coverb h snap ws f = Verdict.accept := by
  have hc : ws.any (fun w => decide (w.fact = f) &&
      check h snap w) = true :=
    List.any_eq_true.2 ⟨w, hw, by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hf, hr⟩⟩
  simp [coverb, hc]

/-- A claim for the fact with no passing witness gives unknown. -/
theorem coverb_unknown {h : List Nat → List Nat} {snap : Snap}
    {ws : List Wit} {f : Nat} {w : Wit} (hw : w ∈ ws)
    (hf : w.fact = f)
    (hno : ∀ w' ∈ ws, w'.fact = f → check h snap w' = false) :
    coverb h snap ws f = Verdict.unknown := by
  have hc1 : ws.any (fun w => decide (w.fact = f) &&
      check h snap w) = false :=
    List.any_eq_false.2 (fun w' hw' => by
      by_cases hf' : w'.fact = f
      · simp [hf', hno w' hw' hf']
      · simp [hf'])
  have hc2 : ws.any (fun w => decide (w.fact = f)) = true :=
    List.any_eq_true.2 ⟨w, hw, decide_true_of hf⟩
  simp [coverb, hc1, hc2]

/-- No claim for the fact at all gives rebuild. -/
theorem coverb_rebuild {h : List Nat → List Nat} {snap : Snap}
    {ws : List Wit} {f : Nat} (hno : ∀ w ∈ ws, w.fact ≠ f) :
    coverb h snap ws f = Verdict.rebuild := by
  have hc1 : ws.any (fun w => decide (w.fact = f) &&
      check h snap w) = false :=
    List.any_eq_false.2 (fun w hw => by simp [hno w hw])
  have hc2 : ws.any (fun w => decide (w.fact = f)) = false :=
    List.any_eq_false.2 (fun w hw => by simp [hno w hw])
  simp [coverb, hc1, hc2]

/-- Obligation 31, executed control: the good witness accepts at
    its own snapshot. -/
theorem control_coverb_accept :
    coverb hashw snapone [witone] 9 = Verdict.accept := by decide

/-- Obligation 31, executed control: the same witness at the
    snapshot whose root moved gives unknown — the stale case. -/
theorem control_coverb_unknown :
    coverb hashw snaptwo [witone] 9 = Verdict.unknown := by decide

/-- Obligation 31, executed control: no witness for the fact gives
    rebuild. -/
theorem control_coverb_rebuild :
    coverb hashw snapone [witone] 7 = Verdict.rebuild := by decide

/-! ## The fabricated record, executed (obligation 32) -/

/-- The fabricated execution handle of the audit's case: an
    execution named only by the record itself. -/
def fexec : Coverage.Execution := ⟨1⟩

/-- The fabricated ledger record: a witness naming that execution,
    with a round event count, supplied from nothing. -/
def fwit : Coverage.Witness := ⟨1, 0⟩

/-- Obligation 32, the old-claim side: the platform premise of the
    earlier coverage claim is inhabited by the fabricated record.
    The validator accepts everything, the ledger holds the one
    fabricated witness, the roster holds the one execution it
    names, the append-only field is the trivial proposition, and
    the privilege ranks are two supplied numbers. Nothing here is
    derived — that is the defect, exhibited as a checked
    construction. -/
def forged : Coverage.PlatformPremise (fun _ => true) [fwit]
    [fexec] where
  sensorPrivilege := 0
  observedPrivilege := 1
  sensorBelow := by decide
  ledgerAppendOnly := True
  ledgerAppendOnlyHolds := trivial
  mediated := by
    intro e he
    have heq : e = fexec := by simpa using he
    subst heq
    decide

/-- Obligation 32, the new-model side: the same shape satisfies
    nothing here. At a snapshot with no deployed sensor, no fact
    is observed — observation requires a deployed sensor in the
    snapshot's own records. -/
theorem forged_not_observed {f : Nat} :
    ¬ Observed { snapone with deploys := [] } f := by
  intro ho
  obtain ⟨s, hsm, _⟩ := ho
  exact List.not_mem_nil hsm

/-- The control snapshot with no deployed sensor. -/
def snapempty : Snap := { snapone with deploys := [] }

/-- The good witness's shape rooted at the empty snapshot. -/
def witempty : Wit := { witone with root := sroot hashw snapempty }

/-- Obligation 32, executed control: at the snapshot with no
    deployed sensor, the witness is refused — there is no sensor
    evidence for its components to check against. -/
theorem control_empty_refused :
    check hashw snapempty witempty = false := by decide

end Sense
end Spine
end SoftwareIsQuantifiable

#print axioms SoftwareIsQuantifiable.Spine.Sense.receipt_root
#print axioms SoftwareIsQuantifiable.Spine.Sense.observedb_iff
#print axioms SoftwareIsQuantifiable.Spine.Sense.least_observed
#print axioms SoftwareIsQuantifiable.Spine.Sense.receipt_of_observed
#print axioms SoftwareIsQuantifiable.Spine.Sense.covered_of_preserved
#print axioms SoftwareIsQuantifiable.Spine.Sense.coverb_accept
#print axioms SoftwareIsQuantifiable.Spine.Sense.forged_not_observed
#print axioms SoftwareIsQuantifiable.Spine.Sense.path_witness
#print axioms SoftwareIsQuantifiable.Spine.Sense.reach_iff_path
