/-
  Claim 4 — Pareto ordering (spec §20.1, §20.2, §20.4, §21.3).

  What is proven:
  * Separation decides soundly: when a candidate's propagated upper
    bounds are at or below an incumbent's lower bounds on both axes,
    strict on one, then under *every* realization inside the bounds
    the candidate is no worse on both axes and better on one (§20.2).
  * The frontier is nonempty: every finite nonempty set of cost
    points has an undominated element (§20.1, §20.2 existence).
  * A frontier output is never dominated by a named incumbent from
    the same candidate set. This excludes dominated outputs, but does NOT
    exclude incomparable trade-offs. Componentwise no-regression
    requires the separate incumbent admission guard below.
  * Refinement is monotone (§20.2): witnesses only shrink intervals,
    and a pair decided under wider bounds stays decided under
    narrower ones.
  * The regression gate is exact: the check accepts a candidate if
    and only if it drops no previously qualified behavior.

  What is DISPROVEN:
  * Without separation, overlapping intervals do not establish
    per-execution dominance. With separation, separated_sound DOES
    establish dominance for every pair of in-bound realizations.
-/

namespace SoftwareIsQuantifiable
namespace Pareto

/-- An interval bound on one cost axis: the witnessed lower and
    upper bounds of a run's cost. -/
structure Bounds where
  /-- Witnessed lower bound. -/
  lo : Nat
  /-- Witnessed upper bound. -/
  hi : Nat
  /-- The bounds are consistent. -/
  valid : lo ≤ hi

/-- A cost point: realized costs on the two axes (time, compute). -/
abbrev Point := Nat × Nat

/-- Point dominance: no worse on both axes, better on at least one. -/
def dominates (a b : Point) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ (a.1 < b.1 ∨ a.2 < b.2)

/-- Dominance is transitive. -/
theorem dominates_trans {a b c : Point}
    (hab : dominates a b) (hbc : dominates b c) : dominates a c := by
  obtain ⟨h1, h2, h3⟩ := hab
  obtain ⟨h4, h5, h6⟩ := hbc
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by omega)
  · rcases h6 with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- Separation (§20.2): the candidate's upper bounds are at or below
    the incumbent's lower bounds on both axes — time (`t`) and
    compute (`c`) — and strictly below on at least one axis. -/
def separated (ct cc it ic : Bounds) : Prop :=
  ct.hi ≤ it.lo ∧ cc.hi ≤ ic.lo ∧ (ct.hi < it.lo ∨ cc.hi < ic.lo)

/-- A realization: actual costs inside the bounds. -/
def realizes (t c : Bounds) (x : Point) : Prop :=
  t.lo ≤ x.1 ∧ x.1 ≤ t.hi ∧ c.lo ≤ x.2 ∧ x.2 ≤ c.hi

/-- **Separation is sound.** If the candidate is separated from the
    incumbent, then under every pair of realizations the candidate
    dominates the incumbent: no worse on time and on compute
    simultaneously, and better on at least one axis. The two
    inequalities are the discharge of §20.1. -/
theorem separated_sound {ct cc it ic : Bounds} (h : separated ct cc it ic)
    {x y : Point} (hx : realizes ct cc x) (hy : realizes it ic y) :
    x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ (x.1 < y.1 ∨ x.2 < y.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **Refinement is monotone** (§20.2): if both candidates' intervals
    shrink (witnesses only ever shrink a bound they speak to), a
    separated pair stays separated. A schedule once proved dominated
    stays dominated. -/
theorem separated_of_refined {ct cc it ic ct' cc' it' ic' : Bounds}
    (h : separated ct cc it ic)
    (hct : ct.lo ≤ ct'.lo ∧ ct'.hi ≤ ct.hi)
    (hcc : cc.lo ≤ cc'.lo ∧ cc'.hi ≤ cc.hi)
    (hit : it.lo ≤ it'.lo ∧ it'.hi ≤ it.hi)
    (hic : ic.lo ≤ ic'.lo ∧ ic'.hi ≤ ic.hi) :
    separated ct' cc' it' ic' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Auxiliary: from any point of a finite list, an undominated point
    of the list is reachable by dominance. Strong induction on the
    cost sum, by plain induction on a fuel bound. -/
theorem exists_undominated_aux :
    ∀ (n : Nat) (L : List Point) (x : Point),
      x ∈ L → x.1 + x.2 ≤ n →
      ∃ y ∈ L, (dominates y x ∨ y = x) ∧
        ∀ z ∈ L, ¬ dominates z y := by
  intro n
  induction n with
  | zero =>
    intro L x hxL hsum
    refine ⟨x, hxL, Or.inr rfl, ?_⟩
    intro z hzL hdom
    obtain ⟨h1, h2, h3⟩ := hdom
    omega
  | succ n IH =>
    intro L x hxL hsum
    by_cases hund : ∃ z ∈ L, dominates z x
    · cases hund with
      | intro z hz =>
        have hzsum : z.1 + z.2 ≤ n := by
          obtain ⟨h1, h2, h3⟩ := hz.2
          omega
        cases IH L z hz.1 hzsum with
        | intro y hy =>
          refine ⟨y, hy.1, ?_, hy.2.2⟩
          rcases hy.2.1 with h | h
          · exact Or.inl (dominates_trans h hz.2)
          · subst h
            exact Or.inl hz.2
    · refine ⟨x, hxL, Or.inr rfl, ?_⟩
      intro z hzL hdom
      exact hund ⟨z, hzL, hdom⟩

/-- **The frontier is nonempty** (§20.1, §20.2): every finite
    nonempty set of cost points has an undominated element. -/
theorem frontier_nonempty {L : List Point} (hL : L ≠ []) :
    ∃ y ∈ L, ∀ z ∈ L, ¬ dominates z y := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    cases exists_undominated_aux (x.1 + x.2) (x :: xs) x
        (by simp) (Nat.le_refl _) with
    | intro y hy => exact ⟨y, hy.1, hy.2.2⟩

/-- **No output is dominated by a named incumbent.** If the incumbent
    is in the candidate set and the output is a frontier element of
    that set, the incumbent does not dominate the output: a candidate
    ordering that the previously qualified ordering dominated is
    never the output. -/
theorem frontier_not_dominated {L : List Point} {out inc : Point}
    (_hout : out ∈ L) (hinc : inc ∈ L)
    (hfrontier : ∀ z ∈ L, ¬ dominates z out) :
    ¬ dominates inc out :=
  hfrontier inc hinc

/-- Splitting a true conjunction of booleans. -/
theorem and_eq_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => simp at h
  | true =>
    cases b with
    | false => simp at h
    | true => exact ⟨rfl, rfl⟩

/-- The regression gate (§21.3) as a decidable check: a candidate is
    accepted exactly when its behavior list still contains every
    previously qualified behavior. -/
def accepts {B : Type} [DecidableEq B] (qualified candidate : List B) : Bool :=
  qualified.all (fun b => decide (b ∈ candidate))

/-- The gate's exactness, both directions: it accepts if and only if
    no previously qualified behavior is dropped. So a candidate that
    drops a behavior is rejected, by construction, at introduction
    time — never discovered later. -/
theorem accepts_iff {B : Type} [DecidableEq B]
    {qualified candidate : List B} :
    accepts qualified candidate = true ↔
      ∀ b ∈ qualified, b ∈ candidate := by
  induction qualified with
  | nil => simp [accepts]
  | cons a q IH =>
    constructor
    · intro h b hb
      have h' : (decide (a ∈ candidate) && accepts q candidate) = true := h
      have ha : decide (a ∈ candidate) = true := (and_eq_true h').1
      have hq : accepts q candidate = true := (and_eq_true h').2
      cases hb with
      | head _ => exact of_decide_eq_true ha
      | tail _ hbm => exact IH.mp hq b hbm
    · intro h
      have ha : a ∈ candidate := h a (by simp)
      have hq : accepts q candidate = true :=
        IH.mpr (fun b hb => h b (List.mem_cons_of_mem _ hb))
      have hdec : decide (a ∈ candidate) = true := by
        cases hd : decide (a ∈ candidate) with
        | true => rfl
        | false => exact (of_decide_eq_false hd ha).elim
      show (decide (a ∈ candidate) && accepts q candidate) = true
      rw [hdec, hq]
      rfl

/-- **DISPROOF — overlapping bounds alone are insufficient.**
    Take schedule X with witnessed time bounds
    [1, 100] and schedule Y with witnessed time bounds [2, 3]
    (compute equal). The claim "every realization of Y beats every
    realization of X" is false: X can realize 1 while Y realizes 3.
    These intervals do not satisfy separation. This does not refute
    separated_sound, which covers every in-bound realization. -/
theorem not_per_execution_dominance :
    ¬ ∀ x y : Point,
      (1 ≤ x.1 ∧ x.1 ≤ 100 ∧ x.2 = 0) →
      (2 ≤ y.1 ∧ y.1 ≤ 3 ∧ y.2 = 0) →
      y.1 < x.1 := by
  intro h
  have := h (1, 0) (3, 0) (by simp) (by simp)
  simp at this

/-- Componentwise non-regression, distinct from non-domination.
    Costs must refer to the same axes, workload, venue, and measurement
    interpretation. Equality of context keys below binds that scope;
    it does not prove the correctness of a measurement or its model. -/
def noWorse (candidate incumbent : Point) : Prop :=
  candidate.1 ≤ incumbent.1 ∧ candidate.2 ≤ incumbent.2

instance (a b : Point) : Decidable (noWorse a b) :=
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2))

/-- Executable counterexample: a frontier may trade worse time for
    better compute. Frontier membership alone is not a release gate. -/
theorem frontier_can_regress :
    let inc : Point := (1, 10)
    let out : Point := (10, 1)
    (∀ z ∈ [inc, out], ¬ dominates z out) ∧
    ¬ noWorse out inc := by
  simp [dominates, noWorse]

#eval decide (noWorse (10, 1) (1, 10)) -- false

/-- Keep the original candidates, admitting only no-worse costs. -/
def admitted (inc : Point) (candidates : List Point) : List Point :=
  candidates.filter (fun candidate => decide (noWorse candidate inc))

theorem admitted_noWorse {inc out : Point} {candidates : List Point}
    (h : out ∈ admitted inc candidates) : noWorse out inc := by
  simpa [admitted] using (List.mem_filter.mp h).2

/-- Baseline retention makes the guarded frontier nonempty. -/
theorem admitted_frontier_exists {inc : Point} {candidates : List Point}
    (hinc : inc ∈ candidates) :
    ∃ out ∈ admitted inc candidates,
      noWorse out inc ∧
      ∀ z ∈ admitted inc candidates, ¬ dominates z out := by
  have hi : inc ∈ admitted inc candidates := by
    simp [admitted, noWorse, hinc]
  have hn : admitted inc candidates ≠ [] := by
    intro he
    simp [he] at hi
  obtain ⟨out, ho, hf⟩ := frontier_nonempty hn
  exact ⟨out, ho, admitted_noWorse ho, hf⟩

/-- Guarded frontier selection has BOTH guarantees, not just one.
    Any dominator of an admitted point is itself no worse than the
    incumbent, so the guarded frontier is also globally nondominated. -/
theorem admitted_frontier_sound {inc out : Point} {candidates : List Point}
    (hout : out ∈ admitted inc candidates)
    (hf : ∀ z ∈ admitted inc candidates, ¬ dominates z out) :
    noWorse out inc ∧ ∀ z ∈ candidates, ¬ dominates z out := by
  have hn := admitted_noWorse hout
  refine ⟨hn, ?_⟩
  intro z hz hd
  have hzi : noWorse z inc :=
    ⟨Nat.le_trans hd.1 hn.1, Nat.le_trans hd.2.1 hn.2⟩
  have hza : z ∈ admitted inc candidates := by
    simp [admitted, hz, hzi]
  exact hf z hza hd

/-- Combined executable admission: comparable context, no lost
    qualified behaviors, and no worse cost on either existing axis.
    A Context value should be the immutable measurement-scope key,
    not merely the source digest. Behavior coverage is certified input
    to this gate; a list's membership does not itself certify behavior. -/
def acceptsRelease {B Context : Type} [DecidableEq B] [DecidableEq Context]
    (baselineContext candidateContext : Context)
    (qualified candidate : List B) (inc out : Point) : Bool :=
  decide (candidateContext = baselineContext) &&
    accepts qualified candidate && decide (noWorse out inc)

theorem acceptsRelease_iff {B Context : Type}
    [DecidableEq B] [DecidableEq Context]
    (baselineContext candidateContext : Context)
    (qualified candidate : List B) (inc out : Point) :
    acceptsRelease baselineContext candidateContext qualified candidate inc out = true ↔
      candidateContext = baselineContext ∧
      (∀ b ∈ qualified, b ∈ candidate) ∧ noWorse out inc := by
  simp [acceptsRelease, Bool.and_eq_true, accepts_iff, and_assoc]

/-- A sufficient interval separation for replacement without worsening
    either cost axis. Reuse the existing point relation on candidate
    upper bounds and incumbent lower bounds. -/
def weaklySeparated (ct cc it ic : Bounds) : Prop :=
  noWorse (ct.hi, cc.hi) (it.lo, ic.lo)

/-- Non-strict separation prevents regression for every pair of
    realizations inside the supplied bounds. -/
theorem weaklySeparated_sound {ct cc it ic : Bounds}
    (h : weaklySeparated ct cc it ic) {x y : Point}
    (hx : realizes ct cc x) (hy : realizes it ic y) :
    noWorse x y := by
  obtain ⟨ht, hc⟩ := h
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  exact ⟨by omega, by omega⟩

/-- The interval adapter uses the same scoped release authority. The
    supplied bounds and behavior lists must refer to the named common
    measurement context; assigning physical evidence remains external. -/
def acceptsReplacement {B Context : Type} [DecidableEq B] [DecidableEq Context]
    (baselineContext candidateContext : Context)
    (qualified candidate : List B) (ct cc it ic : Bounds) : Bool :=
  acceptsRelease baselineContext candidateContext qualified candidate
    (it.lo, ic.lo) (ct.hi, cc.hi)

/-- Exactness is inherited from scoped release admission; there is no
    second independently maintained behavior or point-cost gate. -/
theorem acceptsReplacement_iff {B Context : Type}
    [DecidableEq B] [DecidableEq Context]
    (baselineContext candidateContext : Context)
    (qualified candidate : List B) (ct cc it ic : Bounds) :
    acceptsReplacement baselineContext candidateContext qualified candidate ct cc it ic = true ↔
      candidateContext = baselineContext ∧
      (∀ b ∈ qualified, b ∈ candidate) ∧ weaklySeparated ct cc it ic :=
  acceptsRelease_iff baselineContext candidateContext qualified candidate
    (it.lo, ic.lo) (ct.hi, cc.hi)

/-- Accepted interval replacement preserves scope and qualified behavior
    and is no worse than the incumbent under every contained realization. -/
theorem replacement_no_regression {B Context : Type}
    [DecidableEq B] [DecidableEq Context]
    {baselineContext candidateContext : Context}
    {qualified candidate : List B} {ct cc it ic : Bounds}
    (h : acceptsReplacement baselineContext candidateContext qualified candidate ct cc it ic = true)
    {candidateCost incumbentCost : Point}
    (hc : realizes ct cc candidateCost)
    (hi : realizes it ic incumbentCost) :
    candidateContext = baselineContext ∧
    (∀ b ∈ qualified, b ∈ candidate) ∧ noWorse candidateCost incumbentCost := by
  have accepted := (acceptsReplacement_iff baselineContext candidateContext
    qualified candidate ct cc it ic).mp h
  exact ⟨accepted.1, accepted.2.1, weaklySeparated_sound accepted.2.2 hc hi⟩

/-- Scope mismatch cannot silently reuse performance evidence. -/
example : acceptsRelease "venue-A/workload-1" "venue-B/workload-1"
    [1, 2] [1, 2] (10, 10) (1, 1) = false := by decide

/-- An incomparable frontier trade-off is rejected, not relabeled an improvement. -/
example : acceptsRelease "same-scope" "same-scope"
    [1, 2] [1, 2] (1, 10) (10, 1) = false := by decide

example : acceptsRelease "same-scope" "same-scope"
    [1, 2] [1, 2] (10, 10) (1, 10) = true := by decide

example : acceptsRelease "same-scope" "same-scope"
    [1, 2] [1] (10, 10) (1, 1) = false := by decide

#print axioms frontier_can_regress
#print axioms admitted_frontier_exists
#print axioms admitted_frontier_sound
#print axioms acceptsRelease_iff

/-- Exactly the robust dominance test for the full Cartesian product of the
    two boxes. For a constrained joint distribution the corner pair might
    be impossible and only the original sound direction applies. -/
theorem separated_iff_all (ct cc it ic : Bounds) :
    separated ct cc it ic ↔
      ∀ x y, realizes ct cc x → realizes it ic y → dominates x y := by
  constructor
  · intro h x y hx hy
    exact separated_sound h hx hy
  · intro h
    exact h (ct.hi,cc.hi) (it.lo,ic.lo)
      ⟨ct.valid, Nat.le_refl _, cc.valid, Nat.le_refl _⟩
      ⟨Nat.le_refl _, it.valid, Nat.le_refl _, ic.valid⟩

/-- The interval replacement gate is complete for its matching context and
    behavior criteria and the full Cartesian boxes on both cost axes. -/
theorem replacement_iff_all {B Context : Type} [DecidableEq B] [DecidableEq Context]
    (before after : Context) (required observed : List B) (ct cc it ic : Bounds) :
    acceptsReplacement before after required observed ct cc it ic = true ↔
      after = before ∧ (∀ b ∈ required, b ∈ observed) ∧
      ∀ x y, realizes ct cc x → realizes it ic y → noWorse x y := by
  rw [acceptsReplacement_iff]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h x y hx hy
    exact weaklySeparated_sound h hx hy
  · intro h
    exact h (ct.hi,cc.hi) (it.lo,ic.lo)
      ⟨ct.valid, Nat.le_refl _, cc.valid, Nat.le_refl _⟩
      ⟨Nat.le_refl _, it.valid, Nat.le_refl _, ic.valid⟩

#print axioms separated_iff_all
#print axioms replacement_iff_all

end Pareto
end SoftwareIsQuantifiable
