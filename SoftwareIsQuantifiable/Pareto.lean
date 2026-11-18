import SoftwareIsQuantifiable.Interface

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
    the same candidate set — the regression-freedom content of the
    acceptance discipline (§21.3): an output the incumbent dominated
    would not be on the frontier.
  * Refinement is monotone (§20.2): witnesses only shrink intervals,
    and a pair decided under wider bounds stays decided under
    narrower ones.
  * The regression gate is exact: the check accepts a candidate if
    and only if it drops no previously qualified behavior.

  What is DISPROVEN:
  * The per-execution strengthening — "a dominated schedule finishes
    worse on every single execution" — is false, by a concrete
    counterexample (spec §20.4 names this boundary itself: dominance
    holds at the level of bounds, not per single execution).
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
        (List.mem_cons_self _ _) (Nat.le_refl _) with
    | intro y hy => exact ⟨y, hy.1, hy.2.2⟩

/-- **No output is dominated by a named incumbent.** If the incumbent
    is in the candidate set and the output is a frontier element of
    that set, the incumbent does not dominate the output: a candidate
    ordering that the previously qualified ordering dominated is
    never the output. -/
theorem frontier_not_dominated {L : List Point} {out inc : Point}
    (hout : out ∈ L) (hinc : inc ∈ L)
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
      have ha : a ∈ candidate := h a (List.mem_cons_self _ _)
      have hq : accepts q candidate = true :=
        IH.mpr (fun b hb => h b (List.mem_cons_of_mem _ hb))
      have hdec : decide (a ∈ candidate) = true := by
        cases hd : decide (a ∈ candidate) with
        | true => rfl
        | false => exact (of_decide_eq_false hd ha).elim
      show (decide (a ∈ candidate) && accepts q candidate) = true
      rw [hdec, hq]
      rfl

/-- **DISPROOF — per-execution dominance is false** (§20.4's own
    named boundary). Take schedule X with witnessed time bounds
    [1, 100] and schedule Y with witnessed time bounds [2, 3]
    (compute equal). The claim "every realization of Y beats every
    realization of X" is false: X can realize 1 while Y realizes 3.
    Dominance in this design is a statement about bounds, never
    about a single execution. -/
theorem not_per_execution_dominance :
    ¬ ∀ x y : Point,
      (1 ≤ x.1 ∧ x.1 ≤ 100 ∧ x.2 = 0) →
      (2 ≤ y.1 ∧ y.1 ≤ 3 ∧ y.2 = 0) →
      y.1 < x.1 := by
  intro h
  have := h (1, 0) (3, 0) (by simp) (by simp)
  simp at this

/-- Sum of two consistent interval bounds. -/
def addBounds (a b : Bounds) : Bounds where
  lo := a.lo + b.lo
  hi := a.hi + b.hi
  valid := Nat.add_le_add a.valid b.valid

/-- Pointwise maximum of two consistent interval bounds. -/
def maxBounds (a b : Bounds) : Bounds where
  lo := max a.lo b.lo
  hi := max a.hi b.hi
  valid := Nat.max_le.mpr
    ⟨Nat.le_trans a.valid (Nat.le_max_left _ _),
     Nat.le_trans b.valid (Nat.le_max_right _ _)⟩

theorem max_le_max {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left _ _),
    Nat.le_trans h2 (Nat.le_max_right _ _)⟩

theorem max_lt_max {a b c d : Nat} (h1 : a < c) (h2 : b < d) :
    max a b < max c d := by
  by_cases h : a ≤ b
  · rw [Nat.max_def]
    simp [h]
    exact Nat.lt_of_lt_of_le h2 (Nat.le_max_right c d)
  · rw [Nat.max_def]
    simp [h]
    exact Nat.lt_of_lt_of_le h1 (Nat.le_max_left c d)

/-- **Sequential composition preserves separation.** Summing both axes
    of two separated pairs (one component after another) stays separated. -/
theorem separated_sum
    {ct cc it ic ct2 cc2 it2 ic2 : Bounds}
    (h1 : separated ct cc it ic) (h2 : separated ct2 cc2 it2 ic2) :
    separated (addBounds ct ct2) (addBounds cc cc2)
      (addBounds it it2) (addBounds ic ic2) := by
  obtain ⟨t1, c1, s1⟩ := h1
  obtain ⟨t2, c2, _⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · show ct.hi + ct2.hi ≤ it.lo + it2.lo
    exact Nat.add_le_add t1 t2
  · show cc.hi + cc2.hi ≤ ic.lo + ic2.lo
    exact Nat.add_le_add c1 c2
  · rcases s1 with st | sc
    · exact Or.inl (by
        show ct.hi + ct2.hi < it.lo + it2.lo
        exact Nat.add_lt_add_of_lt_of_le st t2)
    · exact Or.inr (by
        show cc.hi + cc2.hi < ic.lo + ic2.lo
        exact Nat.add_lt_add_of_lt_of_le sc c2)

/-- **Parallel makespan preserves separation.** Time is the max of the
    component time bounds (they overlap); compute still sums. Strictness
    survives: if both time gaps are strict the max is strict, and if
    either compute gap is strict the sum is strict. A component that is
    separated must be strict on at least one axis, so one of those
    cases always applies. -/
theorem separated_parallel
    {ct cc it ic ct2 cc2 it2 ic2 : Bounds}
    (h1 : separated ct cc it ic) (h2 : separated ct2 cc2 it2 ic2) :
    separated (maxBounds ct ct2) (addBounds cc cc2)
      (maxBounds it it2) (addBounds ic ic2) := by
  obtain ⟨t1, c1, s1⟩ := h1
  obtain ⟨t2, c2, s2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · show max ct.hi ct2.hi ≤ max it.lo it2.lo
    exact max_le_max t1 t2
  · show cc.hi + cc2.hi ≤ ic.lo + ic2.lo
    exact Nat.add_le_add c1 c2
  · rcases s1 with st1 | sc1
    · rcases s2 with st2 | sc2
      · exact Or.inl (by
          show max ct.hi ct2.hi < max it.lo it2.lo
          exact max_lt_max st1 st2)
      · exact Or.inr (by
          show cc.hi + cc2.hi < ic.lo + ic2.lo
          exact Nat.add_lt_add_of_le_of_lt c1 sc2)
    · exact Or.inr (by
        show cc.hi + cc2.hi < ic.lo + ic2.lo
        exact Nat.add_lt_add_of_lt_of_le sc1 c2)

def weight2 (w1 w2 : Nat) (p : Point) : Nat := w1 * p.1 + w2 * p.2

/-- A positive weighted sum cannot select the non-supported Pareto
    point `(2, 2)` against `(0, 3)` and `(3, 0)`. `(2, 2)` is
    undominated (`scalar_frontier_point`) and still not a minimizer of
    any positive weights. -/
theorem not_scalarized :
    ¬ ∃ w1 w2 : Nat, 0 < w1 ∧ 0 < w2 ∧
        weight2 w1 w2 (2, 2) ≤ weight2 w1 w2 (0, 3) ∧
        weight2 w1 w2 (2, 2) ≤ weight2 w1 w2 (3, 0) := by
  intro h
  rcases h with ⟨w1, w2, hw1, hw2, hA, hC⟩
  simp [weight2] at hA hC
  have hA' : 2 * w1 ≤ w2 := by omega
  have hC' : 2 * w2 ≤ w1 := by omega
  omega

theorem weighted_strict {w1 w2 a b c d : Nat}
    (hw1 : 0 < w1) (hw2 : 0 < w2)
    (h1 : a ≤ b) (h2 : c ≤ d) (hs : a < b ∨ c < d) :
    w1 * a + w2 * c < w1 * b + w2 * d := by
  rcases hs with hs | hs
  · exact Nat.add_lt_add_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left hs hw1) (Nat.mul_le_mul_left w2 h2)
  · exact Nat.add_lt_add_of_le_of_lt
      (Nat.mul_le_mul_left w1 h1) (Nat.mul_lt_mul_of_pos_left hs hw2)

/-- A positive-weight scalar minimum is undominated. The converse is
    false: `not_scalarized`. -/
theorem scalar_optimum_undominated {w1 w2 : Nat} {L : List Point} {y : Point}
    (hw1 : 0 < w1) (hw2 : 0 < w2) (_hy : y ∈ L)
    (hopt : ∀ z ∈ L, weight2 w1 w2 y ≤ weight2 w1 w2 z) :
    ∀ z ∈ L, ¬ dominates z y := by
  intro z hz hdom
  obtain ⟨h1, h2, h3⟩ := hdom
  have hlt := weighted_strict hw1 hw2 h1 h2 h3
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (hopt z hz) hlt)

def dominatesB (a b : Point) : Bool :=
  decide (a.1 ≤ b.1) && decide (a.2 ≤ b.2) &&
    (decide (a.1 < b.1) || decide (a.2 < b.2))

theorem dominatesB_iff (a b : Point) :
    dominatesB a b = true ↔ dominates a b := by
  simp only [dominatesB, dominates, Bool.and_eq_true_iff, Bool.or_eq_true_iff,
    decide_eq_true_iff]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

instance (a b : Point) : Decidable (dominates a b) :=
  if h : dominatesB a b then
    isTrue ((dominatesB_iff a b).mp h)
  else
    isFalse (fun h' => h ((dominatesB_iff a b).mpr h'))

/-- The Pareto frontier of a finite candidate list: those no candidate dominates. -/
def frontier (L : List Point) : List Point :=
  L.filter (fun x => !(L.any (fun z => dominatesB z x)))

theorem frontier_exact {L : List Point} {x : Point} :
    x ∈ frontier L ↔ x ∈ L ∧ ∀ z ∈ L, ¬ dominates z x := by
  constructor
  · intro h
    have hmem := List.mem_filter.mp h
    refine ⟨hmem.1, ?_⟩
    intro z hz hdom
    have hany : L.any (fun y => dominatesB y x) = true :=
      List.any_eq_true.mpr ⟨z, hz, (dominatesB_iff z x).mpr hdom⟩
    have hnot := hmem.2
    rw [hany] at hnot
    cases hnot
  · intro h
    apply List.mem_filter.mpr
    refine ⟨h.1, ?_⟩
    cases hb : L.any (fun z => dominatesB z x) with
    | false => rfl
    | true =>
      rcases List.any_eq_true.mp hb with ⟨z, hz, hd⟩
      exact absurd ((dominatesB_iff z x).mp hd) (h.2 z hz)

theorem frontier_antichain {L : List Point} {x y : Point}
    (hx : x ∈ frontier L) (hy : y ∈ frontier L) : ¬ dominates x y :=
  (frontier_exact.mp hy).2 x (frontier_exact.mp hx).1

/-- `(2, 2)` is on the frontier of `{(0,3),(2,2),(3,0)}` and is still
    not a positive scalar minimum (`not_scalarized`). -/
theorem scalar_frontier_point :
    (2, 2) ∈ frontier [(0, 3), (2, 2), (3, 0)] := by
  decide

def minkowski (A B : List Point) : List Point :=
  A.flatMap (fun a => B.map (fun b => (a.1 + b.1, a.2 + b.2)))

theorem dominates_add_left {a a' b : Point} (h : dominates a' a) :
    dominates (a'.1 + b.1, a'.2 + b.2) (a.1 + b.1, a.2 + b.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem dominates_add_right {a b b' : Point} (h : dominates b' b) :
    dominates (a.1 + b'.1, a.2 + b'.2) (a.1 + b.1, a.2 + b.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- An undominated sum is a sum of undominated points. Dominated
    summands cannot appear on the frontier of the Minkowski sum. -/
theorem minkowski_frontier_subset {A B : List Point} {a b : Point}
    (ha : a ∈ A) (hb : b ∈ B)
    (hund : ∀ z ∈ minkowski A B, ¬ dominates z (a.1 + b.1, a.2 + b.2)) :
    (∀ a' ∈ A, ¬ dominates a' a) ∧ (∀ b' ∈ B, ¬ dominates b' b) := by
  constructor
  · intro a' ha' hdom
    apply hund (a'.1 + b.1, a'.2 + b.2)
    · exact List.mem_flatMap.mpr ⟨a', ha', List.mem_map.mpr ⟨b, hb, rfl⟩⟩
    · exact dominates_add_left hdom
  · intro b' hb' hdom
    apply hund (a.1 + b'.1, a.2 + b'.2)
    · exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b', hb', rfl⟩⟩
    · exact dominates_add_right hdom

/-- The converse fails. `(0,3)+(3,0) = (3,3)` sums two frontier points
    and is dominated by `(2,0)+(0,2) = (2,2)`, which is also a sum of
    frontier points. -/
theorem not_frontier_minkowski :
    (∀ a' ∈ ([(0, 3), (2, 0)] : List Point), ¬ dominates a' (0, 3)) ∧
    (∀ b' ∈ ([(0, 2), (3, 0)] : List Point), ¬ dominates b' (3, 0)) ∧
    ∃ z ∈ minkowski [(0, 3), (2, 0)] [(0, 2), (3, 0)], dominates z (3, 3) := by
  decide

/-- The two-axis order of this module is the `Interface` profile order
    on a time/compute measure space, both axes `minimize`, observed
    behavior held. -/
inductive CostAxis where
  | time
  | compute
  deriving DecidableEq, Repr

def costSpace : Interface.MeasureSpace CostAxis :=
  [{ measure := .time, polarity := .minimize },
   { measure := .compute, polarity := .minimize }]

def profileOf (x : Point) : Interface.Profile Unit CostAxis where
  symbol := ()
  readings := [x.1, x.2]
  observed := true

theorem dominates_iff_interface (x y : Point) :
    dominates x y ↔
      Interface.dominates costSpace (profileOf x) (profileOf y) := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨⟨⟨rfl, ?_⟩, fun _ => rfl⟩, ?_⟩
    · exact ⟨h1, ⟨h2, trivial⟩⟩
    · rcases h3 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · intro h
    obtain ⟨⟨⟨_, haxes⟩, _⟩, hlt⟩ := h
    obtain ⟨h1, hrest⟩ := haxes
    obtain ⟨h2, _⟩ := hrest
    refine ⟨h1, h2, ?_⟩
    rcases hlt with h | h
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr h
      · cases h

end Pareto
end SoftwareIsQuantifiable
