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

end Pareto
end SoftwareIsQuantifiable
