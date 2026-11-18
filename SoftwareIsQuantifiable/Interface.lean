/-
  Stable interface for the downstream developments that take this
  repository as their base layer:

  * `software-optimality`
  * `software-is-composable`
  * `software-is-incrementally-certifiable`
  * `software-is-incrementally-safe`
  * `software-doesnt-have-to-regress`

  The module is self-contained (Lean prelude only) so a downstream
  repository can `import SoftwareIsQuantifiable.Interface` or mirror
  this file. Nothing here is release-sequence monotonicity: that
  obligation belongs to `software-is-composable`. What is here is the
  shared vocabulary those proofs quantify over — a measure space, a
  per-symbol profile, the profile preorder, and Pareto dominance —
  together with the composition laws (products of measure spaces,
  assemblies of symbols) and the boundaries where a plausible
  strengthening is false.

  Smaller is better on a `minimize` axis and worse on a `maximize`
  axis. An axis that a caller would rather maximize must be given
  polarity `maximize` here, not silently reversed.
-/

namespace SoftwareIsQuantifiable
namespace Interface

/-- Whether a larger reading is worse (`minimize`: cost, latency,
    defect count) or better (`maximize`: attained quality). -/
inductive Polarity where
  | minimize
  | maximize
  deriving DecidableEq, Repr

/-- One reading is no worse than another on an axis of the given polarity. -/
def axisLe (p : Polarity) (a b : Nat) : Prop :=
  match p with
  | .minimize => a ≤ b
  | .maximize => b ≤ a

/-- One reading is strictly better than another on an axis. -/
def axisLt (p : Polarity) (a b : Nat) : Prop :=
  match p with
  | .minimize => a < b
  | .maximize => b < a

theorem axisLe_refl (p : Polarity) (a : Nat) : axisLe p a a := by
  cases p <;> exact Nat.le_refl a

theorem axisLe_trans {p : Polarity} {a b c : Nat}
    (h1 : axisLe p a b) (h2 : axisLe p b c) : axisLe p a c := by
  cases p with
  | minimize => exact Nat.le_trans h1 h2
  | maximize => exact Nat.le_trans h2 h1

theorem axisLe_antisymm {p : Polarity} {a b : Nat}
    (h1 : axisLe p a b) (h2 : axisLe p b a) : a = b := by
  cases p with
  | minimize => exact Nat.le_antisymm h1 h2
  | maximize => exact Nat.le_antisymm h2 h1

theorem not_axisLt_self (p : Polarity) (a : Nat) : ¬ axisLt p a a := by
  cases p <;> exact Nat.lt_irrefl a

/-- A strict improvement survives a further non-strict step. -/
theorem axisLt_trans_le {p : Polarity} {a b c : Nat}
    (hlt : axisLt p a b) (hle : axisLe p b c) : axisLt p a c := by
  cases p with
  | minimize => exact Nat.lt_of_lt_of_le hlt hle
  | maximize => exact Nat.lt_of_le_of_lt hle hlt

/-- A non-strict step into a strict improvement is still strict. -/
theorem axisLe_trans_lt {p : Polarity} {a b c : Nat}
    (hle : axisLe p a b) (hlt : axisLt p b c) : axisLt p a c := by
  cases p with
  | minimize => exact Nat.lt_of_le_of_lt hle hlt
  | maximize => exact Nat.lt_of_lt_of_le hlt hle

theorem axisLt_le {p : Polarity} {a b : Nat} (h : axisLt p a b) : axisLe p a b := by
  cases p <;> exact Nat.le_of_lt h

def axisLeDec (p : Polarity) (a b : Nat) : Decidable (axisLe p a b) :=
  match p with
  | .minimize => inferInstanceAs (Decidable (a ≤ b))
  | .maximize => inferInstanceAs (Decidable (b ≤ a))

def axisLtDec (p : Polarity) (a b : Nat) : Decidable (axisLt p a b) :=
  match p with
  | .minimize => inferInstanceAs (Decidable (a < b))
  | .maximize => inferInstanceAs (Decidable (b < a))

instance (p : Polarity) (a b : Nat) : Decidable (axisLe p a b) := axisLeDec p a b

instance (p : Polarity) (a b : Nat) : Decidable (axisLt p a b) := axisLtDec p a b

/-- A named axis of a measure space, with the polarity of its reading. -/
structure Axis (Measure : Type) where
  /-- Which measure this coordinate is. -/
  measure : Measure
  /-- Whether smaller or larger readings are better. -/
  polarity : Polarity

/-- A measure space is a finite ordered list of axes. Position in the
    list is the position in a profile's reading vector: the space, not
    an external convention, says which coordinate is which measure.
    Duplicated axes are duplicated coordinates; the type does not
    quotient them. -/
abbrev MeasureSpace (Measure : Type) := List (Axis Measure)

/-- Componentwise no-worse comparison of reading vectors against a
    measure space. Vectors whose length differs from the space, or
    from each other, are not related. -/
def axesLe {Measure : Type} : MeasureSpace Measure → List Nat → List Nat → Prop
  | ax :: axs, a :: as, b :: bs => axisLe ax.polarity a b ∧ axesLe axs as bs
  | [], [], [] => True
  | _, _, _ => False

/-- Componentwise strict improvement somewhere along a measure space.
    Every coordinate is compared. A vector that does not cover the
    space is not a strict improvement, even when an early coordinate is. -/
def axesLt {Measure : Type} : MeasureSpace Measure → List Nat → List Nat → Prop
  | ax :: axs, a :: as, b :: bs =>
      (axisLt ax.polarity a b ∧ axesLe axs as bs) ∨
        (axisLe ax.polarity a b ∧ axesLt axs as bs)
  | _, _, _ => False

def axesLeDec {Measure : Type} :
    (sp : MeasureSpace Measure) → (a b : List Nat) → Decidable (axesLe sp a b)
  | ax :: axs, x :: xs, y :: ys =>
      match axisLeDec ax.polarity x y, axesLeDec axs xs ys with
      | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
      | isFalse h1, _ => isFalse fun h => h1 h.1
      | _, isFalse h2 => isFalse fun h => h2 h.2
  | [], [], [] => isTrue trivial
  | [], [], _ :: _ => isFalse fun h => h
  | [], _ :: _, _ => isFalse fun h => h
  | _ :: _, [], _ => isFalse fun h => h
  | _ :: _, _ :: _, [] => isFalse fun h => h

def axesLtDec {Measure : Type} :
    (sp : MeasureSpace Measure) → (a b : List Nat) → Decidable (axesLt sp a b)
  | ax :: axs, x :: xs, y :: ys =>
      match axisLtDec ax.polarity x y with
      | isTrue hlt =>
          match axesLeDec axs xs ys with
          | isTrue hle => isTrue (Or.inl ⟨hlt, hle⟩)
          | isFalse hnle =>
              match axisLeDec ax.polarity x y, axesLtDec axs xs ys with
              | isTrue hleH, isTrue hltT => isTrue (Or.inr ⟨hleH, hltT⟩)
              | isFalse hleH, _ =>
                  isFalse fun h => h.elim (fun p => hnle p.2) (fun p => hleH p.1)
              | _, isFalse hltT =>
                  isFalse fun h => h.elim (fun p => hnle p.2) (fun p => hltT p.2)
      | isFalse hnlt =>
          match axisLeDec ax.polarity x y, axesLtDec axs xs ys with
          | isTrue hleH, isTrue hltT => isTrue (Or.inr ⟨hleH, hltT⟩)
          | isFalse hleH, _ =>
              isFalse fun h => h.elim (fun p => hnlt p.1) (fun p => hleH p.1)
          | _, isFalse hltT =>
              isFalse fun h => h.elim (fun p => hnlt p.1) (fun p => hltT p.2)
  | [], _, _ => isFalse fun h => h
  | _ :: _, [], _ => isFalse fun h => h
  | _ :: _, _ :: _, [] => isFalse fun h => h

instance {Measure : Type} (sp : MeasureSpace Measure) (a b : List Nat) :
    Decidable (axesLe sp a b) :=
  axesLeDec sp a b

instance {Measure : Type} (sp : MeasureSpace Measure) (a b : List Nat) :
    Decidable (axesLt sp a b) :=
  axesLtDec sp a b

theorem axesLe_refl {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a : List Nat),
      a.length = sp.length → axesLe sp a a := by
  intro sp
  induction sp with
  | nil =>
    intro a h
    cases a with
    | nil => exact trivial
    | cons _ _ => simp at h
  | cons ax axs IH =>
    intro a h
    cases a with
    | nil => simp at h
    | cons x xs =>
      have hx : xs.length = axs.length := by
        simp [List.length] at h
        omega
      exact ⟨axisLe_refl ax.polarity x, IH xs hx⟩

theorem axesLe_length {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b : List Nat),
      axesLe sp a b → a.length = sp.length ∧ b.length = sp.length := by
  intro sp
  induction sp with
  | nil =>
    intro a b h
    cases a with
    | nil =>
      cases b with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => cases h
    | cons _ _ => cases h
  | cons ax axs IH =>
    intro a b h
    cases a with
    | nil => cases h
    | cons x xs =>
      cases b with
      | nil => cases h
      | cons y ys =>
        obtain ⟨_, ht⟩ := h
        obtain ⟨hl, hr⟩ := IH xs ys ht
        simp [List.length, hl, hr]

theorem axesLe_trans {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b c : List Nat),
      axesLe sp a b → axesLe sp b c → axesLe sp a c := by
  intro sp
  induction sp with
  | nil =>
    intro a b c hab hbc
    cases a with
    | nil =>
      cases b with
      | nil =>
        cases c with
        | nil => exact trivial
        | cons _ _ => cases hbc
      | cons _ _ => cases hab
    | cons _ _ => cases hab
  | cons ax axs IH =>
    intro a b c hab hbc
    cases a with
    | nil => cases hab
    | cons xa xas =>
      cases b with
      | nil => cases hab
      | cons xb xbs =>
        cases c with
        | nil => cases hbc
        | cons xc xcs =>
          obtain ⟨h1, ht1⟩ := hab
          obtain ⟨h2, ht2⟩ := hbc
          exact ⟨axisLe_trans h1 h2, IH xas xbs xcs ht1 ht2⟩

theorem axesLe_antisymm {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b : List Nat),
      axesLe sp a b → axesLe sp b a → a = b := by
  intro sp
  induction sp with
  | nil =>
    intro a b hab hba
    cases a with
    | nil =>
      cases b with
      | nil => rfl
      | cons _ _ => cases hab
    | cons _ _ => cases hab
  | cons ax axs IH =>
    intro a b hab hba
    cases a with
    | nil => cases hab
    | cons xa xas =>
      cases b with
      | nil => cases hab
      | cons xb xbs =>
        obtain ⟨h1, ht1⟩ := hab
        obtain ⟨h2, ht2⟩ := hba
        have hx : xa = xb := axisLe_antisymm h1 h2
        have hxs : xas = xbs := IH xas xbs ht1 ht2
        subst hx
        subst hxs
        rfl

theorem axesLt_le {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b : List Nat),
      axesLt sp a b → axesLe sp a b := by
  intro sp
  induction sp with
  | nil =>
    intro a b h
    cases a <;> cases h
  | cons ax axs IH =>
    intro a b h
    cases a with
    | nil => cases h
    | cons xa xas =>
      cases b with
      | nil => cases h
      | cons xb xbs =>
        cases h with
        | inl hlt => exact ⟨axisLt_le hlt.1, hlt.2⟩
        | inr hle => exact ⟨hle.1, IH xas xbs hle.2⟩

theorem axesLt_irrefl {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a : List Nat), ¬ axesLt sp a a := by
  intro sp
  induction sp with
  | nil =>
    intro a h
    cases a <;> cases h
  | cons ax axs IH =>
    intro a h
    cases a with
    | nil => cases h
    | cons x xs =>
      cases h with
      | inl hlt => exact not_axisLt_self ax.polarity x hlt.1
      | inr hrest => exact IH xs hrest.2

/-- A strict first coordinate on a vector that does not cover the
    space is not `axesLt`. -/
theorem not_axesLt_of_short_vector :
    ¬ axesLt
        ([ { measure := (), polarity := .minimize },
           { measure := (), polarity := .minimize } ] : MeasureSpace Unit)
        [0] [1, 9] := by
  intro h
  cases h with
  | inl h => cases h.2
  | inr h => cases h.2

theorem axesLt_trans_le {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b c : List Nat),
      axesLe sp b c → axesLt sp a b → axesLt sp a c := by
  intro sp
  induction sp with
  | nil =>
    intro a b c _ hlt
    cases a <;> cases hlt
  | cons ax axs IH =>
    intro a b c hle hlt
    cases a with
    | nil => cases hlt
    | cons xa xas =>
      cases b with
      | nil => cases hlt
      | cons xb xbs =>
        cases c with
        | nil => cases hle
        | cons xc xcs =>
          obtain ⟨hleh, hlet⟩ := hle
          cases hlt with
          | inl hltH =>
            exact Or.inl ⟨axisLt_trans_le hltH.1 hleh,
              axesLe_trans axs xas xbs xcs hltH.2 hlet⟩
          | inr hltT =>
            exact Or.inr ⟨axisLe_trans hltT.1 hleh, IH xas xbs xcs hlet hltT.2⟩

theorem axesLe_trans_lt {Measure : Type} :
    ∀ (sp : MeasureSpace Measure) (a b c : List Nat),
      axesLe sp a b → axesLt sp b c → axesLt sp a c := by
  intro sp
  induction sp with
  | nil =>
    intro a b c _ hlt
    cases b <;> cases hlt
  | cons ax axs IH =>
    intro a b c hle hlt
    cases a with
    | nil => cases hle
    | cons xa xas =>
      cases b with
      | nil => cases hle
      | cons xb xbs =>
        cases c with
        | nil => cases hlt
        | cons xc xcs =>
          obtain ⟨hleh, hlet⟩ := hle
          cases hlt with
          | inl hltH =>
            exact Or.inl ⟨axisLe_trans_lt hleh hltH.1,
              axesLe_trans axs xas xbs xcs hlet hltH.2⟩
          | inr hltT =>
            exact Or.inr ⟨axisLe_trans hleh hltT.1, IH xas xbs xcs hlet hltT.2⟩

/-- Splitting a no-worse comparison across a concatenation of measure
    spaces, when the left reading vectors have the left space's length. -/
theorem axesLe_append {Measure : Type} :
    ∀ (sp1 sp2 : MeasureSpace Measure) (a1 b1 a2 b2 : List Nat),
      a1.length = sp1.length → b1.length = sp1.length →
      (axesLe (sp1 ++ sp2) (a1 ++ a2) (b1 ++ b2) ↔
        axesLe sp1 a1 b1 ∧ axesLe sp2 a2 b2) := by
  intro sp1
  induction sp1 with
  | nil =>
    intro sp2 a1 b1 a2 b2 ha hb
    cases a1 with
    | nil =>
      cases b1 with
      | nil =>
        simp [axesLe]
      | cons _ _ => simp at hb
    | cons _ _ => simp at ha
  | cons ax axs IH =>
    intro sp2 a1 b1 a2 b2 ha hb
    cases a1 with
    | nil => simp at ha
    | cons xa xas =>
      cases b1 with
      | nil => simp at hb
      | cons xb xbs =>
        have hxa : xas.length = axs.length := by
          simp [List.length] at ha
          omega
        have hxb : xbs.length = axs.length := by
          simp [List.length] at hb
          omega
        constructor
        · intro h
          obtain ⟨hh, ht⟩ := h
          obtain ⟨hl, hr⟩ := (IH sp2 xas xbs a2 b2 hxa hxb).mp ht
          exact ⟨⟨hh, hl⟩, hr⟩
        · intro h
          exact ⟨h.1.1, (IH sp2 xas xbs a2 b2 hxa hxb).mpr ⟨h.1.2, h.2⟩⟩

/-- A strict coordinate on one side of a concatenated measure space is
    a strict coordinate of the concatenation when the other side is no
    worse, and conversely. A strict side does not hide a regression on
    the other side. -/
theorem axesLt_append {Measure : Type} :
    ∀ (sp1 sp2 : MeasureSpace Measure) (a1 b1 a2 b2 : List Nat),
      a1.length = sp1.length → b1.length = sp1.length →
      (axesLt (sp1 ++ sp2) (a1 ++ a2) (b1 ++ b2) ↔
        (axesLt sp1 a1 b1 ∧ axesLe sp2 a2 b2) ∨
          (axesLe sp1 a1 b1 ∧ axesLt sp2 a2 b2)) := by
  intro sp1
  induction sp1 with
  | nil =>
    intro sp2 a1 b1 a2 b2 ha hb
    cases a1 with
    | nil =>
      cases b1 with
      | nil =>
        simp [axesLt, axesLe]
      | cons _ _ => simp at hb
    | cons _ _ => simp at ha
  | cons ax axs IH =>
    intro sp2 a1 b1 a2 b2 ha hb
    cases a1 with
    | nil => simp at ha
    | cons xa xas =>
      cases b1 with
      | nil => simp at hb
      | cons xb xbs =>
        have hxa : xas.length = axs.length := by
          simp [List.length] at ha
          omega
        have hxb : xbs.length = axs.length := by
          simp [List.length] at hb
          omega
        constructor
        · intro h
          cases h with
          | inl hlt =>
            obtain ⟨hleL, hleR⟩ :=
              (axesLe_append axs sp2 xas xbs a2 b2 hxa hxb).mp hlt.2
            exact Or.inl ⟨Or.inl ⟨hlt.1, hleL⟩, hleR⟩
          | inr hrest =>
            cases (IH sp2 xas xbs a2 b2 hxa hxb).mp hrest.2 with
            | inl hl => exact Or.inl ⟨Or.inr ⟨hrest.1, hl.1⟩, hl.2⟩
            | inr hr => exact Or.inr ⟨⟨hrest.1, hr.1⟩, hr.2⟩
        · intro h
          cases h with
          | inl hl =>
            cases hl.1 with
            | inl hhead =>
              exact Or.inl ⟨hhead.1,
                (axesLe_append axs sp2 xas xbs a2 b2 hxa hxb).mpr ⟨hhead.2, hl.2⟩⟩
            | inr htail =>
              exact Or.inr ⟨htail.1,
                (IH sp2 xas xbs a2 b2 hxa hxb).mpr (Or.inl ⟨htail.2, hl.2⟩)⟩
          | inr hr =>
            exact Or.inr ⟨hr.1.1,
              (IH sp2 xas xbs a2 b2 hxa hxb).mpr (Or.inr ⟨hr.1.2, hr.2⟩)⟩

/-- The observed profile of one symbol on one measure space.

    `readings` is positional in the measure space. `observed` is the
    separate fact that the symbol's named behavior held; it is not a
    measure and it is not inferred from the readings. -/
structure Profile (Symbol Measure : Type) where
  /-- The symbol this profile speaks about. -/
  symbol : Symbol
  /-- One natural reading per axis of the measure space, in order. -/
  readings : List Nat
  /-- Whether the symbol's named observed behavior held. -/
  observed : Bool

/-- A profile is aligned with a measure space when it has one reading
    per axis. The preorder is reflexive on aligned profiles. -/
abbrev aligned {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p : Profile Symbol Measure) : Prop :=
  p.readings.length = space.length

/-- Measure preorder on profiles: same symbol, and no worse on every
    axis. The observed-behavior bit is ignored here. -/
def measuresLe {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) : Prop :=
  p.symbol = q.symbol ∧ axesLe space p.readings q.readings

/-- Previously observed behavior still holds. A profile that drops a
    behavior the incumbent exhibited is not `behaviorLe`, whatever its
    readings do. -/
def behaviorLe {Symbol Measure : Type}
    (p q : Profile Symbol Measure) : Prop :=
  q.observed = true → p.observed = true

/-- The profile preorder: measures no worse, and observed behavior
    preserved, for the same symbol. Reflexive on aligned profiles,
    transitive, and antisymmetric — so on aligned profiles it is a
    partial order. It is stated as a preorder because that is the
    property composition uses. -/
def noWorse {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) : Prop :=
  measuresLe space p q ∧ behaviorLe p q

/-- Strict improvement on at least one axis of the space. -/
def strictlyBetter {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) : Prop :=
  axesLt space p.readings q.readings

/-- Pareto dominance on profiles: `noWorse`, and strictly better on at
    least one measure. Dropping observed behavior blocks dominance
    even when every measure improves. Equal profiles do not dominate. -/
def dominates {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) : Prop :=
  noWorse space p q ∧ strictlyBetter space p q

instance {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) :
    Decidable (measuresLe space p q) :=
  inferInstanceAs (Decidable (p.symbol = q.symbol ∧ axesLe space p.readings q.readings))

instance {Symbol Measure : Type} (p q : Profile Symbol Measure) :
    Decidable (behaviorLe p q) :=
  inferInstanceAs (Decidable (q.observed = true → p.observed = true))

instance {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) :
    Decidable (strictlyBetter space p q) :=
  inferInstanceAs (Decidable (axesLt space p.readings q.readings))

instance {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) :
    Decidable (noWorse space p q) :=
  inferInstanceAs (Decidable (measuresLe space p q ∧ behaviorLe p q))

instance {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (p q : Profile Symbol Measure) :
    Decidable (dominates space p q) :=
  inferInstanceAs (Decidable (noWorse space p q ∧ strictlyBetter space p q))

theorem measuresLe_aligned {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q : Profile Symbol Measure}
    (h : measuresLe space p q) : aligned space p ∧ aligned space q := by
  obtain ⟨hl, hr⟩ := axesLe_length space p.readings q.readings h.2
  exact ⟨hl, hr⟩

theorem measuresLe_refl {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p : Profile Symbol Measure}
    (h : aligned space p) : measuresLe space p p :=
  ⟨rfl, axesLe_refl space p.readings h⟩

theorem measuresLe_trans {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q r : Profile Symbol Measure}
    (hpq : measuresLe space p q) (hqr : measuresLe space q r) :
    measuresLe space p r :=
  ⟨hpq.1.trans hqr.1, axesLe_trans space _ _ _ hpq.2 hqr.2⟩

theorem measuresLe_antisymm_readings {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q : Profile Symbol Measure}
    (hpq : measuresLe space p q) (hqp : measuresLe space q p) :
    p.symbol = q.symbol ∧ p.readings = q.readings :=
  ⟨hpq.1, axesLe_antisymm space _ _ hpq.2 hqp.2⟩

theorem behaviorLe_refl {Symbol Measure : Type} (p : Profile Symbol Measure) :
    behaviorLe p p :=
  fun h => h

theorem behaviorLe_trans {Symbol Measure : Type} {p q r : Profile Symbol Measure}
    (hpq : behaviorLe p q) (hqr : behaviorLe q r) : behaviorLe p r :=
  fun hr => hpq (hqr hr)

theorem noWorse_refl {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p : Profile Symbol Measure}
    (h : aligned space p) : noWorse space p p :=
  ⟨measuresLe_refl h, behaviorLe_refl p⟩

theorem noWorse_trans {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q r : Profile Symbol Measure}
    (hpq : noWorse space p q) (hqr : noWorse space q r) : noWorse space p r :=
  ⟨measuresLe_trans hpq.1 hqr.1, behaviorLe_trans hpq.2 hqr.2⟩

theorem noWorse_antisymm {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q : Profile Symbol Measure}
    (hpq : noWorse space p q) (hqp : noWorse space q p) : p = q := by
  have hsym : p.symbol = q.symbol := hpq.1.1
  have hread : p.readings = q.readings :=
    axesLe_antisymm space p.readings q.readings hpq.1.2 hqp.1.2
  have hobs : p.observed = q.observed := by
    cases hp : p.observed <;> cases hq : q.observed
    · rfl
    · have h := hpq.2 hq
      rw [hp] at h
      cases h
    · have h := hqp.2 hp
      rw [hq] at h
      cases h
    · rfl
  cases p with
  | mk sp rp op =>
    cases q with
    | mk sq rq oq =>
      cases hsym
      cases hread
      cases hobs
      rfl

theorem not_strictlyBetter_self {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p : Profile Symbol Measure) :
    ¬ strictlyBetter space p p :=
  axesLt_irrefl space p.readings

/-- Dominance is irreflexive, aligned or not. -/
theorem not_dominates_self {Symbol Measure : Type}
    (space : MeasureSpace Measure) (p : Profile Symbol Measure) :
    ¬ dominates space p p :=
  fun h => not_strictlyBetter_self space p h.2

theorem dominates_trans {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q r : Profile Symbol Measure}
    (hpq : dominates space p q) (hqr : dominates space q r) :
    dominates space p r := by
  refine ⟨noWorse_trans hpq.1 hqr.1, ?_⟩
  exact axesLt_trans_le space p.readings q.readings r.readings hqr.1.1.2 hpq.2

theorem dominates_noWorse {Symbol Measure : Type}
    {space : MeasureSpace Measure} {p q : Profile Symbol Measure}
    (h : dominates space p q) : noWorse space p q :=
  h.1

/-- Measure improvement does not dominate when observed behavior is
    dropped. Dominance is not the measure order alone. The witness is
    a one-axis minimize space: readings `0` against `1`, with the
    better reading dropping `observed`. -/
theorem not_dominates_from_measures :
    ∃ (space : MeasureSpace Unit) (p q : Profile Unit Unit),
      measuresLe space p q ∧ strictlyBetter space p q ∧ ¬ dominates space p q := by
  let space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
  let p : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  let q : Profile Unit Unit := { symbol := (), readings := [1], observed := true }
  refine ⟨space, p, q, ⟨rfl, ⟨Nat.zero_le _, trivial⟩⟩,
    Or.inl ⟨Nat.lt_succ_self 0, trivial⟩, ?_⟩
  intro hd
  have hobs : p.observed = true := hd.1.2 rfl
  cases hobs

/-- Profile of one symbol on the concatenation of two measure spaces.
    Observed behavior of the composite holds only when both parts'
    observed bits hold. The symbol is the shared symbol; profiles of
    distinct symbols are not concatenated. -/
def appendProfile {Symbol Measure : Type}
    (p q : Profile Symbol Measure) (_h : p.symbol = q.symbol) :
    Profile Symbol Measure where
  symbol := p.symbol
  readings := p.readings ++ q.readings
  observed := p.observed && q.observed

theorem behaviorLe_append {Symbol Measure : Type}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hb1 : behaviorLe p1 q1) (hb2 : behaviorLe p2 q2)
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol) :
    behaviorLe (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) := by
  intro h
  have hand : q1.observed = true ∧ q2.observed = true :=
    Bool.and_eq_true_iff.mp h
  show (p1.observed && p2.observed) = true
  rw [hb1 hand.1, hb2 hand.2]
  rfl

theorem measuresLe_append_iff {Symbol Measure : Type}
    {sp1 sp2 : MeasureSpace Measure}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol)
    (ha : aligned sp1 p1) (hb : aligned sp1 q1) :
    measuresLe (sp1 ++ sp2) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) ↔
      measuresLe sp1 p1 q1 ∧ measuresLe sp2 p2 q2 := by
  constructor
  · intro h
    have hsplit :=
      (axesLe_append sp1 sp2 p1.readings q1.readings p2.readings q2.readings ha hb).mp h.2
    have hsym2 : p2.symbol = q2.symbol := by
      rw [← hp, ← hq]
      exact h.1
    exact ⟨⟨h.1, hsplit.1⟩, ⟨hsym2, hsplit.2⟩⟩
  · intro h
    have hsym : p1.symbol = q1.symbol := h.1.1
    have haxes :=
      (axesLe_append sp1 sp2 p1.readings q1.readings p2.readings q2.readings ha hb).mpr
        ⟨h.1.2, h.2.2⟩
    exact ⟨hsym, haxes⟩

theorem noWorse_append {Symbol Measure : Type}
    {sp1 sp2 : MeasureSpace Measure}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol)
    (h1 : noWorse sp1 p1 q1) (h2 : noWorse sp2 p2 q2) :
    noWorse (sp1 ++ sp2) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) := by
  have ha : aligned sp1 p1 := (measuresLe_aligned h1.1).1
  have hb : aligned sp1 q1 := (measuresLe_aligned h1.1).2
  have hm :=
    (measuresLe_append_iff hp hq ha hb).mpr ⟨h1.1, h2.1⟩
  exact ⟨hm, behaviorLe_append h1.2 h2.2 hp hq⟩

/-- Conjunction of observed bits does not split. A component can drop
    behavior while the concatenated profile stays `noWorse`, when the
    other component's observed bit is already false and hides the
    conjunction. Component obligations have to be checked on the
    components. -/
theorem not_noWorse_append_converse :
    ∃ (sp : MeasureSpace Unit)
      (p1 q1 p2 q2 : Profile Unit Unit)
      (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol),
      noWorse (sp ++ sp) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) ∧
      ¬ noWorse sp p1 q1 := by
  let sp : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
  let p1 : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  let q1 : Profile Unit Unit := { symbol := (), readings := [0], observed := true }
  let p2 : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  let q2 : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  refine ⟨sp, p1, q1, p2, q2, rfl, rfl, ?_, ?_⟩
  · refine ⟨⟨rfl, ⟨Nat.le_refl _, ⟨Nat.le_refl _, trivial⟩⟩⟩, ?_⟩
    intro hobs
    cases hobs
  · intro hbad
    have : p1.observed = true := hbad.2 rfl
    cases this

theorem dominates_append_left {Symbol Measure : Type}
    {sp1 sp2 : MeasureSpace Measure}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol)
    (h1 : dominates sp1 p1 q1) (h2 : noWorse sp2 p2 q2) :
    dominates (sp1 ++ sp2) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) := by
  have hle := noWorse_append hp hq h1.1 h2
  have ha : aligned sp1 p1 := (measuresLe_aligned h1.1.1).1
  have hb : aligned sp1 q1 := (measuresLe_aligned h1.1.1).2
  have hlt :=
    (axesLt_append sp1 sp2 p1.readings q1.readings p2.readings q2.readings ha hb).mpr
      (Or.inl ⟨h1.2, h2.1.2⟩)
  exact ⟨hle, hlt⟩

theorem dominates_append_right {Symbol Measure : Type}
    {sp1 sp2 : MeasureSpace Measure}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol)
    (h1 : noWorse sp1 p1 q1) (h2 : dominates sp2 p2 q2) :
    dominates (sp1 ++ sp2) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) := by
  have hle := noWorse_append hp hq h1 h2.1
  have ha : aligned sp1 p1 := (measuresLe_aligned h1.1).1
  have hb : aligned sp1 q1 := (measuresLe_aligned h1.1).2
  have hlt :=
    (axesLt_append sp1 sp2 p1.readings q1.readings p2.readings q2.readings ha hb).mpr
      (Or.inr ⟨h1.1.2, h2.2⟩)
  exact ⟨hle, hlt⟩

/-- Product of profile orders, the direction that holds: both halves
    `noWorse`, and at least one half strictly better, yields dominance
    on the concatenated measure space. -/
theorem dominates_append_of_halves {Symbol Measure : Type}
    {sp1 sp2 : MeasureSpace Measure}
    {p1 q1 p2 q2 : Profile Symbol Measure}
    (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol)
    (h1 : noWorse sp1 p1 q1) (h2 : noWorse sp2 p2 q2)
    (hs : strictlyBetter sp1 p1 q1 ∨ strictlyBetter sp2 p2 q2) :
    dominates (sp1 ++ sp2) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) := by
  have hle := noWorse_append hp hq h1 h2
  have ha : aligned sp1 p1 := (measuresLe_aligned h1.1).1
  have hb : aligned sp1 q1 := (measuresLe_aligned h1.1).2
  have hlt :=
    (axesLt_append sp1 sp2 p1.readings q1.readings p2.readings q2.readings ha hb).mpr
      (hs.elim (fun hl => Or.inl ⟨hl, h2.1.2⟩) (fun hr => Or.inr ⟨h1.1.2, hr⟩))
  exact ⟨hle, hlt⟩

/-- Dominance on a concatenated space does not split into dominance,
    or even `noWorse`, on each half. Same hiding conjunction as
    `not_noWorse_append_converse`, with the visible half strict so the
    composite really does dominate. -/
theorem not_dominates_append_splits :
    ∃ (sp : MeasureSpace Unit)
      (p1 q1 p2 q2 : Profile Unit Unit)
      (hp : p1.symbol = p2.symbol) (hq : q1.symbol = q2.symbol),
      dominates (sp ++ sp) (appendProfile p1 p2 hp) (appendProfile q1 q2 hq) ∧
      ¬ noWorse sp p1 q1 := by
  let sp : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
  let p1 : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  let q1 : Profile Unit Unit := { symbol := (), readings := [0], observed := true }
  let p2 : Profile Unit Unit := { symbol := (), readings := [0], observed := false }
  let q2 : Profile Unit Unit := { symbol := (), readings := [1], observed := false }
  refine ⟨sp, p1, q1, p2, q2, rfl, rfl, ?_, ?_⟩
  · refine ⟨⟨⟨rfl, ⟨Nat.le_refl _, ⟨Nat.zero_le _, trivial⟩⟩⟩, ?_⟩, ?_⟩
    · intro hobs
      cases hobs
    · exact Or.inr ⟨Nat.le_refl _, Or.inl ⟨Nat.lt_succ_self 0, trivial⟩⟩
  · intro hbad
    have : p1.observed = true := hbad.2 rfl
    cases this

/-- A release is one profile per symbol the release names, over a
    shared measure space. Order in the list is not the order of
    comparison: profiles are matched by symbol. This is an assembly of
    components at one measurement, not a sequence of releases. -/
abbrev Release (Symbol Measure : Type) := List (Profile Symbol Measure)

/-- Each symbol occurs at most once. A second profile for the same
    symbol is a different claim, not a second witness for the first. -/
def uniqueSymbols {Symbol Measure : Type}
    (R : Release Symbol Measure) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, p.symbol = q.symbol → p = q

/-- The two assemblies name no symbol in common. -/
def symbolsDisjoint {Symbol Measure : Type}
    (left right : Release Symbol Measure) : Prop :=
  ∀ p ∈ left, ∀ q ∈ right, p.symbol ≠ q.symbol

theorem uniqueSymbols_append {Symbol Measure : Type}
    {left right : Release Symbol Measure}
    (hL : uniqueSymbols left) (hR : uniqueSymbols right)
    (hd : symbolsDisjoint left right) : uniqueSymbols (left ++ right) := by
  intro p hp q hq hsym
  cases List.mem_append.mp hp with
  | inl hpl =>
    cases List.mem_append.mp hq with
    | inl hql => exact hL p hpl q hql hsym
    | inr hqr => exact absurd hsym (hd p hpl q hqr)
  | inr hpr =>
    cases List.mem_append.mp hq with
    | inl hql => exact absurd hsym.symm (hd q hql p hpr)
    | inr hqr => exact hR p hpr q hqr hsym

/-- Every incumbent symbol still has a `noWorse` profile in the
    candidate, and each release names each symbol at most once. A
    regressing duplicate of a symbol that also has a no-worse profile
    does not pass. Symbols the candidate adds, once each, are
    unconstrained. -/
def releaseLe {Symbol Measure : Type}
    (space : MeasureSpace Measure)
    (candidate incumbent : Release Symbol Measure) : Prop :=
  uniqueSymbols candidate ∧ uniqueSymbols incumbent ∧
    ∀ q ∈ incumbent, ∃ p ∈ candidate, noWorse space p q

/-- Pareto dominance of one assembly over another: `releaseLe`, and at
    least one incumbent symbol is strictly dominated. -/
def releaseDominates {Symbol Measure : Type}
    (space : MeasureSpace Measure)
    (candidate incumbent : Release Symbol Measure) : Prop :=
  releaseLe space candidate incumbent ∧
    ∃ q ∈ incumbent, ∃ p ∈ candidate, dominates space p q

theorem releaseLe_refl {Symbol Measure : Type}
    {space : MeasureSpace Measure} {R : Release Symbol Measure}
    (hU : uniqueSymbols R) (h : ∀ p ∈ R, aligned space p) :
    releaseLe space R R :=
  ⟨hU, hU, fun q hq => ⟨q, hq, noWorse_refl (h q hq)⟩⟩

theorem releaseLe_trans {Symbol Measure : Type}
    {space : MeasureSpace Measure}
    {c b a : Release Symbol Measure}
    (hcb : releaseLe space c b) (hba : releaseLe space b a) :
    releaseLe space c a := by
  refine ⟨hcb.1, hba.2.1, ?_⟩
  intro q hq
  obtain ⟨p, hp, hle⟩ := hba.2.2 q hq
  obtain ⟨p', hp', hle'⟩ := hcb.2.2 p hp
  exact ⟨p', hp', noWorse_trans hle' hle⟩

/-- Assemblies of disjoint symbols compose. If each component assembly
    is `releaseLe` its incumbent, the concatenated assembly is too. -/
theorem releaseLe_append {Symbol Measure : Type}
    {space : MeasureSpace Measure}
    {c1 i1 c2 i2 : Release Symbol Measure}
    (h1 : releaseLe space c1 i1) (h2 : releaseLe space c2 i2)
    (hc : symbolsDisjoint c1 c2) (hi : symbolsDisjoint i1 i2) :
    releaseLe space (c1 ++ c2) (i1 ++ i2) := by
  refine ⟨uniqueSymbols_append h1.1 h2.1 hc,
    uniqueSymbols_append h1.2.1 h2.2.1 hi, ?_⟩
  intro q hq
  cases List.mem_append.mp hq with
  | inl hl =>
    obtain ⟨p, hp, hle⟩ := h1.2.2 q hl
    exact ⟨p, List.mem_append_left _ hp, hle⟩
  | inr hr =>
    obtain ⟨p, hp, hle⟩ := h2.2.2 q hr
    exact ⟨p, List.mem_append_right _ hp, hle⟩

theorem releaseDominates_append_left {Symbol Measure : Type}
    {space : MeasureSpace Measure}
    {c1 i1 c2 i2 : Release Symbol Measure}
    (h1 : releaseDominates space c1 i1) (h2 : releaseLe space c2 i2)
    (hc : symbolsDisjoint c1 c2) (hi : symbolsDisjoint i1 i2) :
    releaseDominates space (c1 ++ c2) (i1 ++ i2) := by
  refine ⟨releaseLe_append h1.1 h2 hc hi, ?_⟩
  obtain ⟨q, hq, p, hp, hdom⟩ := h1.2
  exact ⟨q, List.mem_append_left _ hq, p, List.mem_append_left _ hp, hdom⟩

theorem releaseDominates_append_right {Symbol Measure : Type}
    {space : MeasureSpace Measure}
    {c1 i1 c2 i2 : Release Symbol Measure}
    (h1 : releaseLe space c1 i1) (h2 : releaseDominates space c2 i2)
    (hc : symbolsDisjoint c1 c2) (hi : symbolsDisjoint i1 i2) :
    releaseDominates space (c1 ++ c2) (i1 ++ i2) := by
  refine ⟨releaseLe_append h1 h2.1 hc hi, ?_⟩
  obtain ⟨q, hq, p, hp, hdom⟩ := h2.2
  exact ⟨q, List.mem_append_right _ hq, p, List.mem_append_right _ hp, hdom⟩

/-- Index order is not the profile preorder. Swapping two symbols'
    profiles keeps `releaseLe` and breaks a position-wise reading
    comparison of the first coordinates (`9` against `1`). -/
theorem not_index_aligned_preorder :
    let gate : Profile Bool Unit :=
      { symbol := false, readings := [1], observed := true }
    let commit : Profile Bool Unit :=
      { symbol := true, readings := [9], observed := true }
    let space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
    releaseLe space [commit, gate] [gate, commit] ∧ ¬ axisLe .minimize 9 1 := by
  let gate : Profile Bool Unit :=
    { symbol := false, readings := [1], observed := true }
  let commit : Profile Bool Unit :=
    { symbol := true, readings := [9], observed := true }
  let space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
  have uniqSwap : uniqueSymbols [commit, gate] := by
    intro p hp q hq hsym
    cases hp with
    | head =>
      cases hq with
      | head => rfl
      | tail _ hq =>
        cases hq with
        | head => cases hsym
        | tail _ hr => cases hr
    | tail _ hp =>
      cases hp with
      | head =>
        cases hq with
        | head => cases hsym
        | tail _ hq =>
          cases hq with
          | head => rfl
          | tail _ hr => cases hr
      | tail _ hr => cases hr
  have uniqInc : uniqueSymbols [gate, commit] := by
    intro p hp q hq hsym
    cases hp with
    | head =>
      cases hq with
      | head => rfl
      | tail _ hq =>
        cases hq with
        | head => cases hsym
        | tail _ hr => cases hr
    | tail _ hp =>
      cases hp with
      | head =>
        cases hq with
        | head => cases hsym
        | tail _ hq =>
          cases hq with
          | head => rfl
          | tail _ hr => cases hr
      | tail _ hr => cases hr
  refine ⟨⟨uniqSwap, uniqInc, ?_⟩, ?_⟩
  · intro q hq
    cases hq with
    | head _ =>
      exact ⟨gate, List.mem_cons_of_mem _ List.mem_cons_self, noWorse_refl rfl⟩
    | tail _ hmem =>
      cases hmem with
      | head _ =>
        exact ⟨commit, List.mem_cons_self, noWorse_refl rfl⟩
      | tail _ hrest => cases hrest
  · intro h
    simp [axisLe] at h

/-- A candidate that keeps one no-worse profile and also submits a
    regressing profile of the same symbol is not `releaseLe`. The
    no-worse profile would have satisfied the incumbent by itself. -/
theorem duplicate_candidate_not_releaseLe :
    let space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
    let good : Profile Bool Unit :=
      { symbol := true, readings := [0], observed := true }
    let regressing : Profile Bool Unit :=
      { symbol := true, readings := [9], observed := true }
    let incumbent : Profile Bool Unit :=
      { symbol := true, readings := [1], observed := true }
    (∃ p ∈ [good, regressing], noWorse space p incumbent) ∧
      ¬ releaseLe space [good, regressing] [incumbent] := by
  let space : MeasureSpace Unit := [{ measure := (), polarity := .minimize }]
  let good : Profile Bool Unit :=
    { symbol := true, readings := [0], observed := true }
  let regressing : Profile Bool Unit :=
    { symbol := true, readings := [9], observed := true }
  let incumbent : Profile Bool Unit :=
    { symbol := true, readings := [1], observed := true }
  refine ⟨⟨good, List.mem_cons_self, ⟨⟨rfl, ⟨Nat.zero_le _, trivial⟩⟩, fun _ => rfl⟩⟩, ?_⟩
  intro h
  have heq : good = regressing :=
    h.1 good List.mem_cons_self regressing
      (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  have hread : good.readings = regressing.readings := congrArg Profile.readings heq
  cases hread

/-- Aligned profiles from `candidates` that no member of `candidates`
    dominates. A profile whose readings do not cover the space is not
    on the frontier. Membership is exact (`frontier_exact`); the list
    is finite because it is a sublist of a finite list. -/
def frontier {Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure) (candidates : List (Profile Symbol Measure)) :
    List (Profile Symbol Measure) :=
  candidates.filter (fun p =>
    decide (aligned space p) &&
      !(candidates.any (fun q => decide (dominates space q p))))

theorem frontier_exact {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {L : List (Profile Symbol Measure)}
    {p : Profile Symbol Measure} :
    p ∈ frontier space L ↔
      p ∈ L ∧ aligned space p ∧ ∀ q ∈ L, ¬ dominates space q p := by
  constructor
  · intro h
    have hmem := List.mem_filter.mp h
    have hcond := hmem.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨hal, hnot⟩ := hcond
    refine ⟨hmem.1, of_decide_eq_true hal, ?_⟩
    intro q hq hdom
    have hany : L.any (fun r => decide (dominates space r p)) = true :=
      List.any_eq_true.mpr ⟨q, hq, decide_eq_true hdom⟩
    rw [hany] at hnot
    cases hnot
  · intro h
    apply List.mem_filter.mpr
    refine ⟨h.1, ?_⟩
    have hal : decide (aligned space p) = true := decide_eq_true h.2.1
    cases hb : L.any (fun q => decide (dominates space q p)) with
    | false =>
      rw [hal]
      rfl
    | true =>
      rcases List.any_eq_true.mp hb with ⟨q, hq, hd⟩
      exact absurd (of_decide_eq_true hd) (h.2.2 q hq)

theorem frontier_antichain {Symbol Measure : Type} [DecidableEq Symbol]
    {space : MeasureSpace Measure} {L : List (Profile Symbol Measure)}
    {p q : Profile Symbol Measure}
    (hp : p ∈ frontier space L) (hq : q ∈ frontier space L) :
    ¬ dominates space p q :=
  (frontier_exact.mp hq).2.2 p (frontier_exact.mp hp).1

/-- A profile whose readings do not cover the space is not undominated
    output. Nothing in the candidate list dominates it; alignment
    removes it. -/
theorem misaligned_not_on_frontier :
    ({ symbol := (), readings := [0, 0], observed := true } : Profile Unit Unit) ∉
      frontier [{ measure := (), polarity := .minimize }]
        [{ symbol := (), readings := [0, 0], observed := true }] := by
  intro h
  exact absurd (frontier_exact.mp h).2.1 (by decide)

#print axioms noWorse_refl
#print axioms noWorse_trans
#print axioms noWorse_antisymm
#print axioms not_dominates_self
#print axioms dominates_trans
#print axioms not_dominates_from_measures
#print axioms measuresLe_append_iff
#print axioms noWorse_append
#print axioms dominates_append_of_halves
#print axioms not_noWorse_append_converse
#print axioms releaseLe_trans
#print axioms releaseLe_append
#print axioms not_index_aligned_preorder
#print axioms duplicate_candidate_not_releaseLe
#print axioms not_axesLt_of_short_vector
#print axioms frontier_exact
#print axioms misaligned_not_on_frontier

end Interface
end SoftwareIsQuantifiable
