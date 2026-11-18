/-
  Claim 3 — Coloring (spec §5 saturation discipline, §16.8, §20).

  Relative to a named snapshot — a finite universe `U` of facts, a
  finite rule set of ground Horn rules, and a seed — the qualification
  coloring is the least fixed point of the closure step. Below: the
  iteration reaches a fixed point within `U.length + 1` steps
  (termination), and the fixed point contains exactly the derivable
  facts (soundness and completeness). The one side condition is
  stated, not hidden: the universe must name every conclusion the
  rules can produce — that is what makes the snapshot a snapshot.
-/

namespace SoftwareIsQuantifiable
namespace Coloring

variable {F : Type} [DecidableEq F]

/-- A ground Horn rule over facts: from all of its premises, conclude
    its conclusion. -/
structure Rule (F : Type) where
  /-- The rule's premises. -/
  premises : List F
  /-- The rule's conclusion. -/
  conclusion : F

/-- A coloring state: which facts currently hold. -/
abbrev State (F : Type) := F → Bool

/-- Whether every premise in the list holds in the state. -/
def holds (s : State F) (l : List F) : Bool := l.all (fun f => s f)

/-- Splitting a true conjunction of booleans. -/
theorem and_eq_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => simp at h
  | true =>
    cases b with
    | false => simp at h
    | true => exact ⟨rfl, rfl⟩

theorem holds_eq_true {s : State F} {l : List F} :
    holds s l = true ↔ ∀ p ∈ l, s p = true := by
  induction l with
  | nil =>
    constructor
    · intro _ p hp
      cases hp
    · intro _
      rfl
  | cons a l IH =>
    constructor
    · intro h
      have h' : (s a && holds s l) = true := h
      have ha : s a = true := (and_eq_true h').1
      have hl : holds s l = true := (and_eq_true h').2
      intro p hp
      cases hp with
      | head _ => exact ha
      | tail _ hpm => exact IH.mp hl p hpm
    · intro h
      have ha : s a = true := h a (List.mem_cons_self _ _)
      have hl : holds s l = true :=
        IH.mpr (fun p hp => h p (List.mem_cons_of_mem _ hp))
      show (s a && holds s l) = true
      rw [ha, hl]
      rfl

/-- A list's `any`, characterized. -/
theorem any_eq_true {β : Type} {l : List β} {p : β → Bool} :
    l.any p = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil =>
    constructor
    · intro h
      exact Bool.noConfusion h
    · intro h
      obtain ⟨x, hx, -⟩ := h
      cases hx
  | cons a l IH =>
    constructor
    · intro h
      have h' : (p a || l.any p) = true := h
      cases hb : p a with
      | true => exact ⟨a, List.mem_cons_self _ _, hb⟩
      | false =>
        have h2 : l.any p = true := by simpa [hb] using h'
        cases IH.mp h2 with
        | intro x hx => exact ⟨x, List.mem_cons_of_mem _ hx.1, hx.2⟩
    · intro h
      cases h with
      | intro x hx =>
        cases hx.1 with
        | head _ => simp [hx.2]
        | tail _ hmem =>
          have h2 : l.any p = true := IH.mpr ⟨x, hmem, hx.2⟩
          simp [h2]

/-- One closure step: keep everything that holds, and add every
    conclusion whose premises all hold. -/
def step (rules : List (Rule F)) (s : State F) : State F :=
  fun f => s f || rules.any (fun r => decide (r.conclusion = f) && holds s r.premises)

/-- The closure step only adds facts. -/
theorem le_step (rules : List (Rule F)) (s : State F) (f : F) :
    s f = true → step rules s f = true := by
  intro h
  show (s f || rules.any
    (fun r => decide (r.conclusion = f) && holds s r.premises)) = true
  rw [h]
  rfl

/-- Iterate the closure step: `iter rules n s` is the `n`-fold
    application of `step` to `s`. -/
def iter (rules : List (Rule F)) : Nat → State F → State F
  | 0, s => s
  | n + 1, s => step rules (iter rules n s)

/-- Once a state is a fixed point, iteration stays there. -/
theorem iter_eq_of_fixed {rules : List (Rule F)} {s : State F}
    (h : step rules s = s) : ∀ m, iter rules m s = s := by
  intro m
  induction m with
  | zero => rfl
  | succ m IH =>
    show step rules (iter rules m s) = s
    rw [IH]
    exact h

/-- Facts are never lost along the iteration. -/
theorem le_iter (rules : List (Rule F)) :
    ∀ (n : Nat) (s : State F) (f : F),
      s f = true → iter rules n s f = true := by
  intro n
  induction n with
  | zero => intro s f hf; exact hf
  | succ n IH =>
    intro s f hf
    show step rules (iter rules n s) f = true
    exact le_step rules _ f (IH s f hf)

/-- The contribution of one universe element to the count. -/
def contrib (b : Bool) : Nat := match b with | true => 1 | false => 0

/-- The size of a state, counted over the universe list. -/
def count : List F → State F → Nat
  | [], _ => 0
  | a :: U, s => contrib (s a) + count U s

/-- The count never exceeds the universe. -/
theorem count_le (U : List F) (s : State F) : count U s ≤ U.length := by
  induction U with
  | nil => exact Nat.le_refl 0
  | cons a U IH =>
    show contrib (s a) + count U s ≤ U.length + 1
    cases hb : s a with
    | true => show 1 + count U s ≤ U.length + 1; omega
    | false => show 0 + count U s ≤ U.length + 1; omega

/-- Counting is monotone in the state. -/
theorem count_le_of_le : ∀ (U : List F) {p q : State F},
    (∀ x ∈ U, p x = true → q x = true) → count U p ≤ count U q := by
  intro U
  induction U with
  | nil => intro _ _ _; exact Nat.le_refl 0
  | cons a U IH =>
    intro p q hle
    have htail : count U p ≤ count U q :=
      IH (fun x hx => hle x (List.mem_cons_of_mem _ hx))
    show contrib (p a) + count U p ≤ contrib (q a) + count U q
    by_cases hpa : p a = true
    · have hqa : q a = true := hle a (List.mem_cons_self _ _) hpa
      rw [hpa, hqa]
      show 1 + count U p ≤ 1 + count U q
      omega
    · have hpaf : p a = false := by
        cases hb : p a with
        | true => exact absurd hb hpa
        | false => rfl
      rw [hpaf]
      show 0 + count U p ≤ contrib (q a) + count U q
      omega

/-- Counting strictly grows when a state grows somewhere in the
    universe. -/
theorem count_lt_of_le_add : ∀ (U : List F) {p q : State F},
    (∀ x ∈ U, p x = true → q x = true) →
    (∃ y ∈ U, q y = true ∧ p y = false) → count U p < count U q := by
  intro U
  induction U with
  | nil =>
    intro p q _ hex
    cases hex with
    | intro y hy => exact absurd hy.1 (List.not_mem_nil y)
  | cons a U IH =>
    intro p q hle hex
    have hle' : ∀ x ∈ U, p x = true → q x = true :=
      fun x hx => hle x (List.mem_cons_of_mem _ hx)
    show contrib (p a) + count U p < contrib (q a) + count U q
    by_cases haw : q a = true ∧ p a = false
    · have htail : count U p ≤ count U q := count_le_of_le U hle'
      rw [haw.1, haw.2]
      show 0 + count U p < 1 + count U q
      omega
    · have hex' : ∃ y ∈ U, q y = true ∧ p y = false := by
        cases hex with
        | intro y hy =>
          cases hy.1 with
          | head _ => exact absurd hy.2 haw
          | tail _ hym => exact ⟨y, hym, hy.2⟩
      have hlt : count U p < count U q := IH hle' hex'
      by_cases hpa : p a = true
      · have hqa : q a = true := hle a (List.mem_cons_self _ _) hpa
        rw [hpa, hqa]
        show 1 + count U p < 1 + count U q
        omega
      · have hpaf : p a = false := by
          cases hb : p a with
          | true => exact absurd hb hpa
          | false => rfl
        have hqaf : q a = false := by
          cases hb : q a with
          | true => exact absurd ⟨hb, hpaf⟩ haw
          | false => rfl
        rw [hpaf, hqaf]
        show 0 + count U p < 0 + count U q
        omega

/-- If a step changes a state, it adds a fact of the universe —
    provided the universe names every conclusion, which is the
    snapshot condition. -/
theorem exists_added (rules : List (Rule F)) (U : List F) (s : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U)
    (hstep : step rules s ≠ s) :
    ∃ y ∈ U, step rules s y = true ∧ s y = false := by
  refine Classical.byContradiction (fun hno => ?_)
  apply hstep
  funext y
  cases hy : s y with
  | true => exact le_step rules s y hy
  | false =>
    by_cases hsy : step rules s y = true
    · exfalso
      apply hno
      have h' : (s y || rules.any
          (fun r => decide (r.conclusion = y) && holds s r.premises)) = true := hsy
      rw [hy] at h'
      have hany : rules.any
          (fun r => decide (r.conclusion = y) && holds s r.premises) = true := by
        simpa using h'
      cases any_eq_true.mp hany with
      | intro r hr =>
        have hrc : r.conclusion = y :=
          of_decide_eq_true (and_eq_true hr.2).1
        exact ⟨y, hrc ▸ hU r hr.1, hsy, hy⟩
    · have e1 : step rules s y = false := by
        cases hb : step rules s y with
        | true => exact absurd hb hsy
        | false => rfl
      rw [e1]

/-- Along a chain with no fixed point, the count grows by at least
    one per step. -/
theorem count_iter_ge (rules : List (Rule F)) (U : List F) (seed : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    ∀ k, (∀ i < k, step rules (iter rules i seed) ≠ iter rules i seed) →
      count U seed + k ≤ count U (iter rules k seed) := by
  intro k
  induction k with
  | zero => intro _; exact Nat.le_refl _
  | succ k IH =>
    intro hne
    have IH' := IH (fun i hi => hne i (Nat.lt_succ_of_lt hi))
    have hstep := hne k (Nat.lt_succ_self k)
    have hex := exists_added rules U (iter rules k seed) hU hstep
    have hlt : count U (iter rules k seed)
        < count U (step rules (iter rules k seed)) :=
      count_lt_of_le_add U (fun x _ => le_step rules _ x) hex
    show count U seed + (k + 1) ≤ count U (step rules (iter rules k seed))
    omega

/-- **Termination.** The closure iteration reaches a fixed point,
    at some step no later than the size of the universe. -/
theorem exists_fixed_point (rules : List (Rule F)) (U : List F) (seed : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    ∃ k, k ≤ U.length ∧
      step rules (iter rules k seed) = iter rules k seed := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hne : ∀ i, i ≤ U.length →
      step rules (iter rules i seed) ≠ iter rules i seed := by
    intro i hi hEq
    exact hcon ⟨i, hi, hEq⟩
  have hchain := count_iter_ge rules U seed hU (U.length + 1)
    (fun i hi => hne i (Nat.le_of_lt_succ hi))
  have hbound := count_le U (iter rules (U.length + 1) seed)
  omega

/-- The coloring of a snapshot: iterate the closure step past the
    termination bound. -/
def coloring (rules : List (Rule F)) (U : List F) (seed : State F) : State F :=
  iter rules (U.length + 1) seed

/-- The coloring is a fixed point of the closure step. -/
theorem coloring_fixed (rules : List (Rule F)) (U : List F) (seed : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    step rules (coloring rules U seed) = coloring rules U seed := by
  cases exists_fixed_point rules U seed hU with
  | intro k hk =>
    have hk1 : k ≤ U.length := hk.1
    have hconst : ∀ m, iter rules (k + m) seed = iter rules k seed := by
      intro m
      induction m with
      | zero => simp
      | succ m IH =>
        have hsplit : k + (m + 1) = (k + m) + 1 := by omega
        rw [hsplit]
        show step rules (iter rules (k + m) seed) = iter rules k seed
        rw [IH]
        exact hk.2
    have hsplit : U.length + 1 = k + (U.length + 1 - k) := by omega
    show step rules (iter rules (U.length + 1) seed)
      = iter rules (U.length + 1) seed
    rw [hsplit, hconst]
    exact hk.2

/-- Derivability from a seed under the snapshot's ground Horn rules:
    the consequence relation the coloring computes. -/
inductive Deriv (rules : List (Rule F)) (seed : State F) : F → Prop where
  | seed {f : F} (h : seed f = true) : Deriv rules seed f
  | apply {r : Rule F} (hr : r ∈ rules)
      (hp : ∀ p ∈ r.premises, Deriv rules seed p) :
      Deriv rules seed r.conclusion

/-- One closure step preserves derivability. -/
theorem step_sound (rules : List (Rule F)) (seed s : State F)
    (hs : ∀ f, s f = true → Deriv rules seed f) :
    ∀ f, step rules s f = true → Deriv rules seed f := by
  intro f hf
  have h' : (s f || rules.any
      (fun r => decide (r.conclusion = f) && holds s r.premises)) = true := hf
  cases hb : s f with
  | true => exact hs f hb
  | false =>
    have hany : rules.any
        (fun r => decide (r.conclusion = f) && holds s r.premises) = true := by
      simpa [hb] using h'
    cases any_eq_true.mp hany with
    | intro r hr =>
      have hrc : r.conclusion = f :=
        of_decide_eq_true (and_eq_true hr.2).1
      have hholds : holds s r.premises = true := (and_eq_true hr.2).2
      have hderiv : Deriv rules seed r.conclusion :=
        Deriv.apply hr.1 (fun p hp => hs p (holds_eq_true.mp hholds p hp))
      subst hrc
      exact hderiv

/-- Every fact the iteration reaches is derivable. -/
theorem iter_sound (rules : List (Rule F)) (seed : State F) :
    ∀ (k : Nat) (s : State F), (∀ f, s f = true → Deriv rules seed f) →
      ∀ f, iter rules k s f = true → Deriv rules seed f := by
  intro k
  induction k with
  | zero => intro s hs f hf; exact hs f hf
  | succ k IH =>
    intro s hs f hf
    exact step_sound rules seed (iter rules k s) (IH s hs) f hf

/-- Every derivable fact holds in every state that contains the seed
    and is a fixed point of the closure step. -/
theorem deriv_closed (rules : List (Rule F)) (seed : State F) :
    ∀ {f : F}, Deriv rules seed f → ∀ s : State F,
      (∀ g, seed g = true → s g = true) → step rules s = s → s f = true := by
  intro f hf
  induction hf with
  | seed h =>
    intro s hs _
    exact hs _ h
  | apply hr hp IH =>
    rename_i r
    intro s hs hfix
    have hfire : step rules s r.conclusion = true := by
      have hprems : holds s r.premises = true :=
        holds_eq_true.mpr (fun p hpm => IH p hpm s hs hfix)
      have hany : rules.any
          (fun r' => decide (r'.conclusion = r.conclusion)
            && holds s r'.premises) = true :=
        any_eq_true.mpr ⟨r, hr, by simp [hprems]⟩
      show (s r.conclusion || rules.any
        (fun r' => decide (r'.conclusion = r.conclusion)
          && holds s r'.premises)) = true
      simp [hany]
    have e := congrFun hfix r.conclusion
    rw [hfire] at e
    exact e.symm

/-- **Soundness of the coloring**: every fact it colors is derivable
    from the seed under the snapshot's rules. -/
theorem coloring_sound (rules : List (Rule F)) (U : List F) (seed : State F) :
    ∀ f, coloring rules U seed f = true → Deriv rules seed f :=
  fun f hf => iter_sound rules seed (U.length + 1) seed
    (fun g hg => Deriv.seed hg) f hf

/-- **Completeness of the coloring**: every derivable fact is
    colored. Together with soundness, the coloring is exactly the
    derivable set — the least fixed point. -/
theorem coloring_complete (rules : List (Rule F)) (U : List F) (seed : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    ∀ f, Deriv rules seed f → coloring rules U seed f = true :=
  fun f hf => deriv_closed rules seed hf (coloring rules U seed)
    (fun g hg => le_iter rules (U.length + 1) seed g hg)
    (coloring_fixed rules U seed hU)

/-- The seed is contained in the coloring. -/
theorem seed_le_coloring (rules : List (Rule F)) (U : List F) (seed : State F) :
    ∀ f, seed f = true → coloring rules U seed f = true :=
  fun f hf => le_iter rules (U.length + 1) seed f hf

/-- Pointwise inclusion of coloring states. -/
def stateLe (a b : State F) : Prop := ∀ f, a f = true → b f = true

theorem stateLe_refl (a : State F) : stateLe a a := fun _ h => h

theorem stateLe_trans {a b c : State F} (hab : stateLe a b) (hbc : stateLe b c) :
    stateLe a c := fun f hf => hbc f (hab f hf)

theorem stateLe_antisymm {a b : State F} (hab : stateLe a b) (hba : stateLe b a) :
    a = b := by
  funext f
  cases ha : a f <;> cases hb : b f
  · rfl
  · exact absurd (hba f hb) (by rw [ha]; exact Bool.noConfusion)
  · exact absurd (hab f ha) (by rw [hb]; exact Bool.noConfusion)
  · rfl

/-- The closure step is monotone in the state. -/
theorem step_mono (rules : List (Rule F)) {s t : State F} (hle : stateLe s t) :
    stateLe (step rules s) (step rules t) := by
  intro f hf
  have h' : (s f || rules.any
      (fun r => decide (r.conclusion = f) && holds s r.premises)) = true := hf
  cases hs : s f with
  | true =>
    have ht : t f = true := hle f hs
    show (t f || rules.any
      (fun r => decide (r.conclusion = f) && holds t r.premises)) = true
    rw [ht]
    rfl
  | false =>
    have hany : rules.any
        (fun r => decide (r.conclusion = f) && holds s r.premises) = true := by
      simpa [hs] using h'
    rcases any_eq_true.mp hany with ⟨r, hr, hfire⟩
    have hdec : decide (r.conclusion = f) = true := (and_eq_true hfire).1
    have hholds : holds s r.premises = true := (and_eq_true hfire).2
    have hholds' : holds t r.premises = true :=
      holds_eq_true.mpr (fun p hp => hle p (holds_eq_true.mp hholds p hp))
    have hany' : rules.any
        (fun r' => decide (r'.conclusion = f) && holds t r'.premises) = true :=
      any_eq_true.mpr ⟨r, hr, by rw [hdec, hholds']; rfl⟩
    show (t f || rules.any
      (fun r' => decide (r'.conclusion = f) && holds t r'.premises)) = true
    simp [hany']

theorem iter_mono (rules : List (Rule F)) :
    ∀ (k : Nat) {s t : State F}, stateLe s t →
      stateLe (iter rules k s) (iter rules k t) := by
  intro k
  induction k with
  | zero =>
    intro s t hle
    exact hle
  | succ k IH =>
    intro s t hle
    exact step_mono rules (IH hle)

/-- **Monotonicity in the seed.** A larger seed only adds colored facts.
    The snapshot bound is not required for this direction. -/
theorem coloring_mono_seed (rules : List (Rule F)) (U : List F) {s t : State F}
    (hle : stateLe s t) : stateLe (coloring rules U s) (coloring rules U t) :=
  iter_mono rules (U.length + 1) hle

/-- **Idempotence.** Re-closing a coloring changes nothing. The snapshot
    condition is the same one `coloring_fixed` uses. -/
theorem coloring_idem (rules : List (Rule F)) (U : List F) (seed : State F)
    (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    coloring rules U (coloring rules U seed) = coloring rules U seed := by
  have hfix := coloring_fixed rules U seed hU
  unfold coloring
  exact iter_eq_of_fixed hfix (U.length + 1)

def joinSt (a b : State F) : State F := fun f => a f || b f

theorem stateLe_join_left (a b : State F) : stateLe a (joinSt a b) := by
  intro f hf
  show (a f || b f) = true
  rw [hf]
  rfl

theorem stateLe_join_right (a b : State F) : stateLe b (joinSt a b) := by
  intro f hf
  show (a f || b f) = true
  rw [hf]
  cases a f <;> rfl

theorem stateLe_join {a b c : State F} (ha : stateLe a c) (hb : stateLe b c) :
    stateLe (joinSt a b) c := by
  intro f hf
  have h' : (a f || b f) = true := hf
  cases ha' : a f with
  | true => exact ha f ha'
  | false =>
    have hb' : b f = true := by simpa [ha'] using h'
    exact hb f hb'

/-- **Compounding.** Closing the join of two seeds equals closing the
    join of their colorings:
    `C(s₁ ∨ s₂) = C(C(s₁) ∨ C(s₂))`.
    Cross-source consequences are kept, because the right-hand side
    closes again. This is not distribution over join; that stronger
    claim is false (`not_coloring_distributes`). -/
theorem coloring_compound (rules : List (Rule F)) (U : List F)
    (s1 s2 : State F) (hU : ∀ r ∈ rules, r.conclusion ∈ U) :
    coloring rules U (joinSt s1 s2) =
      coloring rules U (joinSt (coloring rules U s1) (coloring rules U s2)) := by
  let c1 := coloring rules U s1
  let c2 := coloring rules U s2
  let j := joinSt s1 s2
  let cj := coloring rules U j
  let mid := joinSt c1 c2
  have hc1 : stateLe c1 cj :=
    coloring_mono_seed rules U (stateLe_join_left s1 s2)
  have hc2 : stateLe c2 cj :=
    coloring_mono_seed rules U (stateLe_join_right s1 s2)
  have hto : stateLe (coloring rules U mid) cj := by
    have hmid : stateLe mid cj := stateLe_join hc1 hc2
    have hstep := coloring_mono_seed rules U hmid
    simpa [cj, coloring_idem rules U j hU] using hstep
  have hback : stateLe cj (coloring rules U mid) := by
    have hs1 : stateLe s1 c1 := fun f hf => seed_le_coloring rules U s1 f hf
    have hs2 : stateLe s2 c2 := fun f hf => seed_le_coloring rules U s2 f hf
    exact coloring_mono_seed rules U
      (stateLe_join (stateLe_trans hs1 (stateLe_join_left c1 c2))
        (stateLe_trans hs2 (stateLe_join_right c1 c2)))
  exact stateLe_antisymm hback hto

/-- A rule embedded into the left of a sum of fact domains. -/
def embedRuleLeft {F1 F2 : Type _} (r : Rule F1) : Rule (F1 ⊕ F2) where
  premises := r.premises.map Sum.inl
  conclusion := Sum.inl r.conclusion

/-- A rule embedded into the right of a sum of fact domains. -/
def embedRuleRight {F1 F2 : Type _} (r : Rule F2) : Rule (F1 ⊕ F2) where
  premises := r.premises.map Sum.inr
  conclusion := Sum.inr r.conclusion

/-- Independent seeds, one per domain. -/
def embedSeed {F1 F2 : Type _} (s1 : State F1) (s2 : State F2) : State (F1 ⊕ F2)
  | .inl x => s1 x
  | .inr x => s2 x

def embedUniverse {F1 F2 : Type _} (U1 : List F1) (U2 : List F2) : List (F1 ⊕ F2) :=
  U1.map Sum.inl ++ U2.map Sum.inr

theorem deriv_embed_left {F1 F2 : Type _} {rules1 : List (Rule F1)}
    {seed1 : State F1} {seed2 : State F2} {rules2 : List (Rule F2)} :
    ∀ {f : F1}, Deriv rules1 seed1 f →
      Deriv (rules1.map embedRuleLeft ++ rules2.map embedRuleRight)
        (embedSeed seed1 seed2) (Sum.inl f) := by
  intro f h
  induction h with
  | seed hs =>
    exact Deriv.seed (by simpa [embedSeed] using hs)
  | apply hr hp IH =>
    rename_i r
    refine Deriv.apply (r := embedRuleLeft r) ?_ ?_
    · exact List.mem_append_left _
        (List.mem_map_of_mem embedRuleLeft hr)
    · intro p hpm
      rcases List.mem_map.mp hpm with ⟨p1, hp1, rfl⟩
      exact IH p1 hp1

theorem deriv_embed_right {F1 F2 : Type _} {rules1 : List (Rule F1)}
    {seed1 : State F1} {seed2 : State F2} {rules2 : List (Rule F2)} :
    ∀ {f : F2}, Deriv rules2 seed2 f →
      Deriv (rules1.map embedRuleLeft ++ rules2.map embedRuleRight)
        (embedSeed seed1 seed2) (Sum.inr f) := by
  intro f h
  induction h with
  | seed hs =>
    exact Deriv.seed (by simpa [embedSeed] using hs)
  | apply hr hp IH =>
    rename_i r
    refine Deriv.apply (r := embedRuleRight r) ?_ ?_
    · exact List.mem_append_right _
        (List.mem_map_of_mem embedRuleRight hr)
    · intro p hpm
      rcases List.mem_map.mp hpm with ⟨p1, hp1, rfl⟩
      exact IH p1 hp1

/-- On segregated rule sets, a derivable sum-fact projects to a
    derivation in its own component. No rule crosses the sum. -/
theorem deriv_segregated {F1 F2 : Type _}
    {rules1 : List (Rule F1)} {rules2 : List (Rule F2)}
    {seed1 : State F1} {seed2 : State F2} {g : F1 ⊕ F2}
    (h : Deriv (rules1.map embedRuleLeft ++ rules2.map embedRuleRight)
      (embedSeed seed1 seed2) g) :
    (∀ f, g = Sum.inl f → Deriv rules1 seed1 f) ∧
    (∀ f, g = Sum.inr f → Deriv rules2 seed2 f) := by
  induction h with
  | seed hs =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · subst hf
      exact Deriv.seed (by simpa [embedSeed] using hs)
    · subst hf
      exact Deriv.seed (by simpa [embedSeed] using hs)
  | apply hr hp IH =>
    rename_i r
    cases List.mem_append.mp hr with
    | inl hL =>
      rcases List.mem_map.mp hL with ⟨r1, hr1, rfl⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · cases hf
        apply Deriv.apply hr1
        intro p hpm
        have hmem : (Sum.inl p : F1 ⊕ F2) ∈ (embedRuleLeft r1).premises :=
          List.mem_map_of_mem (Sum.inl : F1 → F1 ⊕ F2) hpm
        exact (IH (Sum.inl p) hmem).1 p rfl
      · cases hf
    | inr hR =>
      rcases List.mem_map.mp hR with ⟨r2, hr2, rfl⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · cases hf
      · cases hf
        apply Deriv.apply hr2
        intro p hpm
        have hmem : (Sum.inr p : F1 ⊕ F2) ∈ (embedRuleRight r2).premises :=
          List.mem_map_of_mem (Sum.inr : F2 → F1 ⊕ F2) hpm
        exact (IH (Sum.inr p) hmem).2 p rfl

theorem embed_universe_closed {F1 F2 : Type _}
    {rules1 : List (Rule F1)} {rules2 : List (Rule F2)}
    {U1 : List F1} {U2 : List F2}
    (h1 : ∀ r ∈ rules1, r.conclusion ∈ U1)
    (h2 : ∀ r ∈ rules2, r.conclusion ∈ U2) :
    ∀ r ∈ rules1.map embedRuleLeft ++ rules2.map embedRuleRight,
      r.conclusion ∈ embedUniverse U1 U2 := by
  intro r hr
  cases List.mem_append.mp hr with
  | inl hL =>
    rcases List.mem_map.mp hL with ⟨r1, hr1, rfl⟩
    unfold embedUniverse
    exact List.mem_append_left _ (List.mem_map_of_mem Sum.inl (h1 r1 hr1))
  | inr hR =>
    rcases List.mem_map.mp hR with ⟨r2, hr2, rfl⟩
    unfold embedUniverse
    exact List.mem_append_right _ (List.mem_map_of_mem Sum.inr (h2 r2 hr2))

/-- **Segregated domains factor.** When every rule lies entirely on one
    side of a sum of fact domains, the coloring of the sum at a left
    fact is the left component's coloring. Independent components
    compose by embedding; a cross-domain rule is a different theorem,
    and distribution over join is false. -/
theorem coloring_segregated_left {F1 F2 : Type _} [DecidableEq F1] [DecidableEq F2]
    (rules1 : List (Rule F1)) (rules2 : List (Rule F2))
    (U1 : List F1) (U2 : List F2) (seed1 : State F1) (seed2 : State F2)
    (hU1 : ∀ r ∈ rules1, r.conclusion ∈ U1)
    (hU2 : ∀ r ∈ rules2, r.conclusion ∈ U2) (f : F1) :
    coloring (rules1.map embedRuleLeft ++ rules2.map embedRuleRight)
        (embedUniverse U1 U2) (embedSeed seed1 seed2) (Sum.inl f) =
      coloring rules1 U1 seed1 f := by
  let rules := rules1.map embedRuleLeft ++ rules2.map embedRuleRight
  let U := embedUniverse U1 U2
  let seed := embedSeed seed1 seed2
  have hU := embed_universe_closed hU1 hU2
  cases hb : coloring rules U seed (Sum.inl f) <;>
    cases hb2 : coloring rules1 U1 seed1 f
  · rfl
  · have d1 := coloring_sound rules1 U1 seed1 f hb2
    have d := deriv_embed_left (rules2 := rules2) (seed2 := seed2) d1
    have ht := coloring_complete rules U seed hU (Sum.inl f) d
    rw [hb] at ht
    cases ht
  · have d := coloring_sound rules U seed (Sum.inl f) hb
    have d1 := (deriv_segregated d).1 f rfl
    have ht := coloring_complete rules1 U1 seed1 hU1 f d1
    rw [hb2] at ht
    cases ht
  · rfl

theorem coloring_segregated_right {F1 F2 : Type _} [DecidableEq F1] [DecidableEq F2]
    (rules1 : List (Rule F1)) (rules2 : List (Rule F2))
    (U1 : List F1) (U2 : List F2) (seed1 : State F1) (seed2 : State F2)
    (hU1 : ∀ r ∈ rules1, r.conclusion ∈ U1)
    (hU2 : ∀ r ∈ rules2, r.conclusion ∈ U2) (f : F2) :
    coloring (rules1.map embedRuleLeft ++ rules2.map embedRuleRight)
        (embedUniverse U1 U2) (embedSeed seed1 seed2) (Sum.inr f) =
      coloring rules2 U2 seed2 f := by
  let rules := rules1.map embedRuleLeft ++ rules2.map embedRuleRight
  let U := embedUniverse U1 U2
  let seed := embedSeed seed1 seed2
  have hU := embed_universe_closed hU1 hU2
  cases hb : coloring rules U seed (Sum.inr f) <;>
    cases hb2 : coloring rules2 U2 seed2 f
  · rfl
  · have d2 := coloring_sound rules2 U2 seed2 f hb2
    have d := deriv_embed_right (rules1 := rules1) (seed1 := seed1) d2
    have ht := coloring_complete rules U seed hU (Sum.inr f) d
    rw [hb] at ht
    cases ht
  · have d := coloring_sound rules U seed (Sum.inr f) hb
    have d2 := (deriv_segregated d).2 f rfl
    have ht := coloring_complete rules2 U2 seed2 hU2 f d2
    rw [hb2] at ht
    cases ht
  · rfl

end Coloring
end SoftwareIsQuantifiable
