/-
  Claim 2 — Fold correctness (spec §17.4, §17.8, §22.D).

  The witness accounting is a fold over content-addressed witnesses
  whose join is a semi-lattice operation. Hence the accounting is
  order- and duplication-independent and exactly recomputable from
  scratch: it is a function of the witness *set*, not of the list
  that presented it. Here the accounting state is the characteristic
  function of the recorded witness set; the join is pointwise union.
-/

namespace SoftwareIsQuantifiable

/-- If a decidable proposition does not hold, its `decide` is false. -/
theorem decide_false_of_not {p : Prop} [Decidable p] (h : ¬ p) :
    decide p = false := by
  cases hd : decide p with
  | true => exact absurd (of_decide_eq_true hd) h
  | false => rfl

namespace Fold

variable {W : Type} [DecidableEq W]

/-- An accounting state: for each witness identity, whether it is
    recorded. Content addressing means a witness is its identity —
    two records with one identity are one witness. -/
def Acct (W : Type) := W → Bool

/-- The join of two accounting states: union of the recorded sets. -/
def join (a b : Acct W) : Acct W := fun w => a w || b w

/-- The empty accounting: nothing recorded. -/
def empty : Acct W := fun _ => false

/-- The accounting of a single witness. -/
def single (w : W) : Acct W := fun x => decide (x = w)

/-- The accounting of a list of witnesses, folded from scratch. -/
def account : List W → Acct W
  | [] => empty
  | w :: ws => join (single w) (account ws)

omit [DecidableEq W] in
/-- The join is associative. -/
theorem join_assoc (a b c : Acct W) : join (join a b) c = join a (join b c) := by
  funext x
  show ((a x || b x) || c x) = (a x || (b x || c x))
  cases h1 : a x <;> cases h2 : b x <;> cases h3 : c x <;> rfl

omit [DecidableEq W] in
/-- The join is commutative. -/
theorem join_comm (a b : Acct W) : join a b = join b a := by
  funext x
  show (a x || b x) = (b x || a x)
  cases h1 : a x <;> cases h2 : b x <;> rfl

omit [DecidableEq W] in
/-- The join is idempotent. -/
theorem join_idem (a : Acct W) : join a a = a := by
  funext x
  show (a x || a x) = a x
  cases h1 : a x <;> rfl

omit [DecidableEq W] in
/-- The empty accounting is a left identity for the join. -/
theorem join_empty_left (a : Acct W) : join empty a = a := by
  funext x
  show (false || a x) = a x
  cases h1 : a x <;> rfl

omit [DecidableEq W] in
/-- The empty accounting is a right identity for the join. -/
theorem join_empty_right (a : Acct W) : join a empty = a := by
  funext x
  show (a x || false) = a x
  cases h1 : a x <;> rfl

/-- The fold splits over appends: a from-scratch recompute over a
    partitioned presentation agrees with the join of the parts. -/
theorem account_append (l₁ l₂ : List W) :
    account (l₁ ++ l₂) = join (account l₁) (account l₂) := by
  induction l₁ with
  | nil => simp [account, join_empty_left]
  | cons w ws IH =>
    show join (single w) (account (ws ++ l₂)) =
      join (join (single w) (account ws)) (account l₂)
    rw [IH, join_assoc]

/-- What the fold records is exactly the presented set: a witness is
    recorded by the fold if and only if it occurs in the list. -/
theorem account_eq_true_iff {ws : List W} {x : W} :
    account ws x = true ↔ x ∈ ws := by
  induction ws with
  | nil => simp [account, empty]
  | cons w ws IH =>
    constructor
    · intro h
      have h' : (decide (x = w) || account ws x) = true := h
      by_cases hx : x = w
      · subst hx
        exact List.Mem.head _
      · rw [decide_false_of_not hx] at h'
        have h2 : account ws x = true := by simpa using h'
        exact List.mem_cons_of_mem w (IH.mp h2)
    · intro h
      cases h with
      | head _ =>
        show (decide (x = x) || account ws x) = true
        cases hd : decide (x = x) with
        | true => rfl
        | false => exact (of_decide_eq_false hd rfl).elim
      | tail _ hmem =>
        have h2 : account ws x = true := IH.mpr hmem
        simp [account, join, single, h2]

/-- **Order- and duplication-independence.** Two presentations of the
    same witness set fold to the same accounting. The fold is a
    function of the set, not of the presentation. -/
theorem account_ext {l₁ l₂ : List W} (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    account l₁ = account l₂ := by
  funext x
  by_cases h1 : account l₁ x = true
  · have hmem : x ∈ l₂ := (h x).mp (account_eq_true_iff.mp h1)
    rw [h1, account_eq_true_iff.mpr hmem]
  · by_cases h2 : account l₂ x = true
    · have hmem : x ∈ l₁ := (h x).mpr (account_eq_true_iff.mp h2)
      exact absurd (account_eq_true_iff.mpr hmem) h1
    · have e1 : account l₁ x = false := by
        cases hb : account l₁ x with
        | true => exact absurd hb h1
        | false => rfl
      have e2 : account l₂ x = false := by
        cases hb : account l₂ x with
        | true => exact absurd hb h2
        | false => rfl
      rw [e1, e2]

/-- **Permutation-independence**: reordering the presentation changes
    nothing. -/
theorem account_perm {l₁ l₂ : List W} (h : List.Perm l₁ l₂) :
    account l₁ = account l₂ :=
  account_ext (fun _ => h.mem_iff)

/-- **Duplication-independence**: presenting every witness twice
    changes nothing; a repeated execution of the same step costs
    zero marginal accounting. -/
theorem account_append_self (l : List W) : account (l ++ l) = account l := by
  rw [account_append]
  funext x
  show (account l x || account l x) = account l x
  cases h1 : account l x <;> rfl

/-- Re-appending an already-recorded witness changes nothing. -/
theorem account_cons_self (w : W) (l : List W) (h : w ∈ l) :
    account (w :: l) = account l := by
  funext x
  by_cases hx : x = w
  · subst hx
    show (decide (x = x) || account l x) = account l x
    rw [account_eq_true_iff.mpr h]
    cases hb : decide (x = x) <;> rfl
  · show (decide (x = w) || account l x) = account l x
    rw [decide_false_of_not hx]
    cases hb : account l x <;> rfl

end Fold
end SoftwareIsQuantifiable
