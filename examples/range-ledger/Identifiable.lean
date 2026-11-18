import Std

namespace RangeLedger.Identifiable

abbrev World := Nat → Int
def total (p : World) (a b : Nat) := p b - p a
abbrev Catalog := Nat → Nat → Prop

inductive Path (g : Catalog) : Nat → Nat → Prop
  | stay (a) : Path g a a
  | edge {a b} : g a b → Path g a b
  | reverse {a b} : Path g a b → Path g b a
  | join {a b c} : Path g a b → Path g b c → Path g a c

def agrees (g : Catalog) (p q : World) :=
  ∀ a b, g a b → total p a b = total q a b

theorem path_determines {g : Catalog} {a b : Nat} (h : Path g a b)
    (p q : World) (same : agrees g p q) : total p a b = total q a b := by
  induction h with
  | stay => simp [total]
  | edge hg => exact same _ _ hg
  | reverse _ ih => unfold total at *; omega
  | join _ _ hl hr => unfold total at *; omega

-- Translate one connected component by one. Every observed difference survives.
theorem determined_iff (g : Catalog) (a b : Nat) :
    (∀ p q, agrees g p q → total p a b = total q a b) ↔ Path g a b := by
  classical
  constructor
  · intro unique
    apply Classical.byContradiction
    intro missing
    let shifted : World := fun x => if Path g a x then 0 else 1
    have same : agrees g (fun _ => 0) shifted := by
      intro u v huv
      have conn : Path g a u ↔ Path g a v :=
        ⟨fun h => h.join (.edge huv), fun h => h.join (.reverse (.edge huv))⟩
      simp [total,shifted,conn]
    have impossible := unique _ _ same
    simp [total,shifted,Path.stay,missing] at impossible
  · exact fun path p q => path_determines path p q

def observed (a b : Nat) := (a = 0 ∧ b = 100) ∨ (a = 55 ∧ b = 100)
theorem hidden_prefix : Path observed 0 55 :=
  (Path.edge (Or.inl ⟨rfl,rfl⟩)).join (.reverse (.edge (Or.inr ⟨rfl,rfl⟩)))

theorem open_cut : ¬ Path observed 0 56 := by
  intro h
  let spike : World := fun i => if i = 56 then 1 else 0
  have same : agrees observed (fun _ => 0) spike := by
    rintro _ _ (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> decide
  exact absurd (path_determines h _ _ same) (by decide)

theorem both_receipts_needed (keepLeft : Bool) :
    ¬ Path (fun a b => a = (if keepLeft then 0 else 55) ∧ b = 100) 0 55 := by
  intro path
  let unseen := if keepLeft then 55 else 0
  let spike : World := fun x => if x = unseen then 1 else 0
  have same : agrees (fun a b => a = (if keepLeft then 0 else 55) ∧ b = 100)
      (fun _ => 0) spike := by
    rintro _ _ ⟨rfl,rfl⟩; cases keepLeft <;> decide
  have bad := path_determines path _ _ same
  cases keepLeft <;> simp [total,spike,unseen] at bad

#print axioms both_receipts_needed
#print axioms determined_iff
#print axioms hidden_prefix
#print axioms open_cut
end RangeLedger.Identifiable
