import Game.Metadata

World "TutorialWorld"
Level 0
Title "The test tactics"

example (hpq : p ∧ q) : q ∧ p := by
  cases hpq
  exact And.intro right left

example (hpq : p ∨ q) : q ∨ p := by
  cases hpq
  exact Or.inr h
  exact Or.inl h

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  linarith

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_add Nat.mul_left_comm
attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_mul Nat.add_left_comm
example (x y z: Nat) (p : Nat → Prop) (h : p (1 * x + 2 * y + 0 * z)) : p (y + x + y) := by
  simp at h
  simp_arith
  exact h
