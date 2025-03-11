import Game.Metadata

World "TutorialWorld"
Level 7
Title "The simp tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第七关！在这一关中，我们将学习如何使用 simp 和 simp_arith 策略，它们是简化表达式的强大工具。

simp 是 Lean 中一个强大的简化策略，它能够自动应用一系列简化规则，将表达式化简为更简单的形式。
"

Statement (x y z: Nat) (p : Nat → Prop) (h : p (1 * x + 2 * y + 0 * z)) : p (x + y + y) := by
  Hint "simp at h 允许你在证明目标的特定位置应用简化规则。"
  simp at h
  Hint "simp_arith 是 simp 的一个变体，专门用于简化算术表达式。"
  simp_arith
  exact h

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic simp simp_arith
--NewTheorem
-- NewDefinition Nat Add Eq
