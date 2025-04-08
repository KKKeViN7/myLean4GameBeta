import Game.Metadata

World "TutorialWorld"
Level 10
Title "The nth_rw tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第七关！在这一关中，我们将学习如何使用 simp 和 simp_arith 策略，它们是简化表达式的强大工具。

simp 是 Lean 中一个强大的简化策略，它能够自动应用一系列简化规则，将表达式化简为更简单的形式。
"

Statement (h1 : a = c) (h2 : a = b) (h3 : a + b + c = 0) : a + a + a = 0 := by
  nth_rw 3 [h1]
  nth_rw 2 [h2]
  exact h3

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic nth_rw
--NewTheorem
-- NewDefinition Nat Add Eq
