import Game.Metadata

World "TutorialWorld"
Level 6
Title "The linarith tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第六关！在这一关中，我们将学习如何使用 linarith 策略，这是解决线性算术问题的强大工具。
"

Statement : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  Hint"linarith 是 Lean 中一个强大的自动化策略，它能够自动解决包含线性算术表达式的证明目标。"
  linarith

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic linarith
--NewTheorem
-- NewDefinition Nat Add Eq
