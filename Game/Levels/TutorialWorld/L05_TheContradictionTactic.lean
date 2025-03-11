import Game.Metadata

World "TutorialWorld"
Level 5
Title "The contradiction tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第五关！在这一关中，我们将学习如何使用 contradiction 策略，它不仅能证明矛盾命题，还能帮助我们像侦探一样在假设中搜索矛盾。
"

Statement (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  Hint"使用 contradiction 策略搜索当前假设中的矛盾"
  contradiction

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic contradiction
--NewTheorem
-- NewDefinition Nat Add Eq
