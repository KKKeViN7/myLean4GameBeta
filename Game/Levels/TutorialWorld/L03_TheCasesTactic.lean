import Game.Metadata

World "TutorialWorld"
Level 3
Title "The cases tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第三关！在这一关中，我们将学习如何使用 cases 策略进行情况分析，以及如何使用 And.intro 定理来构建合取命题的证明。
"

Statement (hpq : p ∧ q) : q ∧ p := by
  Hint"在数学证明中，我们经常需要根据不同的情况进行分析。尝试使用 cases hpq 拆解命题。"
  cases hpq
  Hint"合取命题需要证明所有组成部分都为真。And.intro 定理允许我们通过分别证明每个组成部分，来构建合取命题的证明。注意这是一个定理，需要以 apply And.intro 形式来使用。"
  apply And.intro
  exact right
  exact left

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic cases
NewTheorem And.intro
-- NewDefinition Nat Add Eq
