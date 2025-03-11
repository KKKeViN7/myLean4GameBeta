import Game.Metadata

World "TutorialWorld"
Level 4
Title "The cases tactic 2"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第四关！在这一关中，我们将深入学习如何使用 cases 策略进行情况分析，以及如何使用 Or.inl 和 Or.inr 定理来构建析取命题的证明。
"

Statement (hpq : p ∨ q) : q ∨ p := by
  cases hpq
  Hint "析取命题需要证明至少一个组成部分为真。Or.inl 和 Or.inr 定理允许我们通过分别证明左侧或右侧的组成部分，来构建析取命题的证明。"
  apply Or.inr
  exact h
  apply Or.inl
  exact h

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic
NewTheorem Or.inl Or.inr
-- NewDefinition Nat Add Eq
