import Game.Metadata

World "TutorialWorld"
Level 2
Title "The intro, exact and apply tactics"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到 Lean 线性代数之旅的第二关！在这一关中，我们将学习三个在逻辑推理中至关重要的证明策略：intro, exact 和 apply。
"

Statement (p q r: Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  Hint "在证明“p → r”形式的命题时，我们需要引入假设p作为前提。使用 intro hp 可以帮助我们做到这一点。"
  intro hp
  Hint "在证明过程中，我们经常需要应用已知的定理或假设。apply 策略可以将这些定理或假设“套用”到当前的目标上，尝试 apply hqr 并关注目标的变化。"
  apply hqr
  apply hpq
  Hint "当我们已经找到了与证明目标完全匹配的证据时，exact 策略可以直接完成证明，尝试 exact hp 。"
  exact hp

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic intro exact apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
