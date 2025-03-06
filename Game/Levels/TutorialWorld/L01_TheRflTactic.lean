import Game.Metadata

World "TutorialWorld"
Level 1
Title "The rfl tactic"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "欢迎来到你的 Lean 线性代数学习之旅！在这一关中，你将学习到几个最常用的 Lean 证明策略，它们就像是证明的基石，能够帮助你构建复杂的证明过程"

/-Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]-/
Statement : x = x := by
  rfl

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
