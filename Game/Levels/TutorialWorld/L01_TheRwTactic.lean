import Game.Metadata

World "TutorialWorld"
Level 1
Title "The rfl and rw tactics"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"

Statement (h : y = x + 7) (h' : 2 * x + 14 = z): 2 * y = z := by
  Hint "使用 rw [h] 可以将假设 h 代表的等式代入到证明目标中。"
  rw [h]
  Hint "使用 rw [←h'] 可以将假设 h' 代表的等式反向代入（从右向左）到证明目标中。"
  rw [←h']
  Hint "rfl 是 reflexivity（反身性）的缩写，它将尝试使用反身性来完成当前的目标。"
  rfl

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
