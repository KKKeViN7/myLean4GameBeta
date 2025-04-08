import Game.Metadata

World "MatrixWorld"
Level 11
Title "The invertible matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement [Fintype n] [DecidableEq n]
  (A : Matrix n n ℝ) (h : det A ≠ 0) :
    IsUnit A := by
      rw [isUnit_iff_isUnit_det]
      rw [isUnit_iff_exists]
      use 1/(det A)
      apply And.intro
      simp
      rw [mul_inv_cancel]
      exact h
      simp
      rw [mul_comm]
      rw [mul_inv_cancel]
      exact h

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.isUnit_iff_isUnit_det isUnit_iff_exists mul_inv_cancel
NewDefinition IsUnit
