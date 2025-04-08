import Game.Metadata

World "MatrixWorld"
Level 5
Title "The transpose matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement [DecidableEq n] [Fintype n] [Zero α] [One α] [Sub α] [AddCommMonoid α] [CommSemigroup α]
  (X E: Matrix n n α) (he : E = 1):
    (E - X * Xᵀ)ᵀ = E - X * Xᵀ := by
      rw [he]
      rw [transpose_sub]
      rw [transpose_one]
      rw [transpose_mul]
      rw [transpose_transpose]

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic use
NewTheorem Matrix.transpose_sub Matrix.transpose_one Matrix.transpose_mul Matrix.transpose_transpose
--NewDefinition
