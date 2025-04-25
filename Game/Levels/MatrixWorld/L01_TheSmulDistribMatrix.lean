import Game.Metadata

World "MatrixWorld"
Level 1
Title "The smul distrib matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement [Fintype m] [DecidableEq m] [CommSemiring α]
  (a : α) (M : Matrix m m α) (N : Matrix m m α) :
    a • (M * N) = M * (a • N) := by
      rw [Matrix.smul_eq_mul_diagonal (M * N) a]
      rw [Matrix.mul_assoc]
      rw [Matrix.smul_eq_mul_diagonal N a]


--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

DisabledTactic simp
--NewTactic use
NewTheorem Matrix.smul_eq_mul_diagonal Matrix.mul_assoc Matrix.det_transpose mul_comm MulZeroClass.zero_mul Matrix.inv_eq_right_inv
NewDefinition Matrix Fin invertibleMul Invertible
