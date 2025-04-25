import Game.Metadata

World "OrthogonalityWorld"
Level 7
Title "The orthogonal matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Aᵀ * A = 1) :
  A.HasOrthogonalCols := by
    intro i j hij
    have h_entry := congr_fun (congr_fun h i) j
    rw [Matrix.one_apply_ne hij] at h_entry
    simp [mul_apply] at h_entry
    simp [Matrix.dotProduct]
    exact h_entry

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.one_apply_ne congr_fun Matrix.mul_apply
NewDefinition Matrix.dotProduct
