import Game.Metadata

World "DeterminantWorld"
Level 9
Title "The invert determinant2"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

/-Statement [DecidableEq n] [Fintype n] [CommRing R]:
  det (1 : Matrix n n R) = 1 := by
    rw [← diagonal_one]
    rw [det_diagonal]
    simp-/

Statement [DecidableEq n] [Fintype n]
  (A P: Matrix n n ℝ) [Invertible P] [Invertible P.det] :
    det (P * A * P⁻¹) = (det A) := by
      rw [det_mul]
      rw [mul_comm]
      rw [det_mul]
      rw [←mul_assoc]
      simp

--det_updateRow_smul
--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic
NewTheorem mul_comm mul_assoc
--NewDefinition
