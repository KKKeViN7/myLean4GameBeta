import Game.Metadata

World "MatrixWorld"
Level 9
Title "The mul invert matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement [Fintype n] [DecidableEq n] [CommRing α]
  (A B : Matrix n n α) :
    (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
      simp only [Matrix.inv_def]
      rw [Matrix.smul_mul]
      rw [Matrix.mul_smul]
      rw [smul_smul]
      rw [det_mul]
      rw [Ring.mul_inverse_rev]
      rw [adjugate_mul_distrib]


/-example [Fintype n] [DecidableEq n] [CommRing α]
  (A B : Matrix n n α) [Invertible A] [Invertible B]:
    (A * B) * (B⁻¹ * A⁻¹) = (1 : Matrix n n α) := by
      rw [←Matrix.mul_assoc]
      simp-/

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.inv_def Matrix.smul_mul Matrix.mul_smul smul_smul Ring.mul_inverse_rev Matrix.adjugate_mul_distrib
--NewDefinition
