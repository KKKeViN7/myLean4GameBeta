import Game.Metadata

World "MatrixWorld"
Level 10
Title "The transpose invert matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] :
  A⁻¹ᵀ = Aᵀ⁻¹ := by
    Branch
      rw [Matrix.inv_def]
      rw [Matrix.inv_def]
      rw [transpose_smul]
      rw [adjugate_transpose]
      rw [det_transpose]
    have h1 : Aᵀ * A⁻¹ᵀ = 1 := by
      rw [← transpose_mul A⁻¹ A]
      simp
    have h2 : Aᵀ⁻¹ * Aᵀ * A⁻¹ᵀ = Aᵀ⁻¹ := by
      rw [mul_assoc]
      simp [h1]
    simp at h2
    exact h2


--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.transpose_smul Matrix.adjugate_transpose
--NewDefinition
