import Game.Metadata

World "MatrixWorld"
Level 8
Title "The adjugate det matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hnz : n > 0)
  [Invertible A] [Invertible A.det] :
    (adjugate A).det = A.det ^ (n - 1) := by
      have h : adjugate A = A.det • (⅟ A) := by
        rw [invOf_eq]
        simp [smul_smul]
      rw [h]
      rw [det_smul]
      rw [det_invOf]
      have h2 : det A ^ n = det A ^ (n - 1) * det A := by
        rw [←pow_succ, Nat.sub_add_cancel]
        linarith
      simp [h2]
      simp [mul_assoc]


--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.invOf_eq Matrix.det_smul Matrix.det_invOf pow_succ Nat.sub_add_cancel Fintype.card_pos
NewDefinition Fintype.card
