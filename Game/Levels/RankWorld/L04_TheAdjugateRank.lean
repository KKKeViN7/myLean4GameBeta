import Game.Metadata

World "RankWorld"
Level 4
Title "The adjugate rank"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix


Statement (n : ℕ) (A E: Matrix (Fin n) (Fin n) ℝ) (h : IsUnit A) (he : E = 1) :
  (adjugate A).rank = n := by
    rw [isUnit_iff_isUnit_det] at h
    have h1 : (A * adjugate A).rank = (A.det • E).rank := by
      rw [he]
      rw [mul_adjugate]
    have h2 : (A.det • E).rank = n := by
      rw [Matrix.smul_eq_mul_diagonal E A.det]
      rw [rank_mul_eq_right_of_isUnit_det]
      rw [rank_diagonal]
      have h3 : det A ≠ 0 := by
        have h4 : A⁻¹ * A = 1 := by
          rw [nonsing_inv_mul]
          exact h
        apply det_ne_zero_of_left_inverse h4
      simp [h3]
      rw [Fintype.subtype_card]
      repeat simp [he]
    rw [h2] at h1
    rw [rank_mul_eq_right_of_isUnit_det] at h1
    exact h1
    exact h

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.rank_diagonal Matrix.det_ne_zero_of_left_inverse Fintype.subtype_card
--NewDefinition
