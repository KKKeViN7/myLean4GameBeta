import Game.Metadata

World "RankWorld"
Level 3
Title "The mul isunit rank1"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (P A Q: Matrix (Fin n) (Fin n) ℝ) (hp : IsUnit P) (hq : IsUnit Q):
  (P * A * Q).rank = A.rank := by
    rw [isUnit_iff_isUnit_det] at hp
    rw [isUnit_iff_isUnit_det] at hq
    rw [mul_assoc]
    rw [rank_mul_eq_right_of_isUnit_det]
    rw [rank_mul_eq_left_of_isUnit_det]
    exact hq
    exact hp

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.rank_mul_eq_right_of_isUnit_det Matrix.rank_mul_eq_left_of_isUnit_det
--NewDefinition
