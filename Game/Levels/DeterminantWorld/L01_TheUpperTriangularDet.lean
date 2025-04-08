import Game.Metadata
import Mathlib.Init.Order.Defs

World "DeterminantWorld"
Level 1
Title "The upper triangular determinant"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

/-Statement [LinearOrder m] [DecidableEq m] [Fintype m] [CommRing R]
  (A : Matrix m m R) (h : BlockTriangular A id) :
    det A = ∏ i : m, A i i := by
      rw [det_of_upperTriangular]
      exact h-/

Statement [LinearOrder m] [DecidableEq m] [Fintype m] [CommRing R]
  (v : m → R) (A : Matrix m m R) (h: A = diagonal v) :
    det A = ∏ i, v i := by
      have heq : ∏ i, v i = ∏ i, A i i := by
        rw[h]
        simp
      rw[heq]
      rw [det_of_upperTriangular]
      intro i j hij
      rw [h]
      rw [diagonal_apply_ne]
      simp at hij
      exact ne_of_gt hij

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic
NewTheorem Matrix.det_of_upperTriangular Matrix.diagonal_apply_ne ne_of_gt
NewDefinition Matrix.det Matrix.of
