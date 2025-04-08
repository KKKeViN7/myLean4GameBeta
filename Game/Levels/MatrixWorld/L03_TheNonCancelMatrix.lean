import Game.Metadata

World "MatrixWorld"
Level 3
Title "The non cancel matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

/-Statement [CommSemiring R]
  (A B : Matrix (Fin 1) (Fin 1) R) :
    A * B = B * A := by
      ext i j
      simp [Matrix.mul_apply]
      fin_cases i
      fin_cases j
      simp
      apply mul_comm-/

Statement : ∃ n : ℕ, ∃ (A B C: Matrix (Fin n) (Fin n) ℕ), A * B = A * C ∧ B ≠ C := by
  use 2
  use (0 : Matrix (Fin 2) (Fin 2) ℕ)
  use ![![1, 2], ![3, 4]]
  use ![![4, 3], ![2, 1]]
  apply And.intro
  rw [zero_mul]
  rw [zero_mul]
  intro h
  apply Matrix.ext_iff.mpr at h
  have h00 := h 0 0
  have b00: ![![(1 : ℕ), 2], ![3, 4]] 0 0 = 1 := by simp
  have c00: ![![(4 : ℕ), 3], ![2, 1]] 0 0 = 4 := by simp
  rw [b00] at h00
  rw [c00] at h00
  contradiction

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic fin_cases
NewTheorem Matrix.mul_apply Matrix.ext_iff Matrix.zero_mul
--NewDefinition
