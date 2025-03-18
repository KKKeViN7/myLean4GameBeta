import Game.Metadata

World "MatrixWorld"
Level 4
Title "The non comm matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement : ∃ (A B : Matrix (Fin 2) (Fin 2) ℕ), A * B ≠ B * A := by
  simp
  use !![1, 2; 3, 4]
  use !![4, 3; 2, 1]
  have ab : !![1, 2; 3, 4] * !![4, 3; 2, 1] = !![8, 5; 20, 13] := by simp
  have ba : !![4, 3; 2, 1] * !![1, 2; 3, 4] = !![13, 20; 5, 8] := by simp
  rw [ab]
  rw [ba]
  intro h
  apply Matrix.ext_iff.mpr at h
  have h00 := h 0 0
  repeat rw [Matrix.of_apply] at h00
  have a00: ![![8, 5], ![20, 13]] 0 0 = 8 := by simp
  have b00: ![![13, 20], ![5, 8]] 0 0 = 13 := by simp
  rw [a00] at h00
  rw [b00] at h00
  contradiction

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic use
NewTheorem Matrix.ext_iff Matrix.of_apply
--NewDefinition
