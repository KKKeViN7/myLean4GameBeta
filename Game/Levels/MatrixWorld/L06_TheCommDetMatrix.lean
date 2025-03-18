import Game.Metadata

World "MatrixWorld"
Level 6
Title "The comm det matrix"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing R]
  (A B : Matrix n n R) :
    det (A * B) = det (B * A) := by
      rw [det_mul]
      rw [det_mul]
      Hint "ring 策略是 Lean 中一个强大的自动化策略，用于证明环（ring）上的等式。它能够自动应用环的公理和基本性质，如交换律、结合律、分配律等。"
      ring


--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic ring
NewTheorem Matrix.det_mul
NewDefinition Matrix.det
