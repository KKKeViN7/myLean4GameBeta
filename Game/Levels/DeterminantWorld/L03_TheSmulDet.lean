import Game.Metadata

World "DeterminantWorld"
Level 3
Title "The smul determinant"

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

Statement (n : ℕ)(A : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) :
    ∀ x : Fin n, det (of fun i j => if i = x then k * A i j else A i j) = k * det A := by
      intro x
      --Hint let
      let v : (Fin n) → ℝ := fun i => if i = x then k else 1
      have h_eq : of (fun i j => if i = x then k * A i j else A i j) = of (fun i j => v i * A i j) := by
        simp
        ext i j
        simp [v]
      rw [h_eq]
      rw [det_mul_column v A]
      simp [v]

--det_updateRow_smul
--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic
NewTheorem Matrix.det_mul_column
--NewDefinition
