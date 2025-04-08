import Game.Metadata

World "DeterminantWorld"
Level 5
Title "The row equal determinant"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

theorem det_permute_row [DecidableEq n] [Fintype n] [CommRing R]
  (M : Matrix n n R) (i j : n) (i_ne_j : i ≠ j):
    (Matrix.det fun a b => M (Equiv.swap i j a) b) = -1 * M.det := by
      rw [det_permute (Equiv.swap i j) M]
      rw [Equiv.Perm.sign_swap i_ne_j]
      simp

Statement [DecidableEq n] [Fintype n]
  (M : Matrix n n ℝ) (i j : n) (i_ne_j : i ≠ j) (hij : M i = M j) :
    M.det = 0 := by
      have h_swap : M = fun a b => M (Equiv.swap i j a) b := by ext a b; rw [Equiv.apply_swap_eq_self hij]
      have h_eq : M.det = -1 * M.det := by rw [←det_permute_row M i j i_ne_j]; rw [←h_swap]
      have h_add : M.det + M.det = 0 := by nth_rw 1 [h_eq];simp
      rw [add_self_eq_zero] at h_add
      exact h_add
      /-rw [←two_mul] at h_add
      rw [mul_eq_zero] at h_add
      cases h_add
      have h_neq: ¬ (2 : ℝ) = 0 := by simp
      contradiction
      exact h-/

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic ext nth_rw
NewTheorem det_permute_row Equiv.apply_swap_eq_self two_mul mul_eq_zero add_self_eq_zero
--NewDefinition
