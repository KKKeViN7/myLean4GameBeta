import Game.Metadata

World "EigenvaluesWorld"
Level 9
Title "The invert eigenvalue"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix
open Module End
open Polynomial

Statement (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n) → ℝ) (μ : ℝ)
  (h : HasEigenvector (Matrix.toLin' A) μ x) [Invertible A] [Invertible μ]:
    HasEigenvector (Matrix.toLin' A⁻¹) μ⁻¹ x := by
      rw [HasEigenvector] at h
      cases h
      rw [mem_eigenspace_iff] at left
      rw [toLin'_apply] at left
      have h1 : A⁻¹ *ᵥ A *ᵥ x = A⁻¹ *ᵥ μ • x := by rw [left]
      simp at h1
      have h2 : μ⁻¹ • x = μ⁻¹ • A⁻¹ *ᵥ μ • x := by
        nth_rw 1 [h1]
      rw [mulVec_smul] at h2
      simp [smul_smul] at h2
      apply And.intro
      rw [mem_eigenspace_iff]
      rw [toLin'_apply]
      simp [h2]
      exact right

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Matrix.toLin'_apply Matrix.smul_mulVec_assoc smul_assoc
--NewDefinition Polynomial.X Polynomial.C Matrix.charpoly Matrix.charmatrix
