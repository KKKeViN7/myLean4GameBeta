import Game.Metadata

World "OrthogonalityWorld"
Level 3
Title "The dot product self"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (u : Fin n → ℝ) : u ⬝ᵥ u ≥ 0 ∧ (u ⬝ᵥ u = 0 ↔ u = 0) := by
  apply And.intro
  rw [dotProduct]
  apply Finset.sum_nonneg
  simp
  intro i
  exact mul_self_nonneg (u i)
  apply Iff.intro
  intro h
  rw [dotProduct] at h
  rw [sum_eq_zero_iff_of_nonneg] at h
  simp at h
  exact funext h
  have h_nonneg : ∀ i, 0 ≤ u i * u i := by
    intro i
    apply mul_self_nonneg
  simp [h_nonneg]
  intro h
  simp [h]

  --exact dotProduct_self_eq_zero

--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem Finset.sum_nonneg mul_self_nonneg Matrix.dotProduct_self_eq_zero
NewDefinition Matrix.dotProduct
