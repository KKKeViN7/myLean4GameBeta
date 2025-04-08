import Game.Metadata

World "OrthogonalityWorld"
Level 5
Title "The div norm unit"

/-Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."-/
Introduction "
欢迎来到你的 Lean 线性代数之旅的第一关！在这一关中，我们将学习 Lean 中最简单但又非常重要的证明策略：rfl 和 rw 。

rw 是 rewrite（重写）的缩写，它允许你使用已知的等式替换证明目标中的一部分。这就像在数学证明中“代入”或“替换”的概念。
"
open Finset Function OrderDual
open BigOperators Matrix

Statement (n : ℕ) (v: Fin n → ℝ):
  v ≠ 0 → ‖(‖v‖⁻¹ • v)‖ = 1 := by
    intro hv
    have hnorm_ne_zero : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_inv]
    simp [mul_comm]
    rw [mul_inv_cancel]
    exact hnorm_ne_zero


--Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

--NewTactic ring
NewTheorem norm_ne_zero_iff Real.norm_eq_abs abs_inv inv_eq_one_div mul_inv_cancel
--NewDefinition
