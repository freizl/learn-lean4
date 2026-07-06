import NaturalNumberGame.MyNat

namespace MyNat

theorem mul_left_cancel (a b n : ℕ) : n * a = n * b → a = b := by
  sorry

theorem mul_right_cancel (a b n : ℕ) : a * n = b * n → a = b := by
  sorry

theorem mul_right_eq_one (a b : ℕ) : a * b = 1 → a = 1 := by
  sorry

theorem mul_left_ne_zero (a b : ℕ) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  sorry

theorem eq_succ_of_ne_zero (a : ℕ) : a ≠ 0 → ∃ b, a = succ b := by
  sorry

theorem one_le_of_ne_zero (a : ℕ) : a ≠ 0 → 1 ≤ a := by
  sorry

theorem le_mul_right (a b : ℕ) : 0 < a → b ≤ a * b := by
  sorry

theorem mul_eq_zero' (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0 := by
  sorry

theorem mul_ne_zero' (a b : ℕ) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  sorry

theorem mul_right_eq_self (a b : ℕ) : a * b = a → b = 1 := by
  sorry

end MyNat
