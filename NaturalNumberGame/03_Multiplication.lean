import NaturalNumberGame.MyNat

namespace MyNat

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]
  rfl
