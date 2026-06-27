import NaturalNumberGame.MyNat
import «NaturalNumberGame».«02_Addition»

namespace MyNat

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  sorry

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry

theorem mul_zero (m : ℕ) : m * 0 = 0 := by
  sorry

theorem one_mul (m : ℕ) : 1 * m = m := by
  sorry

theorem mul_comm (a b : ℕ) : a * b = b * a := by
  sorry

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  sorry

theorem mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  sorry

theorem mul_right_comm (a b c : ℕ) : (a * b) * c = (a * c) * b := by
  sorry

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  sorry

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

end MyNat
