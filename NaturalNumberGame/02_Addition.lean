import NaturalNumberGame.MyNat

namespace MyNat

example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]


example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero, add_zero]

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c, add_zero b]

theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]

theorem add_zero_right (a : ℕ) : a + 0 = a := by
  sorry

theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  sorry

theorem add_comm (a b : ℕ) : a + b = b + a := by
  sorry

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  sorry

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  sorry

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  sorry

theorem succ_add_right (a b : ℕ) : a + succ b = succ (a + b) := by
  sorry

theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  sorry

end MyNat
