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
