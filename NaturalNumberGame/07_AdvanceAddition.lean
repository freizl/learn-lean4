import NaturalNumberGame.MyNat

namespace MyNat

theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with
   | zero =>
     rw [zero_eq_0]
     intro h1
     rw [add_zero, add_zero] at h1
     exact h1
   | succ n hn =>
     rw [add_succ, add_succ]
     intro h2
     apply succ_inj at h2
     exact hn h2

theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  sorry

theorem add_right_eq_self (a b : ℕ) : a + b = a → b = 0 := by
  sorry

theorem add_left_eq_self (a b : ℕ) : b + a = a → b = 0 := by
  sorry

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  sorry

theorem add_left_eq_zero (a b : ℕ) : b + a = 0 → a = 0 := by
  sorry
