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
