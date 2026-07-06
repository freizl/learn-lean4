import NaturalNumberGame.MyNat
import «NaturalNumberGame».«01_Tutorial»
import «NaturalNumberGame».«02_Addition»

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
  rw [add_comm n a, add_comm n b]
  exact add_right_cancel a b n

theorem add_right_eq_self (a b : ℕ) : a + b = a → b = 0 := by
  nth_rewrite 2 [← add_zero a] -- a + b = a + 0 -> b = 0
  exact add_left_cancel b 0 a

theorem add_left_eq_self (a b : ℕ) : b + a = a → b = 0 := by
  nth_rewrite 2 [← zero_add a] -- b + a = 0 + a -> b = 0
  exact add_right_cancel b 0 a

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with
   | zero =>
      rw [zero_eq_0]
      rw [add_zero]
      -- TODO: any shortcut for "intro h; exact h;"
      intro h
      exact h
   | succ d =>
     rw [add_succ]
     intro h2
     symm at h2
     apply zero_ne_succ at h2
    --  Another example: if you have a hypothesis h : False then you are done,
    -- because a false statement implies any statement.
    -- Here cases h will close the goal, because there are no ways to
    -- make a proof of False! So you will end up with no goals,
    -- meaning you have proved everything.
     cases h2


theorem add_left_eq_zero (a b : ℕ) : b + a = 0 → a = 0 := by
  rw [add_comm]
  exact add_right_eq_zero a b
