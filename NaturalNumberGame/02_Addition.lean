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

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
   | zero =>
     rw [zero_eq_0]
     rw [add_zero]
   | succ d hd =>
     rw [add_succ, hd]


theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
     rw [zero_eq_0]
     rw [add_zero, add_zero]
  | succ d hd =>
     rw [add_succ, add_succ, hd]

theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero =>
     repeat rw [zero_eq_0]
     rw [add_zero, zero_add]
  | succ d hd =>
     rw [add_succ, succ_add, hd]

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
     repeat rw [zero_eq_0]
     rw [add_zero, add_zero]
  | succ d hd =>
     rw [add_succ, add_succ, add_succ, hd]

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

end MyNat
