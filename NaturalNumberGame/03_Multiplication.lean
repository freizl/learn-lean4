import NaturalNumberGame.MyNat
import «NaturalNumberGame».«01_Tutorial»
import «NaturalNumberGame».«02_Addition»

namespace MyNat

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero => rw [zero_eq_0, mul_zero]
  | succ d hd =>
     rw [mul_succ, hd, add_zero]

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction b with
  | zero => rw [zero_eq_0, mul_zero, mul_zero, add_zero]
  | succ d hd =>
      rw [mul_succ, mul_succ, hd, add_succ, add_succ]
      rw [add_assoc, add_assoc, add_comm a d]

theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with
  | zero => rw [zero_eq_0, mul_zero, zero_mul]
  | succ d hd =>
      rw [mul_succ, succ_mul, hd]


theorem one_mul (m : ℕ) : 1 * m = m := by
  induction m with
  | zero => rw [zero_eq_0, mul_zero]
  | succ d hd => rw [mul_succ, hd, ← succ_eq_add_one]

theorem one_mul_2 (m : ℕ) : 1 * m = m := by
  rw [mul_comm, mul_one]

theorem two_mul (m : ℕ): 2 * m = m + m := by
  rw [mul_comm, two_eq_succ_one, mul_succ, mul_one]

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
     rw [zero_eq_0, add_zero, mul_zero, add_zero]
  | succ d hd =>
     rw [add_succ, mul_succ, mul_succ, hd, add_assoc]


theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm a c]


theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [zero_eq_0, mul_zero, mul_zero, mul_zero]
  | succ d hd =>
    rw [mul_succ, mul_succ, mul_add, hd]


end MyNat
