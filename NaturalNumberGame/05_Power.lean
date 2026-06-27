import NaturalNumberGame.MyNat

namespace MyNat

theorem pow_zero (n : ℕ) : n ^ 0 = 1 := by
  sorry

theorem one_pow (n : ℕ) : 1 ^ n = 1 := by
  sorry

theorem pow_one (n : ℕ) : n ^ 1 = n := by
  sorry

theorem pow_succ (n k : ℕ) : n ^ (k + 1) = n ^ k * n := by
  sorry

theorem pow_add (n a b : ℕ) : n ^ (a + b) = n ^ a * n ^ b := by
  sorry

theorem pow_mul (n a b : ℕ) : n ^ (a * b) = (n ^ a) ^ b := by
  sorry

theorem two_pow_two : (2 : ℕ) ^ 2 = 4 := by
  sorry

theorem three_pow_two : (3 : ℕ) ^ 2 = 9 := by
  sorry

theorem zero_pow_succ (n : ℕ) : 0 ^ (n + 1) = 0 := by
  sorry

theorem one_pow_succ (n : ℕ) : 1 ^ (n + 1) = 1 := by
  sorry

end MyNat
