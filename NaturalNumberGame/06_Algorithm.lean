import NaturalNumberGame.MyNat

namespace MyNat

theorem pred_zero : pred 0 = 0 := by
  sorry

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 := by
  sorry

theorem is_zero_zero : is_zero 0 := by
  sorry

theorem pred_succ' (n : ℕ) : pred (succ n) = n := by
  sorry

theorem succ_pred' (n : ℕ) : succ (pred n) = n := by
  sorry

theorem is_zero_succ' (n : ℕ) : is_zero (succ n) = False := by
  sorry

theorem zero_ne_succ''' (n : ℕ) : 0 ≠ succ n := by
  sorry

theorem succ_ne_zero' (n : ℕ) : succ n ≠ 0 := by
  sorry

theorem pred_zero' : pred 0 = 0 := by
  sorry

end MyNat
