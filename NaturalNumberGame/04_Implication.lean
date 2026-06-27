import NaturalNumberGame.MyNat

namespace MyNat

example (a b : ℕ) (h : a = b) : succ a = succ b := by
  rw [h]

theorem succ_eq_succ_of_eq (a b : ℕ) (h : a = b) : succ a = succ b := by
  rw [h]

theorem zero_ne_succ' (a : ℕ) : 0 ≠ succ a := by
  sorry

theorem eq_of_succ_eq_succ (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry

theorem succ_inj' (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry

theorem not_succ_eq_zero (a : ℕ) : succ a ≠ 0 := by
  sorry

theorem zero_ne_succ'' (a : ℕ) : 0 ≠ succ a := by
  sorry

theorem eq_trans' (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  sorry

theorem eq_symm' (a b : ℕ) (h : a = b) : b = a := by
  sorry

theorem false_elim' (a : Prop) : False → a := by
  sorry

theorem not_false : ¬ False := by
  sorry

end MyNat
