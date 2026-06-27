import NaturalNumberGame.MyNat

example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2
