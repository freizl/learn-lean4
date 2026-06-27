import NaturalNumberGame.MyNat

example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2

theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

theorem not_or_left (P Q : Prop) : ¬ (P ∨ Q) → ¬ P := by
  sorry

theorem not_or_right (P Q : Prop) : ¬ (P ∨ Q) → ¬ Q := by
  sorry

theorem and_imp (P Q : Prop) : P ∧ Q → P := by
  sorry

theorem imp_and (P Q : Prop) : P → Q → P ∧ Q := by
  sorry

theorem iff_refl (P : Prop) : P ↔ P := by
  sorry

theorem iff_symm (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  sorry

theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

theorem false_implies_any (P : Prop) : False → P := by
  sorry

theorem any_implies_true (P : Prop) : P → True := by
  sorry
