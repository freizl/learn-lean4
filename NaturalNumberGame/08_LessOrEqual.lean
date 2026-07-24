import NaturalNumberGame.MyNat
import Mathlib
import «NaturalNumberGame».«01_Tutorial»
import «NaturalNumberGame».«02_Addition»
import «NaturalNumberGame».«07_AdvanceAddition»

namespace MyNat

-- a ≤ b is notation for ∃ c, b = a + c.
theorem le_refl (x : ℕ) : x ≤ x := by
  use 0
  rw [add_zero]

theorem zero_le (x : ℕ) : 0 ≤ x := by
 -- ∃c, x = 0 + c
  use x
  rw [zero_add]

theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  -- succ x = x + c
  use 1
  rw [succ_eq_add_one]

theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
-- y = x + c1
-- z = y + c2
-- z = x + c3
  cases hxy with
    | intro a ha =>
       cases hyz with
        | intro b hb =>
           rw [ha, add_assoc] at hb
           use (a+b)

theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with
    | intro a ha =>
      symm at ha
      apply add_right_eq_zero x a at ha
      exact ha

theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases hxy with
    | intro a ha =>
      cases hyx with
        | intro b hb =>
          rw [ha, add_assoc] at hb
          symm at hb
          apply add_right_eq_self at hb
          apply add_right_eq_zero at hb
          rw [hb, add_zero] at ha
          symm at ha
          exact ha
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2


theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  cases x with
    | zero => cases y with
       | zero =>
          rw [zero_eq_0]
          exact Or.inl (le_refl 0)
       | succ d =>
          rw [zero_eq_0]
          exact Or.inl (zero_le (succ d))
    | succ d1 => cases y with
       | zero =>
          rw [zero_eq_0]
          exact Or.inr (zero_le (succ d1))
       | succ d2 =>
           cases le_total d1 d2 with
              | inl h1 =>
                cases h1 with
                  | intro c hc =>
                    -- rw [← add_left_cancel d2 (d1+c) 1] at hc
                    -- rw [← add_assoc 1 d1 c] at hc
                    -- rw [succ_add] at hc
                    apply Or.inl
                    use c
                    rw [succ_add, ← hc]
              | inr h2 =>
                cases h2 with
                  | intro c hc =>
                    apply Or.inr
                    use c
                    rw [succ_add, ← hc]

theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by


end MyNat
