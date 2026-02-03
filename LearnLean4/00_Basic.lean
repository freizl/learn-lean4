def hello := "world"

def hfun (f: α → β → χ) (g: (β → α) → β) (a:α) :=
  f a (g (λ _b => a))

section Test
  variable {α : Type} [Add α] [One α]
  def test1 (x: α) := x + 1

  variable (x : Nat)
  def test2 := x + 1
end Test

namespace Test
  def test2 x := x * 2
end Test

#check test1
#check Test.test2
#check hfun


/- section 2.8 examples -/

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨ a, b ⟩

def h0 (x : Nat) :=
  f Type (λ a => a) Nat x

def h1 (x : Nat) : Nat := (h0 x).2

#check h0
#check h1
#eval h1 3

-- More interesting β functions when a is a Type like Nat

-- β = List, so b : List Nat
def h2 : (a : Type) × List a :=
  f Type List Nat [1, 2, 3]

-- β = Option, so b : Option Nat
def h3 : (a : Type) × Option a :=
  f Type Option Nat (some 42)

-- β = (T → T), so b : Nat → Nat (an endomorphism)
def h4 : (a : Type) × (a → a) :=
  f Type (λ T => T → T) Nat (· + 1)
                             -- func x => x + 1

-- β = (T → Bool), so b : Nat → Bool (a predicate)
def h5 : (a : Type) × (a → Bool) :=
  f Type (λ T => T → Bool) Nat (· > 0)

-- β = (T × T), so b : Nat × Nat
def h6 : (a : Type) × (a × a) :=
  f Type (λ T => T × T) Nat (3, 7)

#check h2
#check h3
#check h4
#check h5
#check h6

#eval h2.2        -- [1, 2, 3]
#eval h3.2        -- some 42
#eval h6.2     -- (3, 7)

/-
QUIZ: Existential Types
Q1: Why can't we do `#eval h4.2 10`?
-/
