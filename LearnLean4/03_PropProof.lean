
#check Prop

section
  def g (a b : Nat) : Nat :=
    a + b

  #check g 2 3
  #eval g 2 3
end

namespace PropProofExamples

def f (p q : Prop) : Prop :=
  p ∧ q

#check f
#check f True False

end PropProofExamples

/-
1. `theorem` is special form of `def`, no differ for the kernel type check.
2. `theorem` takes Prop but function takes Type
3. There are still practical differences - check section 3.2 in book.
   I didn't fully understand it yet.
   All I can think of from tricky coding perpsective is theorm is just function,
   we need to construct implementation (proof) to honor the type (Prop), using tactics (propositional logic).

   So Just remember Prop and Type are at same level.
-/
section PropProof
  set_option linter.unusedVariables false

  variable (P Q : Prop)
  variable (α β : Type)

  theorem t1 : P → Q → P :=
    fun hp => fun hq => hp

  def f1 : α → β → α :=
    fun a => fun b => a

  #check t1
  #check f1

end PropProof

section PropLogic

  #check False
  #check True
  #check Not
  #check And
  #check Or
  #check Iff
  #check ¬True
  #check True ∧ False
  #check True ∨ False
  #check True → False
  #check True ↔ True
end PropLogic

/-
## Mental Model: Generic Type vs Generic Prop

### Direct Comparison

In Haskell:
  id :: forall a. a -> a
  id x = x
  -- When called: id @Int 42 → α=Int, x=42

In Lean:
  theorem foo {p : Prop} (hp : p) : p := hp
  -- When called: @foo (1=1) rfl → p=(1=1), hp=rfl

### What Can `p : Prop` Be?

Just like `α` can be `Nat`, `String`, `Bool`...
`p` can be any proposition:
  - `True`
  - `1 = 1`
  - `n > 0`
  - `List.length xs = 0`
  - `∀ x, x = x`

### What Can the Body Do with `hp : p`?

`hp` is EVIDENCE. You can:
  1. Return it (like id)
  2. Pass it to other theorems that need proof of p
  3. Pattern match on it (if p has structure, e.g., And.left)
  4. Use it to unlock information (e.g., h.symm for equality)

### The Parallel

  | Generic Type    | Generic Prop                    |
  |-----------------|-------------------------------- |
  | `{α : Type}`    | `{p : Prop}`                    |
  | α = Nat, String | p = (1=1), (n>0), True, ...     |
  | `(a : α)` = val | `(hp : p)` = proof              |
  | `42 : Nat`      | `rfl : 1=1`                     |

So `{p : Prop}` says "for any proposition p",
and `hp : p` says "given a proof of that proposition".
-/

#check 1=1
#check rfl
theorem foo {p : Prop} (hp : p) : p := hp
#check @foo (1=1) rfl  -- @foo makes implicit {p} explicit
#check foo True.intro           -- p=True, hp=True.intro
#check foo (Nat.zero_lt_one)    -- p=(0<1), hp=Nat.zero_lt_one
#check foo (Nat.le_refl 5)      -- p=(5≤5), hp=Nat.le_refl 5
#check foo (And.intro True.intro False.elim)  -- p=(True∧True)
#check True
#check True.intro

section Conjunction
  variable (p q : Prop)
  example (hp : p) (hq : q) : p ∧ q :=
    And.intro hp hq

  #check And.intro

  -- does not work since it requires proofs of p and q but not Prop.
  -- e.g. p: Prop := 1 = 1, hp : p
  -- example (hp : Prop) (hq : Prop) : Prop ∧ Prop :=
  --   And.intro hp hq

  -- Compare with generic functions
  variable (α β : Type)
  def g2 (ha : α) : Nat := sorry
  #print g2
  #check g2 Nat 2

end Conjunction

#check Or.intro_left

namespace disconjunction
  def f {p q : Prop} (h : p ∨ q) : q ∨ p :=
   Or.elim h
    (fun hp : p => Or.inr hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

  def g {p q : Prop} (h : p ∨ q) : q ∨ p :=
    Or.elim h Or.inr Or.inl

  #check f
  #check g

end disconjunction

namespace Negation
  variable (p q : Prop)
  -- `¬p` means `p -> False`, that's why the definition body has `fun hp: p ...`
  def f (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p => hnq (hpq hp)

  #check f

  example (hp : p) (hnp : ¬p) : q := absurd hp hnp
  #check absurd

end Negation

namespace Equivalence
  variable (p q : Prop)
  def f (hpq : p → q) (hqp : q → p) : p ↔ q :=
    Iff.intro hpq hqp

  #check f

  #check Iff.intro
  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun hpq : p ∧ q => And.intro hpq.right hpq.left)
      (fun hqp : q ∧ p => And.intro hqp.right hqp.left)

  theorem and_swap_v2 : p ∧ q ↔ q ∧ p :=
    ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩
  #check and_swap_v2

  theorem test1 (h : p ∧ q) : q ∧ p :=
    Iff.mp (and_swap_v2 p q) h
  #check test1

  theorem test2 (h: p -> q) (hp : p) : q :=
    h hp
  #check test2

end Equivalence

namespace Exercises
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun (hpq : p ∧ q) => ⟨hpq.right, hpq.left⟩)
      (fun (hqp : q ∧ p) => ⟨hqp.right, hqp.left⟩)

  #check Or.comm
  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (fun (hpq : p ∨ q) => Or.symm hpq)
      (fun (hqp : q ∨ p) => Or.symm hqp)

  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (fun (hpq : p ∨ q) => Or.elim hpq Or.inr Or.inl)
      (fun (hqp : q ∨ p) => Or.elim hqp Or.inr Or.inl)

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (fun (h1 : (p ∧ q) ∧ r) => ⟨ h1.left.left, ⟨h1.left.right, h1.right⟩ ⟩)
      (fun (h2 : p ∧ (q ∧ r)) => ⟨ ⟨ h2.left, h2.right.left⟩, h2.right.right ⟩)

  -- Or.elim :: (a ∨ b) -> (a -> c) -> (b -> c) -> c
  -- (p ∨ q) ∨ r) -> (p ∨ q -> ??) -> (r -> c) -> (p ∨ (q ∨ r))
  --   p ∨ q -> (p -> p ∨ (q ∨ r)) -> (q -> p ∨ (q ∨ r)) -> p ∨ (q ∨ r)
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      (fun (h1 : (p ∨ q) ∨ r) => Or.elim h1
                                   (fun (g1 : p ∨ q) => Or.elim g1
                                                          (fun g11 => Or.inl g11)
                                                          (fun g12 => Or.inr (Or.inl g12)))
                                   (fun (g2 : r) => Or.inr (Or.inr g2)))
      (fun (h2 : p ∨ (q ∨ r)) => Or.elim h2
                                   (fun (g1 : p) => Or.inl (Or.inl g1))
                                   (fun (g2 : (q ∨ r)) => Or.elim g2
                                                          (fun g21 => Or.inl (Or.inr g21))
                                                          (fun g22 => Or.inr g22)))

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      (fun (h1 : p ∧ (q ∨ r)) => Or.elim h1.right
                                   (fun (g1 : q) => Or.inl ⟨h1.left, g1⟩)
                                   (fun (g2 : r) => Or.inr ⟨h1.left, g2⟩))
      (fun (h2 : (p ∧ q) ∨ (p ∧ r)) => Or.elim h2
                                   (fun (g1 : (p ∧ q)) => ⟨g1.left, Or.inl g1.right⟩)
                                   (fun (g2 : (p ∧ r)) => ⟨g2.left, Or.inr g2.right⟩))

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
       (fun h1 => Or.elim h1
                     (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
                     (fun hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
       (fun h2 => Or.elim h2.left
                    (fun hp => Or.inl hp)
                    (fun hq => Or.elim h2.right
                               (fun hp2 => Or.inl hp2)
                               (fun hr => Or.inr ⟨hq, hr⟩) ))

  -- other properties
  -- p ∧ q -> r means an function (p ∧ q) -> r
  example : (p → (q → r)) ↔ (p ∧ q → r) :=
     Iff.intro
        (fun h1 => fun hpq => h1 hpq.left hpq.right)
        (fun h1 => fun hp => fun hq => h1 ⟨hp,hq⟩)

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
     Iff.intro
       (fun h1 => ⟨ fun hp => h1 (Or.inl hp), fun hq => h1 (Or.inr hq) ⟩)
       (fun h2 => fun hpq => Or.elim hpq h2.left h2.right)

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
   Iff.intro
     -- (h1 : p ∨ q -> False) -> (p -> False ∧ q -> False)
     (fun h1 => ⟨ h1 ∘ Or.inl, h1 ∘ Or.inr ⟩)
     (fun h2 => fun hpq => Or.elim hpq h2.left h2.right )

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h1 =>  -- ¬p ∨ ¬q
     fun h2 => -- (p ∧ q)
      Or.elim h1
        (fun hnp => hnp h2.left)
        (fun hnq => hnq h2.right)

  example : ¬(p ∧ ¬p) :=
    fun h1 => -- p ∧ ¬p ... p ∧ (p -> False)
      h1.right h1.left

  example : p ∧ ¬q → ¬(p → q) :=
    fun hpnq => -- p ∧ ¬q  .... p ∧ (q -> False)
      fun hpq => -- p -> q
        hpnq.right (hpq hpnq.left)

  #check absurd
  example : ¬p → (p → q) :=
     fun hnp =>
       fun hp =>
         absurd hp hnp

  example : (¬p ∨ q) → (p → q) :=
    fun hnpq =>
      fun hp =>
        Or.elim hnpq
           (fun np => absurd hp np)
           id

  example : p ∨ False ↔ p :=
    Iff.intro
      (fun hpf => Or.elim hpf id False.elim)
      (fun hp => Or.inl hp)

  example : p ∧ False ↔ False :=
    Iff.intro And.right False.elim

  example : (p → q) → (¬q → ¬p) :=
    fun hpq =>    -- p -> q
      fun hnq =>  -- q -> False
        fun hnp => -- p
           hnq (hpq hnp)

end Exercises

namespace ClassicalLogic
  open Classical
  #check em
  #check byContradiction
  #check byCases
  
  variable (p q r : Prop)
  
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry

end ClassicalLogic
