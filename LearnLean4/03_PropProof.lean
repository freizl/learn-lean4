
#check Prop

def g (a b : Nat) : Nat :=
  a + b

#check g 2 3
#eval g 2 3

def f (p q : Prop) : Prop :=
  p ∧ q

#check f
#check f True False


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
