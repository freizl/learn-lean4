
namespace Equality

#check Eq.refl
#check Eq.symm


def proofEqA (a : α) := Eq.refl a
#check proofEqA

variable (p q : Prop)

def h1 := p ∨ q
def h2 := Eq.refl p
def h3 (h₁ : p = q) := Eq.symm h₁
def h4 (h₁ : p ∧ q) := And.symm h₁

#check h3
#check h4


def p0 (a : α): Prop := a = a
def p1 (a: α) (b: α) : Prop := a = b
theorem h10 (h: p1 a b) : (b = a) := Eq.symm h


def add_zero_prop (n: Nat): Prop := n + 0 = n
-- theorem good (n : Nat) : Prop := Nat.add_zero n
theorem good (n : Nat) : (add_zero_prop n) := Nat.add_zero n

#check good
#check Nat.add_zero

end Equality


namespace AccessControl
-- Facts in your system
variable (User Resource : Type)

-- Policies/claims (propositions)
variable (CanRead : User → Resource → Prop)
variable (IsOwner : User → Resource → Prop)
variable (HasRoleAdmin : User → Prop)

-- Policy rule: owners can read
variable (owner_rule : ∀ u r, IsOwner u r → CanRead u r)

-- Policy rule: admins can read anything
variable (admin_rule : ∀ u r, HasRoleAdmin u → CanRead u r)

-- Concrete evidence in one request:
variable (alice bob : User)
variable (file1 file2 : Resource)
variable (hOwner1 : IsOwner alice file1)
variable (hAdmin : HasRoleAdmin bob)

#check hOwner1
#check owner_rule

-- Build proof that alice can read file1
def allow_read_owner : CanRead alice file1 :=
  owner_rule alice file1 hOwner1

-- Practice: use `admin_rule` with an admin proof.
def allow_read_admin : CanRead bob file1 :=
   admin_rule bob file1 hAdmin

-- Practice: combine the two policy paths with case analysis on `Or`.
theorem allow_read_from_owner_or_admin : CanRead alice file1 :=
  sorry

axiom owner_rule_a : ∀ (u: User) (r: Resource), IsOwner u r → CanRead u r
axiom admin_rule_a : ∀ (u: User) (r: Resource), HasRoleAdmin u → CanRead u r
#check owner_rule_a

theorem allow_read_from_owner_or_admin_any
    (u : User) (r : Resource)
    (h : IsOwner u r ∨ HasRoleAdmin u) :
    CanRead u r :=
    Or.elim h
      (fun howner => owner_rule_a User Resource CanRead IsOwner u r howner)
      (fun hrole => admin_rule_a User Resource CanRead HasRoleAdmin u r hrole)


-- Practice: if user can read every resource, then user can read this one.
theorem allow_read_of_global_access (hAll : ∀ r : Resource, CanRead alice r) : CanRead alice file1 :=
  hAll file1

end AccessControl


namespace NatPlayground

#check Nat.mul_add
#check Nat.add_mul
#check Nat.add_assoc
#check Eq.symm
#check Eq.subst

example (a b c : Nat) : a + (b + c) = a + b + c :=
  Eq.symm (Nat.add_assoc a b c)


example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
   have h1: (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
   have h2: (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
      (Nat.add_mul x y y) ▸ (Nat.add_mul x y x) ▸ h1
   have h3: x * x + y * x + (x * y + y * y) = x * x + y * x + x * y + y * y := Eq.symm (Nat.add_assoc (x * x + y * x) (x * y) (y * y))
  --  h3 ▸ h2
   Eq.subst h3 h2

end NatPlayground

#check Exists.intro
#print Exists.intro
#check Exists.elim

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

def IsEven (a : Nat) := ∃ b, a = 2 * b

#check Nat.mul_add
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  let ⟨ a1, ha ⟩ := h1
  let ⟨ b1, hb ⟩ := h2
  have h3 : a + b = 2 * (a1 + b1) := by
    rw [ha, hb]
    rw [Nat.mul_add]
  Exists.intro (a1 + b1) h3

namespace Exercise

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h1 => And.intro (fun t => (h1 t).left ) (fun t => (h1 t).right))
    (fun h2 => fun t => And.intro (h2.left t) (h2.right t))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 => fun h2 => fun t => h1 t (h2 t)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
   fun h1 => fun t =>
     Or.elim h1  -- a ∨ b → (a → c) → (b → c) → c
       (fun l1 => Or.inl (l1 t))
       (fun r1 => Or.inr (r1 t))

end Exercise
