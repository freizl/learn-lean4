
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
