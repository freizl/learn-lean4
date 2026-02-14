
namespace Equality

#check Eq.refl
#check Eq.symm

variable (p q : Prop)

def eq1 : Prop := p = p
def h : (eq1 p) := Eq.refl p

def p0 (a : α): Prop := a = a
def p1 (a: α) (b: α) : Prop := a = b
def h1 (h: p1 a b) : (b=a) := Eq.symm h
end Equality
