def hello := "world"

def hfun (f: α → β → χ) (g: (β → α) → β) (a:α) :=
  f a (g (λ _b => a))
