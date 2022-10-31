-- The bare minimum of type theory needed for my tactics
prelude
import tactic.localized

namespace hott

variables {α β : Type*}

-- Avoid name clash with `eq`
inductive Eq (a : α) : α → Type*
| refl [] : Eq a

localized "infix ` = `:50 := Eq" in hott
localized "notation `rfl` := Eq.refl _" in hott

namespace Eq
@[elab_as_eliminator]
def ind_on {C : Π (a b : α), a = b → Type*}
  {a b : α} (p : a = b)
  (c : Π (a : α), C a a rfl) :
  C a b p :=
@Eq.rec α a (C a) (c a) b p

-- Exercise 1.15: indiscernability of identicals follows from path induction
-- The justification for the name `transport` is in ch2
@[elab_as_eliminator]
def transport {a b : α} {P : α → Type*} (p : a = b) : P a → P b :=
Eq.ind_on p (λ a, @id (P a))

localized "postfix `∗`:51 := Eq.transport" in hott

def trans {a b c : α} : a = b → b = c → a = c :=
λ p, p∗ (@id (a = c))

localized "infix ` ⬝ `:51 := Eq.trans" in hott

@[elab_as_eliminator]
def ap (f : α → β) {a b : α} (p : a = b) : f a = f b :=
p∗ (refl (f a))

localized "infixr ` ▸ `:75 := Eq.ap" in hott

end Eq

end hott