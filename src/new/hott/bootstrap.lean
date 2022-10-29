-- The bare minimum of type theory needed for my tactics
prelude
import tactic.localized

namespace hott

variables {α : Type*}

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

end Eq

end hott