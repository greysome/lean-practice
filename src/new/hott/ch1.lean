prelude  -- don't import `init` modules; we want to work from scratch

variables {α : Type*} {β : Type*} {γ : Type*}

-- Avoid name clash with `eq`
inductive Eq {α : Type*} (a : α) : α → Type*
| refl [] : Eq a

infix ` = `:50 := Eq
notation `rfl` := Eq.refl _

namespace Eq
#check @Eq.rec -- Based path induction

-- Path induction
def ind : Π (C : Π (a b : α), a = b → Type*),
  (Π (a : α), C a a rfl) → Π (a b : α) (p : a = b), C a b p :=
λ C c a b p, @Eq.rec α a (C a) (c a) b p

-- Based path induction, with rearranged arguments
def ind' : Π (a : α) (C : Π (b : α), a = b → Type*),
  C a rfl → Π (b : α) (p : a = b), C b p :=
λ a C c b p, @Eq.rec α a C c b p

-- Based path induction, proven using `ind`
def ind'₀ : Π (a : α) (C : Π (b : α), a = b → Type*),
  C a rfl → Π (b : α) (p : a = b), C b p :=
sorry

-- Exercise 1.15: indiscernability of identicals (in a sense the recursor)
-- follows from path induction
def rec' : Π (C : α → Type*) (a b : α) (p : a = b), C a → C b :=
λ C, ind (λ a b _, C a → C b) (λ _ c, c)


variables (a b c : α)

def symm : a = b → b = a :=
λ p, ind (λ a b _, b = a) (λ a, rfl) a b p

def trans : a = b → b = c → a = c :=
let C := λ (a b : α) (p : a = b), Π (c : α), b = c → a = c,
  f : Π (a b : α) (p : a = b) (c : α), b = c → a = c
    := ind C (λ _ _ p, p) in
λ p q, f a b p c q

end Eq



inductive prod (α : Type*) (β : Type*)
| mk : α → β → prod

namespace prod
-- The recursor, i.e. non-dependent eliminator
def rec' : (α → β → γ) → (prod α β → γ) := @prod.rec α β (λ _, γ)

-- The induction principle, i.e. dependent eliminator
-- This is just the Lean-given `prod.rec` with rearranged arguments
def ind : Π (C : prod α β → Type*),
  (Π (a : α) (b : β), C (mk a b)) → Π (x : prod α β), C x :=
λ C c, @prod.rec α β C c

def pr₁ : prod α β → α := rec' (λ a b, a)
def pr₂ : prod α β → β := rec' (λ a b, b)
def swap : prod α β → prod β α := rec' (λ a b, prod.mk b a)

-- The computation rules of pr₁, pr₂ and swap. That is, the
-- LHS is *definitionally equal* to the RHS.
example {a : α} {b : β} : pr₁ (mk a b) = a := rfl
example {a : α} {b : β} : pr₂ (mk a b) = b := rfl
example {a : α} {b : β} : swap (mk a b) = mk b a := rfl

-- The uniqueness principle
def uniq : Π (x : prod α β), x = mk x.pr₁ x.pr₂ :=
let C : prod α β → Type* := λ x, x = mk x.pr₁ x.pr₂ in
ind C (λ a b, rfl)

end prod



inductive sum (α : Type*) (β : Type*)
| inl : α → sum
| inr : β → sum

namespace sum
def rec' : (α → γ) → (β → γ) → (sum α β → γ) := @sum.rec α β (λ _, γ)

def ind : Π (C : sum α β → Type*),
  (Π (a : α), C (inl a)) → (Π (b : β), C (inr b)) → Π (x : sum α β), C x :=
λ C c, @sum.rec α β C c

end sum



inductive one
| star : one

namespace one
def rec' : α → one → α := @one.rec (λ _, α)

def ind : Π (C : one → Type*), C star → Π (x : one), C x := @one.rec

def uniq : Π (x : one), x = star :=
let C : one → Type* := λ x, x = star in
ind C rfl

end one



inductive two
| zero : two
| one : two

namespace two
def rec' : α → α → two → α := @two.rec (λ _, α)

def ind : Π (C : two → Type*), C zero → C one → Π (x : two), C x := @two.rec

def uniq : Π (x : two), sum (x = zero) (x = one) :=
let C : two → Type* := λ x, sum (x = zero) (x = one) in
ind C (sum.inl rfl) (sum.inr rfl)

end two



inductive sigma {α : Type*} (f : α → Type*)
| mk : Π (a : α), f a → sigma

-- I just copy pasted this line, I have no idea how it works
notation `Σ` binders `, ` r:(scoped f, sigma f) := r

namespace sigma
-- TODO: recursor and inductor
end sigma



inductive nat
| zero : nat
| succ : nat → nat

notation `ℕ` := nat

namespace nat
def rec' : α → (ℕ → α → α) → ℕ → α := @nat.rec (λ _, α)

def ind : Π (C : ℕ → Type*), C zero →
  (Π (n : ℕ), C n → C (succ n)) → Π (n : ℕ), C n :=
@nat.rec

-- `add` is defined via recursion on the first argument
def add : ℕ → ℕ → ℕ := nat.rec' (λ n, n) (λ m f n, succ (f n))

infix ` + `:65 := add


variables (i j k : ℕ)

def add_assoc : (i + j) + k = i + (j + k) :=
sorry

end nat



-- Exercises
namespace ch1
def sum' (α : Type*) (β : Type*) : Type := Σ (x : two), two.rec' α β x
def prod' (α : Type*) (β : Type*) : Type := Π (x : two), two.rec' α β x

end ch1