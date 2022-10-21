prelude  -- don't import `init` modules; we want to work from scratch

variables {α β γ δ : Type*}

def id {α : Type*} : α → α := λ a, a


-- Avoid name clash with `eq`
inductive Eq {α : Type*} (a : α) : α → Type*
| refl [] : Eq a

infix ` = `:50 := Eq
notation `rfl` := Eq.refl _

namespace Eq
#check @Eq.rec -- Based path induction

-- Path induction
def ind (C : Π (a b : α), a = b → Type*)
  (c : Π (a : α), C a a rfl) :
  Π (a b : α) (p : a = b), C a b p :=
λ a b p, @Eq.rec α a (C a) (c a) b p

-- Based path induction
def ind' (a : α)
  (C : Π (b : α), a = b → Type*)
  (c : C a rfl) :
  Π (b : α) (p : a = b), C b p :=
λ b p, @Eq.rec α a C c b p

-- Based path induction, proven using `ind`
def ind'₁ (a : α)
  (C : Π (b : α), a = b → Type*)
  (c : C a rfl) :
  Π (b : α) (p : a = b), C b p :=
let D : Π (a b : α), a = b → Type* :=
    λ a b p, Π (C : Π (z : α), a = z → Type*), C a rfl → C b p,
  d : Π (a : α), D a a rfl := λ x C, id,
  f : Π (a b : α) (p : a = b), D a b p := Eq.ind D d in
λ b p, f a b p C c

-- Exercise 1.15: indiscernability of identicals (in a sense the recursor)
-- follows from path induction
def rec' (P : α → Type*) :
  Π {a b : α} (p : a = b), P a → P b :=
let C := λ (a b : α) (p : a = b), P a → P b in
Eq.ind C (λ a c, c)

example {P : α → Type*} {a : α} : rec' P (Eq.refl a) = id := rfl

end Eq



inductive prod (α : Type*) (β : Type*)
| mk : α → β → prod

infixr ` × `:35 := prod

namespace prod
-- The recursor, i.e. non-dependent eliminator
def rec' : (α → β → γ) → α × β → γ := @prod.rec α β (λ _, γ)

-- The induction principle, i.e. dependent eliminator
-- This is just the Lean-given `prod.rec` with rearranged arguments
def ind (C : α × β → Type*)
  (c : Π (a : α) (b : β), C ⟨a, b⟩) :
  Π (x : α × β), C x :=
@prod.rec α β C c

def pr₁ : α × β → α := prod.rec' (λ a b, a)
def pr₂ : α × β → β := prod.rec' (λ a b, b)

-- The definitional equality satisfied by `rec`, or the computation rule.
-- That is to say, the LHS is *definitionally equal* to the RHS.
example {f : α → β → γ} {a : α} {b : β} : prod.rec' f ⟨a, b⟩ = f a b := rfl
example {a : α} {b : β} : pr₁ ⟨a, b⟩ = a := rfl
example {a : α} {b : β} : pr₂ ⟨a, b⟩ = b := rfl

-- The uniqueness principle
def uniq : Π (x : α × β), x = ⟨x.pr₁, x.pr₂⟩ :=
let C : α × β → Type* := λ x, x = ⟨x.pr₁, x.pr₂⟩ in
prod.ind C (λ a b, rfl)

end prod



inductive sigma {α : Type*} (f : α → Type*)
| mk : Π (a : α), f a → sigma

-- I just copy pasted this line, I have no idea how it works
notation `Σ` binders `, ` r:(scoped f, sigma f) := r

namespace sigma
variable {f : α → Type*}

def rec' : (Π (a : α), f a → β) → (Σ (a : α), f a) → β :=
@sigma.rec α f (λ _, β)

def ind (C : (Σ (a : α), f a) → Type*)
  (c : Π (a : α) (b : f a), C ⟨a, b⟩) :
  Π (p : Σ (a : α), f a), C p :=
@sigma.rec α f C c

def pr₁ : (Σ (a : α), f a) → α := sigma.rec' (λ a b, a)

def pr₂ : Π (x : Σ (a : α), f a), f x.pr₁ :=
let C := λ (x : Σ (a : α), f a), f x.pr₁ in
sigma.ind C (λ a b, b)

-- A naive type-theoretic formulation of the axiom of choice,
-- which is trivial in this case.
def fake_ac (R : α → β → Type*) (total : Π (a : α), Σ (b : β), R a b) :
  Σ (f : α → β), Π (a : α), R a (f a) :=
sigma.mk (λ a, pr₁ (total a)) (λ a, pr₂ (total a))

end sigma



inductive sum (α : Type*) (β : Type*)
| inl : α → sum
| inr : β → sum

infixr ` ⊕ `:34 := sum

namespace sum
def rec' : (α → γ) → (β → γ) → α ⊕ β → γ := @sum.rec α β (λ _, γ)

def ind (C : α ⊕ β → Type*) :
  (Π (a : α), C (inl a)) → (Π (b : β), C (inr b)) → Π (x : α ⊕ β), C x :=
λ c, @sum.rec α β C c

end sum



inductive empty : Type

namespace empty
def rec' : empty → α := empty.rec (λ _, α)

def ind (C : empty → Type*) : Π (x : empty), C x := empty.rec C

end empty



inductive unit
| star : unit

namespace unit
def rec' : α → unit → α := @unit.rec (λ _, α)

def ind : Π (C : unit → Type*), C star → Π (x : unit), C x := @unit.rec

def uniq : Π (x : unit), x = star :=
let C : unit → Type* := λ x, x = star in
unit.ind C rfl

end unit



inductive bool
| ff : bool
| tt : bool

namespace bool
def rec' : α → α → bool → α := @bool.rec (λ _, α)

def ind : Π (C : bool → Type*), C ff → C tt → Π (x : bool), C x := @bool.rec

def uniq : Π (x : bool), (x = ff) ⊕ (x = tt) :=
let C : bool → Type* := λ x, (x = ff) ⊕ (x = tt) in
bool.ind C (sum.inl rfl) (sum.inr rfl)

end bool



inductive nat
| zero : nat
| succ : nat → nat

notation `ℕ` := nat

namespace nat
def rec' : α → (ℕ → α → α) → ℕ → α := @nat.rec (λ _, α)

def ind : Π (C : ℕ → Type*), C zero →
  (Π (n : ℕ), C n → C (succ n)) → Π (n : ℕ), C n :=
@nat.rec

def double : ℕ → ℕ := nat.rec' zero (λ n y, succ (succ y)) 
def add : ℕ → ℕ → ℕ := nat.rec' id (λ m f n, succ (f n))
infix ` + `:65 := add

example : double (zero.succ.succ) = zero.succ.succ.succ.succ := rfl
example : add zero.succ zero.succ.succ = zero.succ.succ.succ := rfl

def le (n m : ℕ) := Σ k, k + n = m
def lt (n m : ℕ) := Σ (k : ℕ), k.succ + n = m  

infix ` < `:50 := lt
infix ` ≤ `:50 := le

end nat



-- Propositional reasoning, by encoding propositions as types
prefix `¬`:40 := λ a, a → empty

namespace prop
variables {A B : Type*} -- Think of these as representing propositions

example : ¬ A × ¬ B → ¬ (A ⊕ B) :=
λ h, sum.rec' h.pr₁ h.pr₂

example : ¬ (A ⊕ B) → ¬ A × ¬ B :=
λ h, ⟨λ a, h (sum.inl a),
  λ b, h (sum.inr b)⟩

variables {P Q : A → Type*}
example : (Π (a : A), P a × Q a) → (Π (a : A), P a) × (Π (a : A), Q a) :=
λ h, ⟨λ a, (h a).pr₁,
  λ a, (h a).pr₂⟩

end prop



-- Exercise 1.1
def comp (g : β → γ) (f : α → β) : α → γ := λ x, g (f x)
infix ` ∘ `:63 := comp
example {f : α → β} {g : β → γ} {h : γ → δ} : h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

-- Exercise 1.2
def prod.rec₁ : (α → β → γ) → α × β → γ := λ f x, f x.pr₁ x.pr₂
example {f : α → β → γ} {a : α} {b : β} : prod.rec₁ f ⟨a, b⟩ = f a b := rfl

variable {f : α → Type*}
def sigma.rec₁ : (Π (a : α), f a → β) → (Σ (a : α), f a) → β := λ g x, g x.pr₁ x.pr₂
example {g : Π (a : α), f a → β} {a : α} {b : f a} : sigma.rec₁ g ⟨a, b⟩ = g a b := rfl

-- Exercise 1.3
def Eq.symm {a b : α} : a = b → b = a :=
let P := λ x, x = a in
λ p, @Eq.rec' α P a b p rfl

def prod.ind₁ (C : α × β → Type*)
  (c : Π (a : α) (b : β), C ⟨a, b⟩) :
  Π (x : α × β), C x :=
λ x, Eq.rec' C x.uniq.symm (c x.pr₁ x.pr₂)

-- Full derivation:
-- prod.ind₁ C c ⟨a, b⟩
-- ≡ Eq.rec' C ⟨a, b⟩ ⟨a, b⟩ ⟨a, b⟩.uniq.symm (c a b)
-- ≡ Eq.rec' C ⟨a, b⟩ ⟨a, b⟩ rfl (c a b)
-- ≡ id (c a b)
-- ≡ (c a b)
example {C : α × β → Type*}{c : Π (a : α) (b : β), C ⟨a, b⟩}
  {a : α} {b : β} : prod.ind₁ C c ⟨a, b⟩ = c a b :=
rfl

def sigma.uniq : Π (x : Σ (a : α), f a), x = ⟨x.pr₁, x.pr₂⟩ :=
let C := λ (x : Σ (a : α), f a), x = ⟨x.pr₁, x.pr₂⟩ in
sigma.ind C (λ a b, rfl)

-- Basically the same proof as prod.ind₁ (the characters are exactly
-- the same even!)
def sigma.ind₁ (C : (Σ (a : α), f a) → Type*)
  (c : Π (a : α) (b : f a), C ⟨a, b⟩) :
  Π (x : Σ (a : α), f a), C x :=
λ x, Eq.rec' C x.uniq.symm (c x.pr₁ x.pr₂)

example {C : (Σ (a : α), f a) → Type*}
  {c : Π (a : α) (b : f a), C ⟨a, b⟩}
  {a : α} {b : f a} : sigma.ind₁ C c ⟨a, b⟩ = c a b :=
rfl

-- Exercise 1.4
def nat.iter : α → (α → α) → ℕ → α := λ a f, nat.rec' a (λ n y, f y)

example {a : α} {f : α → α} : nat.iter a f nat.zero = a := rfl
example {a : α} {f : α → α} {n : ℕ} : nat.iter a f n.succ = f (nat.iter a f n) := rfl

def G (f : ℕ → α → α) : ℕ × α → ℕ × α := λ y, ⟨y.pr₁.succ, f y.pr₁ y.pr₂⟩

-- Name comes from the `zip` function in Python.
-- The function is like zip(ℕ, nat.rec' a f).
def zip (a : α) (f : ℕ → α → α) : ℕ → ℕ × α :=
nat.iter ⟨nat.zero, a⟩ (G f)

def nat.rec₁ : α → (ℕ → α → α) → ℕ → α :=
λ a f n, (zip a f n).pr₂

-- Full derivation:
-- nat.rec₁ a f 0
-- ≡ (zip a f 0).pr₂
-- ≡ (nat.iter ⟨0, a⟩ (G f) 0).pr₂
-- ≡ ⟨0, a⟩.pr₂
-- ≡ a
example {a : α} {f : ℕ → α → α} : nat.rec₁ a f nat.zero = a := rfl

-- ProvinG the other computation rule of `nat.rec₁` requires some
-- intermediate results
def Eq.ap (f : α → β) {a b : α} (p : a = b) : f a = f b :=
let C := λ x, f a = f x in
@Eq.rec' α C _ _ p rfl

def Eq.trans {a b c : α} : a = b → b = c → a = c :=
let C := λ (x : α), x = c → a = c in
λ p, Eq.rec' C p id

-- This is NOT definitionally true, and it must be proven via induction.
-- Full derivation for the inductive step:
-- zip a f n.succ
-- ≡ nat.iter ⟨0, a⟩ G n.succ
-- ≡ G (nat.iter ⟨0, a⟩ G n)
-- = G ⟨n, nat.rec' a f n⟩  (this is the non-judGmental equality that needs to proven)
-- ≡ ⟨n.succ, f n (nat.rec' a f n)⟩
-- ≡ ⟨n.succ, nat.rec' a f n.succ⟩
def aux (a : α) (f : ℕ → α → α) (n : ℕ) : zip a f n = ⟨n, nat.rec' a f n⟩ :=
let C := λ n, zip a f n = ⟨n, nat.rec' a f n⟩ in
nat.ind C rfl (λ n h, Eq.ap (G f) h) n

-- Full derivation:
-- nat.rec₁ a f n.succ
-- ≡ (zip a f n.succ).pr₂
-- = nat.rec' a f n.succ  (essentially h₁)
-- ≡ f n (nat.rec' a f n)
-- = f n (zip a f n).pr₂  (h₂)
-- ≡ f n (nat.rec₁ a f n)
example {a : α} {f : ℕ → α → α} {n : ℕ} :
  nat.rec₁ a f n.succ = f n (nat.rec₁ a f n) :=
let h₁ : (zip a f n.succ).pr₂ = nat.rec' a f n.succ :=
  Eq.ap prod.pr₂ (aux a f n.succ),
h₂ : f n (nat.rec' a f n) = f n (zip a f n).pr₂ :=
  @Eq.ap (ℕ × α) α (λ x, f n x.pr₂) _ _ (aux a f n).symm in
Eq.trans h₁ h₂

-- Exercise 1.5
def sum₁ (α β : Type*) : Type* := Σ (x : bool), bool.rec' α β x

namespace sum₁
-- idk why α and β have to be explicitly listed as implicit
def ind {α β : Type*} (C : sum₁ α β → Type*)
  (c₁ : Π (a : α), C ⟨bool.ff, a⟩)
  (c₂ : Π (b : β), C ⟨bool.tt, b⟩) :
  Π (x : sum₁ α β), C x :=
sigma.ind C (
  let C' : bool → Type* := λ a, Π (b : bool.rec' α β a), C ⟨a, b⟩ in
  bool.ind C' c₁ c₂
)

-- Full derivation:
-- sum₁.ind C c₁ c₂ ⟨bool.ff, a⟩
-- ≡ sigma.ind C (bool.ind _ c₁ c₂) ⟨bool.ff, a⟩
-- ≡ bool.ind _ c₁ c₂ bool.ff a 
-- ≡ c₁ a
example {α β : Type*} {C : sum₁ α β → Type*}
  {c₁ : Π (a : α), C ⟨bool.ff, a⟩}
  {c₂ : Π (b : β), C ⟨bool.tt, b⟩}
  {a : α} :
sum₁.ind C c₁ c₂ ⟨bool.ff, a⟩ = c₁ a := rfl

example {α β : Type*} {C : sum₁ α β → Type*}
  {c₁ : Π (a : α), C ⟨bool.ff, a⟩}
  {c₂ : Π (b : β), C ⟨bool.tt, b⟩}
  {b : β} :
sum₁.ind C c₁ c₂ ⟨bool.tt, b⟩ = c₂ b := rfl

end sum₁

-- Exercise 1.9
def fin : ℕ → Type* := λ n, Σ m, m < n
def fmax : Π (n : ℕ), fin n.succ := λ n, ⟨n, ⟨nat.zero, rfl⟩⟩

-- Exercise 1.10
namespace nat
def ack : ℕ → ℕ → ℕ :=
  nat.rec' succ (λ _ f, nat.rec' (f zero.succ) (λ _ y, f y))

variables {m n : ℕ}
example : ack zero n = n.succ := rfl
example : ack m.succ zero = ack m zero.succ := rfl
example : ack m.succ n.succ = ack m (ack m.succ n) := rfl

end nat

-- Exercises 1.11-1.13
namespace prop
variables {A B : Type*}
example : ¬¬¬ A → ¬ A := λ (f : ¬¬ A → empty) a, f (λ g : ¬ A, g a)
example : A → B → A := λ a b, a
example : A → ¬¬ A := λ a (f : A → empty), f a
example : ¬ A ⊕ ¬ B → ¬ (A × B) :=
  λ p q, sum.rec' (λ hna : ¬ A, hna q.pr₁) (λ hnb : ¬ B, hnb q.pr₂) p
example : ¬¬ (A ⊕ ¬ A) :=
  λ (f : A ⊕ ¬ A → empty), f (sum.inr (λ A, f (sum.inl A)))

-- Exercise 1.15: see definition of `Eq.rec`

end prop