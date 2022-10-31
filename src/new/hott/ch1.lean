prelude
import .my_tactics

namespace hott
open_locale hott

localized "notation f ` $ `:1 a:0 := f a" in hott

variables {α β γ δ : Type*}

def id : α → α := λ a, a

namespace Eq
-- Path induction
@[elab_as_eliminator]
def ind {C : Π (a b : α), a = b → Type*}
  (c : Π (a : α), C a a rfl) :
  Π {a b : α} (p : a = b), C a b p :=
λ a b p, @Eq.rec α a (C a) (c a) b p

-- Based path induction
@[elab_as_eliminator]
def ind_on' (a : α)
  {C : Π (b : α), a = b → Type*}
  {b : α} (p : a = b)
  (c : C a rfl) :
  C b p :=
@Eq.rec α a C c b p

-- Based path induction, proven using `ind`
def ind_on'₁ (a : α)
  {C : Π (b : α), a = b → Type*}
  {b : α} (p : a = b)
  (c : C a rfl) :
  C b p :=
let D : Π (a b : α), a = b → Type* :=
    λ a b p, Π (C : Π (z : α), a = z → Type*), C a rfl → C b p,
  d : Π (a : α), D a a rfl := λ x C, id,
  f : D a b p := Eq.ind_on p d in
f C c

example {P : α → Type*} {a : α} : @@transport P (refl a) = id := rfl
example {f : α → β} {a : α} : f ▸ refl a = refl (f a) := rfl

-- The following results were not proven in ch1 but they are needed
-- for some of the exercises
def symm {a b : α} : a = b → b = a :=
λ p, p∗ (refl a)

localized "postfix `⁻¹`:1034 := Eq.symm" in hott

end Eq


-- Names such as `refl`, `ap` and `transport` are so ubiquitous that
-- I choose to make them top-level names
open Eq

inductive prod (α : Type*) (β : Type*)
| mk : α → β → prod

localized "infixr ` × `:51 := prod" in hott

variables {x : γ}

namespace prod
-- The recursor, i.e. non-dependent eliminator
def rec' : (α → β → γ) → α × β → γ := @prod.rec α β (λ _, γ)

-- The induction principle, i.e. dependent eliminator
-- This is just the Lean-given `prod.rec` with rearranged arguments
@[elab_as_eliminator]
def ind {C : α × β → Type*}
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
@@prod.ind (λ x, x = ⟨x.pr₁, x.pr₂⟩) (λ a b, rfl)

end prod



inductive sigma {α : Type*} (f : α → Type*)
| mk : Π (a : α), f a → sigma

-- I just copy pasted this line, I have no idea how it works
localized "notation `Σ` binders `, ` r:(scoped f, sigma f) := r" in hott

namespace sigma
variable {f : α → Type*}

def rec' : (Π (a : α), f a → β) → (Σ (a : α), f a) → β :=
@sigma.rec α f (λ _, β)

@[elab_as_eliminator]
def ind {C : (Σ (a : α), f a) → Type*}
  (c : Π (a : α) (b : f a), C ⟨a, b⟩) :
  Π (p : Σ (a : α), f a), C p :=
@sigma.rec α f C c

def pr₁ : (Σ (a : α), f a) → α := sigma.rec' (λ a b, a)

def pr₂ : Π (x : Σ (a : α), f a), f x.pr₁ :=
@@sigma.ind f (λ (x : sigma f), f x.pr₁) (λ a b, b)

-- A naive type-theoretic formulation of the axiom of choice,
-- which is trivial in this case.
def fake_ac (R : α → β → Type*) (total : Π (a : α), Σ (b : β), R a b) :
  Σ (f : α → β), Π (a : α), R a (f a) :=
sigma.mk (λ a, pr₁ (total a)) (λ a, pr₂ (total a))

end sigma



inductive sum (α : Type*) (β : Type*)
| inl : α → sum
| inr : β → sum

localized "infixr ` ⊕ `:51 := sum" in hott

namespace sum
def rec' : (α → γ) → (β → γ) → α ⊕ β → γ := @sum.rec α β (λ _, γ)

@[elab_as_eliminator]
def ind {C : α ⊕ β → Type*} :
  (Π (a : α), C (inl a)) → (Π (b : β), C (inr b)) → Π (x : α ⊕ β), C x :=
λ c, @sum.rec α β C c

end sum



inductive empty : Type

namespace empty
def rec' : empty → α := empty.rec (λ _, α)

@[elab_as_eliminator]
def ind {C : empty → Type*} : Π (x : empty), C x := empty.rec C

end empty



inductive unit
| star : unit

namespace unit
def rec' : α → unit → α := @unit.rec (λ _, α)

@[elab_as_eliminator]
def ind : Π {C : unit → Type*}, C star → Π (x : unit), C x := @unit.rec

def uniq : Π (x : unit), x = star :=
@@unit.ind (λ x, x = star) rfl

end unit



inductive bool
| ff : bool
| tt : bool

namespace bool
def rec' : α → α → bool → α := @bool.rec (λ _, α)

@[elab_as_eliminator]
def ind : Π {C : bool → Type*}, C ff → C tt → Π (x : bool), C x := @bool.rec

def uniq : Π (x : bool), (x = ff) ⊕ (x = tt) :=
@@bool.ind (λ x, (x = ff) ⊕ (x = tt)) (sum.inl rfl) (sum.inr rfl)

end bool



inductive nat
| zero : nat
| succ : nat → nat

localized "notation `ℕ` := nat" in hott

namespace nat
def rec' : α → (ℕ → α → α) → ℕ → α := @nat.rec (λ _, α)

@[elab_as_eliminator]
def ind : Π {C : ℕ → Type*}, C zero →
  (Π (n : ℕ), C n → C (succ n)) → Π (n : ℕ), C n :=
@nat.rec

@[elab_as_eliminator]
def ind_on : Π {C : ℕ → Type*} (n : ℕ),
  C zero → (Π (n : ℕ), C n → C (succ n)) → C n :=
@nat.rec_on

def double : ℕ → ℕ := nat.rec' zero (λ n y, succ (succ y)) 
def add : ℕ → ℕ → ℕ := nat.rec' id (λ m f n, succ (f n))

example : double (zero.succ.succ) = zero.succ.succ.succ.succ := rfl
example : add zero.succ zero.succ.succ = zero.succ.succ.succ := rfl

def le (n m : ℕ) := Σ k, add k n = m
def lt (n m : ℕ) := Σ (k : ℕ), add k.succ n = m  

end nat

localized "infix ` + `:65 := nat.add" in hott
localized "infix ` < `:50 := nat.lt" in hott
localized "infix ` ≤ `:50 := nat.le" in hott


-- Propositional reasoning, by encoding propositions as types
localized "prefix `¬`:1034 := λ a, a → empty" in hott

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



open_locale hott

-- Exercise 1.1
def comp (g : β → γ) (f : α → β) : α → γ := λ x, g (f x)
localized "infix ` ∘ `:76 := comp" in hott
example {f : α → β} {g : β → γ} {h : γ → δ} : h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

-- Exercise 1.2
def prod.rec₁ : (α → β → γ) → α × β → γ := λ f x, f x.pr₁ x.pr₂
example {f : α → β → γ} {a : α} {b : β} : prod.rec₁ f ⟨a, b⟩ = f a b := rfl

variable {f : α → Type*}
def sigma.rec₁ : (Π (a : α), f a → β) → (Σ (a : α), f a) → β := λ g x, g x.pr₁ x.pr₂
example {g : Π (a : α), f a → β} {a : α} {b : f a} : sigma.rec₁ g ⟨a, b⟩ = g a b := rfl

-- Exercise 1.3
def prod.ind₁ {C : α × β → Type*}
  (c : Π (a : α) (b : β), C ⟨a, b⟩) :
  Π (x : α × β), C x :=
λ x, (x.uniq)⁻¹∗ (c x.pr₁ x.pr₂)

-- Full derivation:
-- prod.ind₁ c ⟨a, b⟩
-- ≡ (⟨a, b⟩.uniq)⁻¹∗ (c a b)
-- ≡ rfl∗ (c a b)
-- ≡ id (c a b)
-- ≡ (c a b)
example {C : α × β → Type*} {c : Π (a : α) (b : β), C ⟨a, b⟩}
  {a : α} {b : β} : prod.ind₁ c ⟨a, b⟩ = c a b :=
rfl

def sigma.uniq : Π (x : Σ (a : α), f a), x = ⟨x.pr₁, x.pr₂⟩ :=
let C := λ (x : Σ (a : α), f a), x = ⟨x.pr₁, x.pr₂⟩ in
@@sigma.ind f C (λ a b, rfl)

-- Basically the same proof as prod.ind₁ (the characters are exactly
-- the same even!)
def sigma.ind₁ {C : (Σ (a : α), f a) → Type*}
  (c : Π (a : α) (b : f a), C ⟨a, b⟩) :
  Π (x : Σ (a : α), f a), C x :=
λ x, (x.uniq)⁻¹∗ (c x.pr₁ x.pr₂)

example {C : (Σ (a : α), f a) → Type*}
  {c : Π (a : α) (b : f a), C ⟨a, b⟩}
  {a : α} {b : f a} : sigma.ind₁ c ⟨a, b⟩ = c a b :=
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

-- Proving the other computation rule of `nat.rec₁` requires some
-- intermediate results

-- This is NOT definitionally true, and it must be proven via induction.
-- Full derivation for the inductive step:
-- zip a f n.succ
-- ≡ nat.iter ⟨0, a⟩ G n.succ
-- ≡ G (nat.iter ⟨0, a⟩ G n)
-- = G ⟨n, nat.rec' a f n⟩  (this is the non-judgmental equality that needs to proven)
-- ≡ ⟨n.succ, f n (nat.rec' a f n)⟩
-- ≡ ⟨n.succ, nat.rec' a f n.succ⟩
def aux (a : α) (f : ℕ → α → α) (n : ℕ) : zip a f n = ⟨n, nat.rec' a f n⟩ :=
nat.ind_on n rfl (λ n h, G f ▸ h)

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
  prod.pr₂ ▸ (aux a f n.succ),
h₂ : f n (nat.rec' a f n) = f n (zip a f n).pr₂ :=
  (λ (x : ℕ × α), f n x.pr₂) ▸ (aux a f n)⁻¹ in
h₁ ⬝ h₂

-- Exercise 1.5
-- Note α and β are forced to be in the same universe,
-- since α and β must have the same type in the call to `bool.rec'`.
-- This makes the definition somewhat weaker than the original.
def sum₁ (α β : Type*) : Type* := Σ (x : bool), bool.rec' α β x

namespace sum₁
def ind {α β : Type*} {C : sum₁ α β → Type*}
  (c₁ : Π (a : α), C ⟨bool.ff, a⟩)
  (c₂ : Π (b : β), C ⟨bool.tt, b⟩) :
  Π (x : sum₁ α β), C x :=
sigma.ind (
  let C' := λ a, Π (b : bool.rec' α β a), C ⟨a, b⟩ in
  @@bool.ind C' c₁ c₂
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
sum₁.ind c₁ c₂ ⟨bool.ff, a⟩ = c₁ a := rfl

example {α β : Type*} {C : sum₁ α β → Type*}
  {c₁ : Π (a : α), C ⟨bool.ff, a⟩}
  {c₂ : Π (b : β), C ⟨bool.tt, b⟩}
  {b : β} :
sum₁.ind c₁ c₂ ⟨bool.tt, b⟩ = c₂ b := rfl

end sum₁



-- Exercise 1.8, 1.16
namespace nat
def mul : ℕ → ℕ → ℕ := nat.rec' (λ _, zero) (λ _ f n, add n (f n))
-- Following the convention of `add` and `mul`,
-- I define `exp m n` so that `exp 0 n = 1`. Thus `exp m n = n ^ m`.
def exp : ℕ → ℕ → ℕ := nat.rec' (λ _, zero.succ) (λ _ f n, mul n (f n))

end nat

localized "infix ` * `:66 := nat.mul" in hott

namespace nat
example {n : ℕ} : mul zero n = zero := rfl
example {n m : ℕ} : mul m.succ n = add n (mul m n) := rfl
example {n : ℕ} : exp zero n = zero.succ := rfl
example {n m : ℕ} : exp m.succ n = mul n (exp m n) := rfl

-- The rest is proving that ℕ is a commutative semiring
variables (k n m : ℕ)

-- I have no idea why the hell removing the @ breaks the proof
-- Full derivation of the inductive step left as an exercise to the reader
def add_assoc : (k + n) + m = k + (n + m) :=
nat.ind_on k rfl (λ k h, succ ▸ h)

def add_zero : n + zero = n :=
nat.ind_on n rfl (λ k h, succ ▸ h)

-- Recall `zero_add : zero + n = n` is a definitional equality.

-- The proof is not trivial; it requires double induction
def add_comm : n + m = m + n :=
begin
  revert m,
  induction n with n hn,
  { exact λ m, (add_zero _)⁻¹ },
  { intro m, induction m with m hm,
    { exact (add_zero _) },
    hrw (succ ▸ hn m.succ),
    hrw (succ ∘ succ ▸ (hn m)⁻¹),
    hrw (succ ▸ hm) }
end

def one_mul : zero.succ * k = k := add_zero k

def mul_one : k * zero.succ = k :=
nat.ind_on k rfl (λ k h, add zero.succ ▸ h)

def mul_zero : k * zero = zero :=
nat.ind_on k rfl (λ k h, h)

-- `zero_mul : zero * k = zero` holds definitionally

def mul_add : k * (n + m) = k * n + k * m :=
begin
  induction k with k hk, spamrfl,
  hrw (add (n + m) ▸ hk),
  hrw (add_assoc n m _),
  hrw (add n ▸ (add_assoc _ _ _)⁻¹),
  hrw ((λ x, n + (x + k * m)) ▸ add_comm m (k * n)),
  hrw (add n ▸ add_assoc (k * n) m (k * m)),
  hrw (add_assoc n (k * n) _)⁻¹
end

def add_mul : (n + m) * k = n * k + m * k :=
begin
  induction n with n hn, spamrfl,
  hrw (add k ▸ hn),
  hrw (add_assoc _ _ _)⁻¹
end

def mul_assoc : (k * n) * m = k * (n * m) :=
begin
  induction k with k hk, spamrfl,
  hrw (add_mul _ _ _),
  hrw (add (n * m) ▸ hk)
end

def mul_comm : n * m = m * n :=
begin
  induction n with n hn,
    exact (mul_zero m)⁻¹,
  hrw (add_comm _ _),
  hrw ((λ x, x + m) ▸ hn),
  hrw (add (m * n) ▸ (mul_one m)⁻¹),
  hrw (mul_add _ _ _)⁻¹,
  hrw (mul m ▸ add_comm _ _)
end

end nat

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

end hott