prelude
import .ch1

variables {α β γ δ : Type*}
variables {a b c d : α} {p : a = b} {q : b = c} {r : c = d}

namespace Eq
-- The computation rules associated with various proofs of
-- symmetry and transitivity of Eq
postfix `⁻¹`:100 := symm
example : (refl a)⁻¹  = rfl := rfl

infix ` ⬝ `:51 := trans
example : rfl ⬝ p = p := rfl

-- Two other proofs of transitivity with different computation rules
def trans₁ : a = b → b = c → a = c :=
λ p q, Eq.rec' (λ x, a = x) q p

def trans₂ : a = b → b = c → a = c :=
λ p, Eq.rec' (λ x, x = c → a = c) p
  (λ q, Eq.rec' (λ x, a = x) q rfl)

example : trans₁ p rfl = p := rfl
example : trans₂ (refl a) rfl = rfl := rfl

-- These fail:
-- example : trans₁ rfl p = p := rfl
-- example : trans₂ p rfl = p := rfl
-- example : trans₂ rfl p = p := rfl

def concat_rfl : p ⬝ rfl = p :=
let C : Π (a b : α), a = b → Type* := λ a b p, p ⬝ rfl = p in
Eq.ind C (λ a, (rfl : refl a ⬝ rfl = rfl)) a b p

-- See the example above
def rfl_concat : rfl ⬝ p = p := rfl

def inv_concat : p⁻¹ ⬝ p = rfl :=
let C : Π (a b : α), a = b → Type* := λ a b p, p⁻¹ ⬝ p = rfl in
Eq.ind C (λ a, (rfl : (refl a)⁻¹ ⬝ rfl = rfl)) a b p

def concat_inv : p ⬝ p⁻¹ = rfl :=
let C : Π (a b : α), a = b → Type* := λ a b p, p ⬝ p⁻¹ = rfl in
Eq.ind C (λ a, (rfl : (refl a) ⬝ rfl⁻¹ = rfl)) a b p

def inv_inv : p⁻¹⁻¹ = p :=
let C : Π (a b : α), a = b → Type* := λ a b p, p⁻¹⁻¹ = p in
Eq.ind C (λ a, (rfl : (refl a)⁻¹⁻¹ = rfl)) a b p

-- As with `Eq.trans`, one can perform induction three ways.
-- As usual I do induction on `p`, and in fact it's the most
-- convenient since the proof of the base case follows definitionally.
def concat_assoc : (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
let C : Π (a b : α), a = b → Type* := λ a b p,
  Π (c d : α) (q : b = c) (r : c = d), (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) in
Eq.ind C (λ a c d q r, (rfl : (rfl ⬝ q) ⬝ r = rfl ⬝ (q ⬝ r)))
  a b p c d q r


def pointed : Type* := Σ (α : Type*), α

def loop_space' : ℕ → pointed → pointed :=
nat.rec' id (λ _ Ωⁿ x, Ωⁿ ⟨x.pr₂ = x.pr₂, rfl⟩)

def loop_space : ℕ → α → Type* :=
λ n a, (loop_space' n ⟨α, a⟩).pr₁

prefix `Ω`:50 := loop_space
-- How to generalise this notation to all natural arguments?
prefix `Ω²`:50 := loop_space nat.zero.succ.succ

example : Ω² a = (refl a = rfl) := rfl

def eckmann_hilton {A B : Ω² a} : A ⬝ B = B ⬝ A := sorry

end Eq