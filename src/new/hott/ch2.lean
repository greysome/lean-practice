prelude
import .ch1

variables {α β γ δ : Type*}
variables {a b c d : α} (p : a = b) (q : b = c) (r : c = d)

namespace Eq
-- The computation rules associated with various proofs of
-- symmetry and transitivity of Eq
postfix `⁻¹`:100 := symm
example : (refl a)⁻¹  = rfl := rfl

infix ` ⬝ `:51 := trans
example : rfl ⬝ p = p := rfl

-- Two other proofs of transitivity with different computation rules
def trans₁ : a = b → b = c → a = c :=
λ p q, transport q p

def trans₂ : a = b → b = c → a = c :=
λ p, transport p (λ q, transport q rfl)

example : trans₁ p rfl = p := rfl
example : trans₂ (refl a) rfl = rfl := rfl

-- These fail:
-- example : trans₁ rfl p = p := rfl
-- example : trans₂ p rfl = p := rfl
-- example : trans₂ rfl p = p := rfl

def concat_rfl : p ⬝ rfl = p :=
Eq.ind (λ a, (rfl : refl a ⬝ rfl = rfl)) a b p

-- See the example above
def rfl_concat : rfl ⬝ p = p := rfl

def inv_concat : p⁻¹ ⬝ p = rfl :=
let C : Π (a b : α), a = b → Type* := λ a b p, p⁻¹ ⬝ p = rfl in
Eq.ind (λ a, (rfl : (refl a)⁻¹ ⬝ rfl = rfl)) a b p

def concat_inv : p ⬝ p⁻¹ = rfl :=
Eq.ind (λ a, (rfl : (refl a) ⬝ rfl⁻¹ = rfl)) a b p

def inv_inv : p⁻¹⁻¹ = p :=
let C : Π (a b : α), a = b → Type* := λ a b p, p⁻¹⁻¹ = p in
Eq.ind (λ a, (rfl : (refl a)⁻¹⁻¹ = rfl)) a b p

-- As with `Eq.trans`, one can perform induction three ways.
-- As usual I do induction on `p`, and in fact it's the most
-- convenient since the proof of the base case follows definitionally.
def concat_assoc : (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
Eq.ind (λ a c d q r, (rfl : (rfl ⬝ q) ⬝ r = rfl ⬝ (q ⬝ r)))
  a b p c d q r

variables (f : α → β) (g : β → γ)

def ap_concat : ap f (p ⬝ q) = (ap f p) ⬝ (ap f q) :=
Eq.ind (λ a c q, rfl) a b p c q

def ap_inv : ap f (p⁻¹) = (ap f p)⁻¹ :=
Eq.ind (λ a, rfl) a b p

def ap_ap : ap g (ap f p) = ap (g ∘ f) p :=
Eq.ind (λ a, rfl) a b p

def ap_id : ap id p = p :=
Eq.ind (λ a, rfl) a b p

end Eq



open Eq

namespace homotopy
def pointed : Type* := Σ (α : Type*), α

def loop_space' : ℕ → pointed → pointed :=
nat.rec' id (λ _ Ωⁿ x, Ωⁿ ⟨x.pr₂ = x.pr₂, rfl⟩)

def loop_space : ℕ → α → Type* :=
λ n a, (loop_space' n ⟨α, a⟩).pr₁

prefix `Ω`:50 := loop_space
-- How to generalise this notation to all natural arguments?
prefix `Ω²`:50 := loop_space nat.zero.succ.succ

-- Sanity check that the definition of `loop_space` is correct
example : Ω² a = (refl a = rfl) := rfl

-- The entire following section is devoted to proving Eckmann-Hilton
def whisker_right {p q : a = b} (A : p = q) (r : b = c) :
  p ⬝ r = q ⬝ r :=
Eq.ind (λ b a p q A, p.concat_rfl ⬝ A ⬝ q.concat_rfl⁻¹) b c r a p q A

def whisker_left {r s : b = c} (q : a = b) (B : r = s) :
  q ⬝ r = q ⬝ s :=
Eq.ind (λ a c r s B, r.rfl_concat ⬝ B ⬝ s.rfl_concat⁻¹) a b q c r s B

infix ` ⬝r `:50 := whisker_right
infix ` ⬝l `:50 := whisker_left

-- One could also define `whisker_right` and `whisker_left` as follows
-- (namely induction on `A`), but we lose our nice judgmental equality:
example {p q : a = b} (A : p = q) (r : b = c) :
  p ⬝ r = q ⬝ r :=
Eq.transport A rfl

example {r s : b = c} (q : a = b) (B : r = s) :
  q ⬝ r = q ⬝ s :=
Eq.transport B rfl

def star {p q : a = b} {r s : b = c} (A : p = q) (B : r = s) :
  p ⬝ r = q ⬝ s :=
(A ⬝r r) ⬝ (q ⬝l B)

def star₁ {p q : a = b} {r s : b = c} (A : p = q) (B : r = s) :
  p ⬝ r = q ⬝ s :=
(p ⬝l B) ⬝ (A ⬝r s)

variables (A B : Ω² a)

-- This should really be done via tactics... 
def star_eq_concat : star A B = A ⬝ B :=
let A' := (concat_rfl rfl) ⬝ A ⬝ (concat_rfl rfl)⁻¹,
  B' := (concat_rfl rfl) ⬝ B ⬝ (concat_rfl rfl)⁻¹,
  h₁ : A' = A := concat_rfl A,
  h₂ : B' = B := concat_rfl B,
  h₃ : A' ⬝ B' = A' ⬝ B := ap (λ x, A' ⬝ x) h₂,
  h₄ : A' ⬝ B = A ⬝ B := ap (λ x, x ⬝ B) h₁ in
h₃ ⬝ h₄

def star₁_eq_concat : star₁ A B = B ⬝ A :=
let A' := (concat_rfl rfl) ⬝ A ⬝ (concat_rfl rfl)⁻¹,
  B' := (concat_rfl rfl) ⬝ B ⬝ (concat_rfl rfl)⁻¹,
  h₁ : A' = A := concat_rfl A,
  h₂ : B' = B := concat_rfl B,
  h₃ : B' ⬝ A' = B ⬝ A' := ap (λ x, x ⬝ A') h₂,
  h₄ : B ⬝ A' = B ⬝ A := ap (λ x, B ⬝ x) h₁ in
h₃ ⬝ h₄

def star_eq_star₁ : star A B = star₁ A B :=
let C := λ (p q : a = a) (A : p = q), star A B = star₁ A B in
@@Eq.ind C (λ (p : a = a),
  let C' := λ (r s : a = a) (B : r = s), star (refl p) B = star₁ (refl p) B in
  @@Eq.ind C' (λ (r : a = a), _) rfl rfl B
) rfl rfl A

def eckmann_hilton : A ⬝ B = B ⬝ A :=
(star_eq_concat A B).symm ⬝ (star_eq_star₁ A B) ⬝ (star₁_eq_concat A B)

end homotopy