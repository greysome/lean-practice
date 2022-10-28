prelude
import .ch1

variables {α β γ δ : Type*}
variables {a b c d : α} (p : a = b) (q : b = c) (r : c = d)

namespace Eq
-- The computation rules associated with various proofs of
-- symmetry and transitivity of Eq
postfix `⁻¹`:1034 := symm
example : (refl a)⁻¹  = rfl := rfl

infix ` ⬝ `:51 := trans
example : rfl ⬝ p = p := rfl

postfix `∗ `:51 := transport

-- Two other proofs of transitivity with different computation rules
def trans₁ : a = b → b = c → a = c :=
λ p q, q∗ p

def trans₂ : a = b → b = c → a = c :=
λ p, p∗ (λ q, q∗ rfl)

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


-- Preliminaries for proving Eckmann-Hilton
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

def whisker_right {p q : a = b} (A : p = q) (r : b = c) :
  p ⬝ r = q ⬝ r :=
Eq.ind (λ b a p q A, p.concat_rfl ⬝ A ⬝ q.concat_rfl⁻¹) b c r a p q A

def whisker_left {r s : b = c} (q : a = b) (B : r = s) :
  q ⬝ r = q ⬝ s :=
Eq.ind (λ a c r s B, r.rfl_concat ⬝ B ⬝ s.rfl_concat⁻¹) a b q c r s B

infix ` ⬝r `:50 := whisker_right
infix ` ⬝l `:50 := whisker_left

-- One could also define `whisker_right` and `whisker_left` via
-- transport, but we lose our nice judgmental equality:
example {p q : a = b} (A : p = q) (r : b = c) :
  p ⬝ r = q ⬝ r :=
A∗ rfl

example {r s : b = c} (q : a = b) (B : r = s) :
  q ⬝ r = q ⬝ s :=
B∗ rfl

def cancel_left {r s : b = c} (q : a = b) (A : q ⬝ r = q ⬝ s) :
  r = s :=
Eq.ind (λ a c r s A, A) a b q c r s A

def cancel_right {p q : a = b} (r : b = c) (A : p ⬝ r = q ⬝ r) :
  p = q :=
Eq.ind (λ b a p q A, p.concat_rfl⁻¹ ⬝ A ⬝ q.concat_rfl) b c r a p q A



variables (f : α → β) (g : β → γ)

def ap_concat : f ▸ (p ⬝ q) = f ▸ p ⬝ f ▸ q :=
Eq.ind (λ a c q, rfl) a b p c q

def ap_inv : f ▸ p⁻¹ = (f ▸ p)⁻¹ :=
Eq.ind (λ a, rfl) a b p

def ap_ap : g ▸ f ▸ p = (g ∘ f) ▸ p :=
Eq.ind (λ a, rfl) a b p

def ap_id : id ▸ p = p :=
Eq.ind (λ a, rfl) a b p



variables {P : α → Type*}

def lift (u : P a) : (⟨a, u⟩ : sigma P) = ⟨b, p∗ u⟩ :=
Eq.ind (λ a u, rfl) a b p u

def project {u v : sigma P} (q : u = v) : u.pr₁ = v.pr₁ :=
Eq.ind (λ u, rfl) u v q

example {p : a = b} {u : P a} : project (lift p u) = p :=
Eq.ind (λ a u, rfl) a b p u

def apd (f : Π (x : α), P x) (p : a = b) : (p∗ (f a) : P b) = f b :=
Eq.ind (λ a, rfl) a b p

def transportconst (p : a = b) (x : β) : (p∗ x : β) = x :=
Eq.ind (λ a, rfl) a b p

def apd_eq_concat_ap (f : α → β) (p : a = b) :
  apd f p = transportconst p (f a) ⬝ (f ▸ p) :=
Eq.ind (λ a, rfl) a b p

def transport_concat (p : a = b) (q : b = c) (u : P a) :
  (q∗ (p∗ u) : P c) = (p⬝q)∗ u :=
Eq.ind (λ a q u, rfl) a b p q u

def transport_over {P Q : α → Type*} (f : Π (a : α), P a → Q a) (p : a = b) (u : P a) :
  (p∗ (f a u) : Q b) = f b (p∗ u) :=
Eq.ind (λ a u, rfl) a b p u


namespace eckmann_hilton
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
  h₃ : A' ⬝ B' = A' ⬝ B := (λ x, A' ⬝ x) ▸ h₂,
  h₄ : A' ⬝ B = A ⬝ B := (λ x, x ⬝ B) ▸ h₁ in
h₃ ⬝ h₄

def star₁_eq_concat : star₁ A B = B ⬝ A :=
let A' := (concat_rfl rfl) ⬝ A ⬝ (concat_rfl rfl)⁻¹,
  B' := (concat_rfl rfl) ⬝ B ⬝ (concat_rfl rfl)⁻¹,
  h₁ : A' = A := concat_rfl A,
  h₂ : B' = B := concat_rfl B,
  h₃ : B' ⬝ A' = B ⬝ A' := (λ x, x ⬝ A') ▸ h₂,
  h₄ : B ⬝ A' = B ⬝ A := (λ x, B ⬝ x) ▸ h₁ in
h₃ ⬝ h₄

def star_eq_star₁ : star A B = star₁ A B :=
let C := λ (p q : a = a) (A : p = q), star A B = star₁ A B in
@@Eq.ind C (λ (p : a = a),
  let C' := λ (r s : a = a) (B : r = s), star (refl p) B = star₁ (refl p) B in
  @@Eq.ind C' (λ (r : a = a), _) rfl rfl B
) rfl rfl A

def main : A ⬝ B = B ⬝ A :=
(star_eq_concat A B)⁻¹ ⬝ (star_eq_star₁ A B) ⬝ (star₁_eq_concat A B)

end eckmann_hilton
end Eq



open Eq

namespace homotopy
section
variables {P : α → Type*} (f g h : Π (a : α), P a)

def homotopy : Type* := Π (a : α), f a = g a

infix ` ∼ `:50 := homotopy

def refl : f ∼ f := λ a, rfl

def symm : f ∼ g → g ∼ f := λ H a, (H a)⁻¹

def trans : f ∼ g → g ∼ h → f ∼ h := λ H₁ H₂ a, (H₁ a) ⬝ (H₂ a)

def natural {f g : α → β} (H : f ∼ g) (p : a = b) :
  H a ⬝ g ▸ p = f ▸ p ⬝ H b :=
Eq.ind (λ a, concat_rfl _) a b p

def natural₁ {f : α → α} (H : f ∼ id) (a : α) :
  H (f a) = f ▸ H a :=
cancel_right (H a)
  (whisker_left _ (ap_id _)⁻¹ ⬝ natural H (H a))


-- Quasi-equivalence
structure qequiv (α β : Type*) :=
(f : α → β)
(g : β → α)
(A : f ∘ g ∼ @id β)
(B : g ∘ f ∼ @id α)

infix ` ≃q `:49 := qequiv

def qequiv.refl : α ≃q α :=
{ f := id, g := id, A := λ b, rfl, B := λ a, rfl }

-- `def` instead of `instance` use to prevent typeclass loops
def qequiv.symm [ψ : α ≃q β] : β ≃q α :=
⟨ψ.g, ψ.f, ψ.B, ψ.A⟩

def qequiv.trans [ψ : α ≃q β] [ψ' : β ≃q γ] : α ≃q γ :=
{ f := ψ'.f ∘ ψ.f,
  g := ψ.g ∘ ψ'.g,
  A := λ c, (ψ'.f ▸ ψ.A (ψ'.g c)) ⬝ ψ'.A c,
  B := λ a, (ψ.g ▸ ψ'.B (ψ.f a)) ⬝ ψ.B a }

def _root_.Eq.trans.qequiv (p : a = b) (c : α) :
  b = c ≃q a = c :=
{ f := λ (q : b = c), p ⬝ q,
  g := λ (q : a = c), p⁻¹ ⬝ q,
  A := λ r, (concat_assoc _ _ _)⁻¹ ⬝ (whisker_right (concat_inv _) r),
  B := λ r, (concat_assoc _ _ _)⁻¹ ⬝ (whisker_right (inv_concat _) r)}

def _root_.Eq.trans.qequiv₁ (p : a = b) (c : α) :
  c = a ≃q c = b :=
{ f := λ (q : c = a), q ⬝ p,
  g := λ (q : c = b), q ⬝ p⁻¹,
  A := λ r, (concat_assoc _ _ _) ⬝ (whisker_left r (inv_concat _)) ⬝ concat_rfl _,
  B := λ r, (concat_assoc _ _ _) ⬝ (whisker_left r (concat_inv _)) ⬝ concat_rfl _ }

def _root_.Eq.transport.qequiv {P : α → Type*} (p : a = b) :
  P a ≃q P b :=
{ f := p∗, g := p⁻¹∗,
  A := λ u,
    transport_concat p⁻¹ p u ⬝
      (λ q, @@transport P q u) ▸ inv_concat p,
  B := λ u,
    transport_concat p p⁻¹ u ⬝
      (λ q, @@transport P q u) ▸ concat_inv p }

end


structure equiv (α β : Type*) :=
(f : α → β)
(g h : β → α)
(A : f ∘ g ∼ @id β)
(B : h ∘ f ∼ @id α)

infix ` ≃ `:49 := equiv

namespace equiv
def from_qequiv [ψ : α ≃q β] : α ≃ β :=
⟨ψ.f, ψ.g, ψ.g, ψ.A, ψ.B⟩

def to_qequiv [φ : α ≃ β] : α ≃q β :=
⟨φ.f, φ.g, φ.A,
  λ a, (φ.B $ (φ.g ∘ φ.f) a)⁻¹ ⬝
    φ.h ▸ φ.A (φ.f a) ⬝
    φ.B a⟩

-- To be proved in ch4
def uniq (φ : α ≃ β) (φ' : α ≃ β) : φ.f = φ'.f := sorry

def refl {α : Type*} : α ≃ α :=
@@from_qequiv qequiv.refl

def symm {α : Type*} [φ : α ≃ β] : β ≃ α :=
@@from_qequiv $ @@qequiv.symm $ @@to_qequiv φ

def trans {α : Type*} [φ : α ≃ β] [φ' : β ≃ γ] : α ≃ γ :=
@@from_qequiv $ @@qequiv.trans (@@to_qequiv φ) (@@to_qequiv φ')

end equiv
end homotopy