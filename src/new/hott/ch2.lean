prelude
import .ch1

namespace hott
open_locale hott

variables {α β γ δ : Type*}
variables {a b c d : α} (p : a = b) (q : b = c) (r : c = d)

namespace Eq
-- The computation rules associated with various proofs of
-- symmetry and transitivity of Eq
example : (refl a)⁻¹ = rfl := rfl

example : rfl ⬝ p = p := rfl

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
Eq.ind_on p (λ a, (rfl : refl a ⬝ rfl = rfl))

-- See the example above
def rfl_concat : rfl ⬝ p = p := rfl

def inv_concat : p⁻¹ ⬝ p = rfl :=
Eq.ind_on p (λ a, (rfl : (refl a)⁻¹ ⬝ rfl = rfl))

def concat_inv : p ⬝ p⁻¹ = rfl :=
Eq.ind_on p (λ a, (rfl : (refl a) ⬝ rfl⁻¹ = rfl))

def inv_inv : p⁻¹⁻¹ = p :=
Eq.ind_on p (λ a, (rfl : (refl a)⁻¹⁻¹ = rfl))

-- As with `Eq.trans`, one can perform induction three ways.
-- As usual I do induction on `p`, and in fact it's the most
-- convenient since the proof of the base case follows definitionally.
def concat_assoc : (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
Eq.ind_on p (λ a c d q r, (rfl : (rfl ⬝ q) ⬝ r = rfl ⬝ (q ⬝ r)))
  c d q r



def whisker_right {p q : a = b} (A : p = q) (r : b = c) :
  p ⬝ r = q ⬝ r :=
Eq.ind_on r (λ b a p q A, p.concat_rfl ⬝ A ⬝ q.concat_rfl⁻¹) a p q A

def whisker_left {r s : b = c} (q : a = b) (B : r = s) :
  q ⬝ r = q ⬝ s :=
Eq.ind_on q (λ a c r s B, r.rfl_concat ⬝ B ⬝ s.rfl_concat⁻¹) c r s B

localized "infix ` ⬝r `:50 := whisker_right" in hott
localized "infix ` ⬝l `:50 := whisker_left" in hott

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
Eq.ind_on q (λ a c r s A, A) c r s A

def cancel_right {p q : a = b} (r : b = c) (A : p ⬝ r = q ⬝ r) :
  p = q :=
Eq.ind_on r (λ b a p q A, p.concat_rfl⁻¹ ⬝ A ⬝ q.concat_rfl) a p q A



variables (f : α → β) (g : β → γ)

def ap_concat : f ▸ (p ⬝ q) = f ▸ p ⬝ f ▸ q :=
Eq.ind_on p (λ a c q, rfl) c q

def ap_inv : f ▸ p⁻¹ = (f ▸ p)⁻¹ :=
Eq.ind_on p (λ a, rfl)

def ap_ap : g ▸ f ▸ p = (g ∘ f) ▸ p :=
Eq.ind_on p (λ a, rfl)

def ap_id : id ▸ p = p :=
Eq.ind_on p (λ a, rfl)



variables {P : α → Type*}

def lift (u : P a) : (⟨a, u⟩ : sigma P) = ⟨b, p∗ u⟩ :=
Eq.ind_on p (λ a u, rfl) u

def project {u v : sigma P} (q : u = v) : u.pr₁ = v.pr₁ :=
Eq.ind_on q (λ u, rfl)

example {p : a = b} {u : P a} : project (lift p u) = p :=
Eq.ind_on p (λ a u, rfl) u

def apd (f : Π (x : α), P x) (p : a = b) : (p∗ (f a) : P b) = f b :=
Eq.ind_on p (λ a, rfl)

def transportconst (p : a = b) (x : β) : (p∗ x : β) = x :=
Eq.ind_on p (λ a, rfl)

def apd_eq_concat_ap (f : α → β) (p : a = b) :
  apd f p = transportconst p (f a) ⬝ (f ▸ p) :=
Eq.ind_on p (λ a, rfl)

def transport_concat (p : a = b) (q : b = c) (u : P a) :
  (q∗ (p∗ u) : P c) = (p⬝q)∗ u :=
Eq.ind_on p (λ a q u, rfl) q u

def transport_over {P Q : α → Type*} (f : Π (a : α), P a → Q a) (p : a = b) (u : P a) :
  (p∗ (f a u) : Q b) = f b (p∗ u) :=
Eq.ind_on p (λ a u, rfl) u


namespace eckmann_hilton

-- Preliminaries for proving Eckmann-Hilton
def pointed : Type* := Σ (α : Type*), α

def loop_space' : ℕ → pointed → pointed :=
nat.rec' id (λ _ Ωⁿ x, Ωⁿ ⟨x.pr₂ = x.pr₂, rfl⟩)

def loop_space : ℕ → α → Type* :=
λ n a, (loop_space' n ⟨α, a⟩).pr₁

localized "prefix `Ω `:50 := eckmann_hilton.loop_space" in hott
-- How to generalise this local notation to all natural arguments?
localized "prefix `Ω²`:50 := eckmann_hilton.loop_space nat.zero.succ.succ" in hott

-- Sanity check that the definition of `loop_space` is correct
example : Ω² a = (refl a = rfl) := rfl



def star {p q : a = b} {r s : b = c} (A : p = q) (B : r = s) :
  p ⬝ r = q ⬝ s :=
(A ⬝r r) ⬝ (q ⬝l B)

def star₁ {p q : a = b} {r s : b = c} (A : p = q) (B : r = s) :
  p ⬝ r = q ⬝ s :=
(p ⬝l B) ⬝ (A ⬝r s)


def star_eq_concat (A B : Ω² a) :
  star A B = A ⬝ B :=
begin
  let A' := (concat_rfl rfl) ⬝ A ⬝ (concat_rfl rfl)⁻¹,
  let B' := (concat_rfl rfl) ⬝ B ⬝ (concat_rfl rfl)⁻¹,
  hrw ((λ x, A' ⬝ x) ▸ concat_rfl B),
  hrw ((λ x, x ⬝ B) ▸ concat_rfl A)
end

def star₁_eq_concat (A B : Ω² a) :
  star₁ A B = B ⬝ A :=
begin
  let A' := (concat_rfl rfl) ⬝ A ⬝ (concat_rfl rfl)⁻¹,
  let B' := (concat_rfl rfl) ⬝ B ⬝ (concat_rfl rfl)⁻¹,
  hrw ((λ x, x ⬝ A') ▸ concat_rfl B),
  hrw ((λ x, B ⬝ x) ▸ concat_rfl A)
end

def star_eq_star₁ {p q : a = b} {r s : b = c} (A : p = q) (B : r = s) :
  star A B = star₁ A B :=
begin
  pinduction p q A,
  pinduction r s B,
  intros r₁,
  pinduction b c r₁,
  intros b₁ p₁,
  pinduction a b₁ p₁,
  spamrfl
end

def main (A B : Ω² a) : A ⬝ B = B ⬝ A :=
(star_eq_concat A B)⁻¹ ⬝ (star_eq_star₁ A B) ⬝ (star₁_eq_concat A B)

end eckmann_hilton
end Eq



open Eq

def homotopy {P : α → Type*} (f g : Π (a : α), P a) : Type* :=
Π (a : α), f a = g a

localized "infix ` ∼ `:50 := homotopy" in hott

namespace homotopy
open_locale hott

variables {P : α → Type*} (f g h : Π (a : α), P a)

def refl : f ∼ f := λ a, rfl

def symm : f ∼ g → g ∼ f := λ H a, (H a)⁻¹

def trans : f ∼ g → g ∼ h → f ∼ h := λ H₁ H₂ a, (H₁ a) ⬝ (H₂ a)

def natural {f g : α → β} (H : f ∼ g) (p : a = b) :
  H a ⬝ g ▸ p = f ▸ p ⬝ H b :=
Eq.ind_on p (λ a, concat_rfl _)

def natural₁ {f : α → α} (H : f ∼ id) (a : α) :
  H (f a) = f ▸ H a :=
cancel_right (H a)
  ((_ ⬝l (ap_id _)⁻¹) ⬝ natural H (H a))


-- Quasi-equivalence
structure qequiv (α β : Type*) :=
(f : α → β)
(g : β → α)
(A : f ∘ g ∼ @id β)
(B : g ∘ f ∼ @id α)

localized "infix ` ≃q `:49 := homotopy.qequiv" in hott

def qequiv.refl : α ≃q α :=
{ f := id, g := id, A := λ b, rfl, B := λ a, rfl }

-- `def` instead of `instance` use to prevent typeclass loops
def qequiv.symm (ψ : α ≃q β) : β ≃q α :=
⟨ψ.g, ψ.f, ψ.B, ψ.A⟩

def qequiv.trans (ψ : α ≃q β) (ψ' : β ≃q γ) : α ≃q γ :=
{ f := ψ'.f ∘ ψ.f,
  g := ψ.g ∘ ψ'.g,
  A := λ c, (ψ'.f ▸ ψ.A (ψ'.g c)) ⬝ ψ'.A c,
  B := λ a, (ψ.g ▸ ψ'.B (ψ.f a)) ⬝ ψ.B a }

def _root_.Eq.trans.qequiv (p : a = b) (c : α) :
  b = c ≃q a = c :=
{ f := λ (q : b = c), p ⬝ q,
  g := λ (q : a = c), p⁻¹ ⬝ q,
  A := λ r, (concat_assoc _ _ _)⁻¹ ⬝ ((concat_inv _) ⬝r r),
  B := λ r, (concat_assoc _ _ _)⁻¹ ⬝ ((inv_concat _) ⬝r r)}

def _root_.Eq.trans.qequiv₁ (p : a = b) (c : α) :
  c = a ≃q c = b :=
{ f := λ (q : c = a), q ⬝ p,
  g := λ (q : c = b), q ⬝ p⁻¹,
  A := λ r, (concat_assoc _ _ _) ⬝ (r ⬝l (inv_concat _)) ⬝ concat_rfl _,
  B := λ r, (concat_assoc _ _ _) ⬝ (r ⬝l (concat_inv _)) ⬝ concat_rfl _ }

def _root_.Eq.transport.qequiv {P : α → Type*} (p : a = b) :
  P a ≃q P b :=
{ f := p∗, g := p⁻¹∗,
  A := λ u,
    transport_concat p⁻¹ p u ⬝
      (λ q, @@transport P q u) ▸ inv_concat p,
  B := λ u,
    transport_concat p p⁻¹ u ⬝
      (λ q, @@transport P q u) ▸ concat_inv p }


structure equiv (α β : Type*) :=
(f : α → β)
(g h : β → α)
(A : f ∘ g ∼ @id β)
(B : h ∘ f ∼ @id α)

localized "infix ` ≃ `:49 := homotopy.equiv" in hott

namespace equiv
def from_qequiv (ψ : α ≃q β) : α ≃ β :=
⟨ψ.f, ψ.g, ψ.g, ψ.A, ψ.B⟩

def to_qequiv (φ : α ≃ β) : α ≃q β :=
⟨φ.f, φ.g, φ.A,
  λ a, (φ.B $ (φ.g ∘ φ.f) a)⁻¹ ⬝
    φ.h ▸ φ.A (φ.f a) ⬝
    φ.B a⟩

-- To be proved in ch4
def uniq (φ : α ≃ β) (φ' : α ≃ β) : φ.f = φ'.f := sorry

def refl {α : Type*} : α ≃ α :=
from_qequiv qequiv.refl

def symm {α : Type*} (φ : α ≃ β) : β ≃ α :=
from_qequiv $ φ.to_qequiv.symm

def trans {α : Type*} (φ : α ≃ β) (φ' : β ≃ γ) : α ≃ γ :=
from_qequiv $ qequiv.trans φ.to_qequiv φ'.to_qequiv

end equiv
end homotopy



namespace prod
open_locale hott

variables (x y z : α × β)

-- Read: 'paths in product types are characterized by pairs of
-- paths between the respective components'
def eq : x = y ≃ (x.pr₁ = y.pr₁) × (x.pr₂ = y.pr₂) :=
homotopy.equiv.from_qequiv {
  f := λ p, ⟨pr₁ ▸ p, pr₂ ▸ p⟩,
  g := λ z, begin
    induction z with p q,
    induction x with a b,
    induction y with c d,
    pinduction a c p,
    pinduction b d q,
    spamrfl
  end,
  A := λ z, begin
    induction z with p q,
    induction x with a b,
    induction y with c d,
    pinduction a c p,
    pinduction b d q,
    spamrfl
  end,
  B := λ p, begin
    pinduction x y p,
    intro x,
    induction x with a b,
    spamrfl
  end
}

def pair {x y : α × β} : (x.pr₁ = y.pr₁) × (x.pr₂ = y.pr₂) → x = y :=
(eq x y).to_qequiv.g

def uniq₁ : x = ⟨x.pr₁, x.pr₂⟩ :=
@pair _ _ x ⟨x.pr₁, x.pr₂⟩ ⟨rfl, rfl⟩

-- Note the following equalities don't hold definitionally
example {p : x.pr₁ = y.pr₁} {q : x.pr₂ = y.pr₂} :
  pr₁ ▸ pair ⟨p, q⟩ = p :=
begin
  induction x with a b,
  induction y with c d,
  pinduction a c p,
  pinduction b d q,
  spamrfl
end

example {r : x = y} : r = pair ⟨pr₁ ▸ r, pr₂ ▸ r⟩ :=
begin
  pinduction x y r,
  intro x,
  induction x with a b,
  spamrfl
end

-- Inverse and concatenation is indeed component-wise
def inv_compwise (p : x = y) : p⁻¹ = pair ⟨(pr₁ ▸ p)⁻¹, (pr₂ ▸ p)⁻¹⟩ :=
begin
  pinduction x y p,
  intro x,
  induction x with a b,
  spamrfl
end

def concat_compwise (p : x = y) (q : y = z) :
  p ⬝ q = pair ⟨pr₁ ▸ p ⬝ pr₁ ▸ q, pr₂ ▸ p ⬝ pr₂ ▸ q⟩ :=
begin
  revert q,
  pinduction x y p,
  intros y q,
  pinduction y z q,
  intro z,
  induction z with a b,
  spamrfl
end

def transport_compwise (P Q : α → Type*) (p : a = b) (x : P a × Q a) :
  (p∗ x : P b × Q b) = ⟨p∗ x.pr₁, p∗ x.pr₂⟩ :=
begin
  revert x,
  pinduction a b p,
  intros a x,
  exact uniq x
end

def pair_fn (f : α → γ) (g : β → δ) : α × β → γ × δ :=
λ x, ⟨f x.pr₁, g x.pr₂⟩

def ap_compwise (f : α → γ) (g : β → δ)
  (p : x.pr₁ = y.pr₁) (q : x.pr₂ = y.pr₂) :
pair_fn f g ▸ pair ⟨p, q⟩ = pair ⟨f ▸ p, g ▸ q⟩ :=
begin
  induction x with a b,
  induction y with c d,
  pinduction a c p,
  pinduction b d q,
  spamrfl
end

end prod



namespace sigma
open_locale hott

variables {P : α → Type*} (x y : sigma P)

-- Paths in Σ-types are characterized by pairs of paths between
-- the respective components modulo transport
def eq : x = y ≃ Σ (p : x.pr₁ = y.pr₁), (p∗ x.pr₂ : P y.pr₁) = y.pr₂ :=
homotopy.equiv.from_qequiv {
  f := λ p, begin
    pinduction x y p,
    intro x, exact ⟨rfl, rfl⟩
  end,
  g := λ r, begin
    induction x with a b,
    induction y with c d,
    hrw (Eq.lift r.pr₁ b),
    happ (mk c),
    exact r.pr₂
  end,
  A := λ r, begin
    induction r with p q,
    induction x with a b,
    induction y with c d,
    change a = c at p,  -- Eliminate dependence on `b` and `d`
    revert b d q,
    pinduction a c p,
    intros a b d q,
    pinduction b d q,
    spamrfl
  end,
  B := λ p, begin
    pinduction x y p,
    intro x,
    induction x with a b,
    spamrfl
  end
}

def pair {x y : sigma P} :
  (Σ (p : x.pr₁ = y.pr₁), (p∗ x.pr₂ : P y.pr₁) = y.pr₂) → x = y :=
(eq x y).to_qequiv.g

def uniq₁ : x = ⟨x.pr₁, x.pr₂⟩ :=
@pair _ _ x ⟨x.pr₁, x.pr₂⟩ ⟨rfl, rfl⟩

def _root_.Eq.lift₁ (u : P a) : (⟨a, u⟩ : sigma P) = ⟨b, p∗ u⟩ :=
pair ⟨p, rfl⟩

def transport_compwise (P : α → Type*) (Q : sigma P → Type*)
  (p : a = b) (r : Σ (u : P a), Q ⟨a, u⟩) :
  (p∗ ⟨r.pr₁, r.pr₂⟩ : Σ (u : P b), Q ⟨b, u⟩) =
    ⟨p∗ r.pr₁, (lift p r.pr₁)∗ r.pr₂⟩ :=
begin
  revert r,
  pinduction a b p,
  spamrfl
end

end sigma



namespace unit
open_locale hott

def eq (a b : unit) : (a = b) ≃ unit :=
homotopy.equiv.from_qequiv {
  f := λ p, star,
  g := λ s, begin
    induction a,
    induction b,
    spamrfl
  end,
  A := λ s, begin
    induction s,
    spamrfl
  end,
  B := λ p, begin
    pinduction a b p,
    intro a,
    induction a,
    spamrfl
  end
}

end unit

end hott