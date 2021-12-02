import data.nat.basic
import data.int.basic
import data.real.basic
open classical

variables (α : Type) (p q : α → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h : ∀ x, p x ∧ q x,
    and.intro
      (λ x, show p x, from (h x).left)
      (λ x, show q x, from (h x).right))
  (assume h : (∀ x, p x) ∧ (∀ x, q x),
    λ x, show p x ∧ q x, from ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h1 : ∀ x, p x → q x,
assume h2 : ∀ x, p x,
λ x, show q x, from (h1 x) (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h : (∀ x, p x) ∨ (∀ x, q x),
λ x, show p x ∨ q x, from or.elim h
  (assume h1 : ∀ x, p x, or.inl (h1 x))
  (assume h2 : ∀ x, q x, or.inr (h2 x))

example : α → ((∀ x : α, r) ↔ r) :=
λ x, iff.intro
  (assume h : ∀ y : α, r, show r, from h x)
  (assume r1 : r, λ y, show r, from r1)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
  (assume h : ∀ x, p x ∨ r,
    by_cases
      (assume h1 : r, or.inr h1)
      (assume h1 : ¬r, or.inl
        (λ x, show p x, from or.elim (h x)
          (assume h2 : p x, h2)
          (assume h2 : r, false.elim (h1 h2)))))
  (assume h : (∀ x, p x) ∨ r,
    assume x : α,
    show p x ∨ r, from or.elim h
      (assume h1 : ∀ x, p x, or.inl (h1 x))
      (λ r1, or.inr r1))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro
  (assume h : ∀ x, r → p x,
    λ r x, show p x, from h x r)
  (assume h : r → ∀ x, p x,
    λ x r, show p x, from h r x)

-- Barber paradox
variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
or.elim (classical.em (shaves barber barber))
  (assume h1 : shaves barber barber, (h barber).mp h1 h1)
  (assume h1 : ¬ shaves barber barber, h1 ((h barber).mpr h1))

-- Some number theory
def prime (n : ℕ) : Prop := ∀ (k : ℕ), k ∣ n → k = 1 ∨ k = n

def infinitely_many_primes : Prop := ∀ n, ∃ N, n < N ∧ prime N

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ (k : ℕ), n = 2 ^ k + 1

def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ N, n < N ∧ Fermat_prime N

def goldbach_conjecture : Prop :=
  ∀ (n : ℕ), even n → (∃ x y, prime x ∧ prime y ∧ n = x + y)

def Goldbach's_weak_conjecture : Prop :=
  ∀ (n : ℕ), ¬ even n ∧ n > 5 → (∃ x y z, prime x ∧ prime y ∧ prime z ∧ n = x + y + z)

def Fermat's_last_theorem : Prop :=
  ∀ (n : ℕ), n > 2 → ¬(∃ (a b c : ℕ), a ^ n + b ^ n = c ^ n)

-- Very fun
example : (∃ x : α, r) → r :=
assume h : ∃ x, r,
let ⟨x, r⟩ := h in r

example (a : α) : r → (∃ x : α, r) :=
λ r0, exists.intro a r0

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
  (assume h : ∃ x, p x ∧ r,
    let ⟨x, hx⟩ := h in ⟨⟨x, hx.left⟩, hx.right⟩)
  (assume h : (∃ x, p x) ∧ r,
    let ⟨x, hx⟩ := h.left in ⟨x, hx, h.right⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (assume h : ∃ x, p x ∨ q x,
    let ⟨x, hx⟩ := h in or.elim hx
      (assume h1 : p x, or.inl ⟨x, h1⟩)
      (assume h1 : q x, or.inr ⟨x, h1⟩))
  (assume h : (∃ x, p x) ∨ (∃ x, q x),
    or.elim h
      (assume h1 : ∃ x, p x, let ⟨x, hx⟩ := h1 in ⟨x, or.inl hx⟩)
      (assume h1 : ∃ x, q x, let ⟨x, hx⟩ := h1 in ⟨x, or.inr hx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro
  (assume h1 : ∀ x, p x,
    assume h2 : ∃ x, ¬ p x,
    let ⟨x, hnpx⟩ := h2 in hnpx (h1 x))
  (assume h1 : ¬ (∃ x, ¬ p x),
    λ x, by_cases
      (assume h2 : p x, h2)
      (assume h2 : ¬ p x, false.elim (h1 ⟨x, h2⟩)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro
  (assume h1 : ∃ x, p x,
    assume h2 : ∀ x, ¬ p x,
    let ⟨x, hpx⟩ := h1 in h2 x hpx)
  (assume h1 : ¬ (∀ x, ¬ p x),
    classical.by_contradiction
      (assume h2 : ¬ (∃ x, p x),
        suffices h3 : ∀ x, ¬ p x, from h1 h3,
        λ x, assume h4 : p x, h2 ⟨x, h4⟩))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro
  (assume h1 : ¬ ∃ x, p x,
    λ x, by_cases
      (assume h2 : p x, false.elim (h1 ⟨x, h2⟩))
      (assume h2 : ¬ p x, h2))
  (assume h1 : ∀ x, ¬ p x,
    assume h2 : ∃ x, p x,
    let ⟨x, hpx⟩ := h2 in h1 x hpx)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro
  (assume h1 : ¬ ∀ x, p x,
    classical.by_contradiction
      (assume h2 : ¬ (∃ x, ¬ p x),
        suffices h3 : ∀ x, p x, from h1 h3,
        λ x, by_cases
          (assume h4 : p x, h4)
          (assume h4 : ¬ p x, false.elim (h2 ⟨x, h4⟩))))
  (assume h1 : ∃ x, ¬ p x,
    assume h2 : ∀ x, p x,
    let ⟨x, hnpx⟩ := h1 in hnpx (h2 x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
  (assume h1 : ∀ x, p x → r,
    assume h2 : ∃ x, p x,
    let ⟨x, hpx⟩ := h2 in h1 x hpx)
  (assume h1 : (∃ x, p x) → r,
    λ x, assume h2 : p x, h1 ⟨x, h2⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
  (assume h1 : ∃ x, p x → r,
    assume h2 : ∀ x, p x,
    let ⟨x, hpxr⟩ := h1 in hpxr (h2 x))
  -- This solution is very cursed
  (assume h1 : (∀ x, p x) → r,
    show ∃ x, p x → r, from
      by_cases
        (assume hap : ∀ x, p x, ⟨a, λ h', h1 hap⟩)
        (assume hnap : ¬ ∀ x, p x,
          classical.by_contradiction
            (assume hnex : ¬ ∃ x, p x → r,
              have hap : ∀ x, p x, from
                assume x,
                classical.by_contradiction
                  (assume hnp : ¬ p x,
                    have hex : ∃ x, p x → r,
                      from ⟨x, (assume hp, absurd hp hnp)⟩,
                    show false, from hnex hex),
              show false, from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
iff.intro
  (assume h1 : ∃ x, r → p x,
    assume r1 : r,
    let ⟨x, hrpx⟩ := h1 in ⟨x, hrpx r1⟩)
  (assume h1 : r → ∃ x, p x,
    by_cases
      (assume h2 : r,
        let ⟨x, hpx⟩ := h1 h2 in ⟨x, λ r, hpx⟩)
      (assume h2 : ¬ r,
        exists.intro a
          (assume r1 : r, false.elim (h2 r1))))

-- Some calculation
variables log exp : real → real
variable log_exp_eq : ∀ x, log (exp x) = x
variable exp_log_eq : ∀ x, x > 0 → exp (log x) = x
variable exp_pos : ∀ x, exp x > 0
variable exp_add : ∀ x y, exp (x + y) = exp x * exp y
include log_exp_eq exp_log_eq exp_pos exp_add

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc log (x * y) = log (x * exp (log y)) : by rw exp_log_eq y hy
... = log (exp (log x) * exp (log y)) : by rw exp_log_eq x hx
... = log (exp (log x + log y)) : by rw exp_add
... = log x + log y : log_exp_eq _

example (x : ℤ) : x * 0 = 0 :=
calc x * 0 = x * (x - x) : by rw ←sub_self
... = x * x - x * x : by rw mul_sub
... = 0 : by rw sub_self