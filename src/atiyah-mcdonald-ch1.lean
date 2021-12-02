import algebra.ring.basic
import algebra.big_operators.basic
import algebra.group.units
import data.polynomial.basic
import data.polynomial.coeff
import data.polynomial.degree.definitions
import order.locally_finite
import ring_theory.nilpotent
import ring_theory.polynomial.content
import tactic
open finset tactic polynomial
open_locale big_operators

variables {R : Type} [comm_ring R] [nontrivial R]

/-
1.1: sum of unit and nilpotent is a unit
Note: An alternative approach is to use the characterisation of members
of the Jacobson radical, and apply it to nilpotent elements.
-/
lemma mul_neg_one_square (r : R) : r * (-1) ^ 2 = r := by ring

theorem unit_of_one_plus_nilpotent (r : R) (h : is_nilpotent r) :
  is_unit (1 + r) :=
begin
  rw is_unit_iff_exists_inv',
  by_cases rzero : r = 0,
  rw [rzero, add_zero],
  use ⟨1, by ring⟩,

  obtain ⟨n, hn⟩ := h,
  have npos : n > 0,
  { by_contra h,
    replace h := nat.eq_zero_of_le_zero (le_of_not_gt h),
    subst h,
    have contra : (0 : R) ≠ (1 : R) := zero_ne_one,
    rw ←hn at contra,
    exact contra (pow_zero _) },

  set S : ℕ → R := λ k, (-1) ^ k * r ^ k with Sdef,
  set inv := ∑ (k : ℕ) in Ico 0 n, S k with invdef,

  have : ∀ (k : ℕ), S (k+1) = (-1) ^ (k+1) * r ^ (k+1) :=
    by { intro k, refl },

  have S_inv : inv * (1 + r) = 1,
  { rw [invdef, mul_add, mul_one, sum_mul],
    -- I wish there was an easier way to manipulate sums...
    conv_lhs {
      conv {
        congr, skip, congr, skip, funext,
        rw mul_assoc, rw ←pow_succ',

        rw ←mul_neg_one_square ((-1 : R) ^ x),
        rw [←pow_add, pow_succ, mul_assoc, ←this x, add_comm],
      },
      conv {
        congr,
        rw [sum_eq_sum_Ico_succ_bot npos, zero_add],
        skip,
        rw sum_Ico_add (λ k, (-1) * S k),
        rw sum_Ico_succ_top (nat.succ_le_iff.mpr npos),
      }
    },
    repeat { dsimp only },
    conv_lhs {
      rw add_assoc, congr, skip, rw ←add_assoc, congr,
      rw ←sum_add_distrib, congr, skip, funext,
      dsimp [S], simp,
    },
    rw sum_const_zero, dsimp [S], rw hn, ring },

  use inv, exact S_inv
end

lemma nilpotent_of_mul_nilpotent (a r : R) (hr : is_nilpotent r) :
  is_nilpotent (a * r) :=
begin
  obtain ⟨n, hn⟩ := hr,
  use n,
  rw [mul_pow, hn, mul_zero]
end

theorem unit_of_unit_plus_nilpotent (u r : R) (hu : is_unit u) (hr : is_nilpotent r) :
  is_unit (u + r) :=
begin
  have hu' := hu,  -- For the last line
  rw is_unit_iff_exists_inv at hu,
  obtain ⟨v, huv⟩ := hu,

  have : u + r = u * (1 + v * r) :=
    by { rw [mul_add, ←mul_assoc], rw huv, simp },
  rw this,

  exact is_unit.mul hu'
    (unit_of_one_plus_nilpotent _ (nilpotent_of_mul_nilpotent _ _ hr)),
end

/-
1.2: characterisation of units, nilpotents, zero divisors in R[x],
and primitive elements
-/
theorem ex1_2i (p : polynomial R) :
  is_unit p ↔ is_unit (p.coeff 0) ∧ ∀ (n : ℕ), n > 0 → is_nilpotent (p.coeff n) :=
begin
  split,
  { repeat { rw is_unit_iff_exists_inv },
    rintro ⟨q, hpq⟩,
    split,
    { use q.coeff 0,
      rw polynomial.ext_iff at hpq,
      specialize hpq 0,
      rwa [mul_coeff_zero, coeff_one_zero] at hpq },
    -- The hard part
    { sorry } },
  { rintro ⟨hconst, hp⟩,
    let d' := p.degree,
    have : d' ≠ ⊥ := sorry,
    have d := with_bot.unbot d' this,
    clear this d',
    sorry }
end

theorem ex1_2ii (p : polynomial R) :
  is_nilpotent p ↔ ∀ (n : ℕ), is_nilpotent (p.coeff n) :=
begin
  sorry
end

def is_zero_divisor (a : R) : Prop := a ≠ 0 ∧ ∃ b, b ≠ 0 ∧ a * b = 0

theorem ex1_2iii (p : polynomial R) :
  is_zero_divisor p ↔ ∃ (a : R), a ≠ 0 ∧ a • p = 0 :=
sorry

theorem ex1_2iv (p q : polynomial R) :
  (p * q).is_primitive ↔ p.is_primitive ∧ q.is_primitive :=
sorry