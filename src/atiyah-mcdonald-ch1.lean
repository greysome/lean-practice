import algebra.ring.basic
import algebra.big_operators.basic
import algebra.group.units
import order.locally_finite
import ring_theory.nilpotent
import tactic
open finset tactic
open_locale big_operators

variables {R : Type} [comm_ring R] [nontrivial R]

lemma mul_neg_one_square (r : R) : r * (-1) ^ 2 = r := by ring

theorem unit_of_one_plus_nilpotent (r : R) (h : is_nilpotent r) :
  is_unit (1 + r) :=
begin
  by_cases rzero : r = 0,
  rw [rzero, add_zero],
  exact is_unit_one,

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

  let u : units R := {
    val := 1 + r,
    inv := inv,
    val_inv := by rwa mul_comm,
    inv_val := S_inv
  },
  use ⟨u, rfl⟩
end

lemma nilpotent_of_unit_mul_nilpotent (u : units R) (r : R) (h : is_nilpotent r) :
  is_nilpotent (↑u * r) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [mul_pow, hn, mul_zero]
end

theorem unit_of_unit_plus_nilpotent (u : units R) (r : R) (h : is_nilpotent r) :
  is_unit (↑u + r) :=
begin
  rw [←(units.is_unit_mul_units _ u⁻¹), add_mul],
  rw [units.mul_inv, mul_comm],
  apply unit_of_one_plus_nilpotent,
  exact nilpotent_of_unit_mul_nilpotent u⁻¹ r h
end