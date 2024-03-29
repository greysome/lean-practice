import data.rat.defs
import data.fintype.card
import data.polynomial.eval
import algebra.group.basic
import algebra.algebra.basic
import algebra.big_operators.intervals
import ring_theory.algebraic
import ring_theory.int.basic

-- This code is a perfect example of how *NOT* to use Lean
-- There are some `sorry`s because I attempted to refactor my old code
-- to make it more idiomatic, but I just gave up halfway...

namespace rat
theorem pow_num_denom (q : ℚ) (n : ℕ) : q ^ n = rat.mk (q.num ^ n) (↑q.denom ^ n) :=
sorry

theorem div_mk_div_cancel_right {a b c : ℤ} (c0 : c ≠ 0) :
  rat.mk (c * a) (c * b) = rat.mk a b :=
by rw [mul_comm c a, mul_comm c b, rat.div_mk_div_cancel_left c0]

theorem sum_same_denom {n : ℕ} {num : fin (n + 1) → ℤ} {denom : ℤ} :
  finset.univ.sum (λ x : fin (n + 1), rat.mk (num x) denom) =
  rat.mk (finset.univ.sum (λ x : fin (n + 1), num x)) denom := by {
  induction n with i hi,
    repeat {rw fin.sum_univ_one},
  repeat {rw @fin.sum_univ_succ _ _ i.succ _},
  repeat {rw rat.add_mk},
  congr,
  apply hi, 
}
end rat

-- The ring of integers of ℚ is ℤ
theorem int_of_algebraic_rat (r : ℚ) (hr : is_integral ℤ r) : r.denom = 1 :=
begin
  obtain ⟨p, hp1, hp2⟩ := hr,
  set n := p.nat_degree with hn,
  set P := r.num with hP,
  set Q : ℤ := ↑r.denom with hQ,

  by_cases p.nat_degree = 0,
  { rw [polynomial.eq_C_of_nat_degree_eq_zero h,
      polynomial.eval₂_C,
      algebra_map_int_eq,
      ring_hom.eq_int_cast,
      rat.coe_int_eq_mk,
      rat.mk_eq_zero one_ne_zero,
      ←h,
      polynomial.monic.coeff_nat_degree hp1]
      at hp2,
    exact false.elim (one_ne_zero hp2) },

  have Qpow : ∀ n : ℕ, Q ^ n ≠ 0 := sorry,
  rw [polynomial.eval₂_eq_sum,
    polynomial.sum_over_range, -- generates an intermediate goal...
    ←fin.sum_univ_eq_sum_range]
    at hp2,
  simp_rw [algebra_map_int_eq,
    ring_hom.eq_int_cast,
    rat.coe_int_eq_mk,
    rat.pow_num_denom,
    rat.mul_def one_ne_zero $ Qpow _,
    one_mul,
    rat.mk_eq_div] at hp2,

  swap, -- ...which we immediately handle
  { intro n, simp },
  
  have : (λ x : fin (n + 1), ((p.coeff (x : ℕ) * P ^ ↑x) / Q ^ (x : ℕ))) =
    (λ x : fin (n + 1), ((p.coeff (x : ℕ) * P ^ (x : ℕ) * Q ^ (n -(x : ℕ))) / Q ^ n : ℚ)) := by {
    funext,
    calc ((p.coeff ↑x * P ^ ↑x) / Q ^ ↑x : ℚ)
      = ((p.coeff ↑x * P ^ ↑x * Q ^ (n-↑x)) / (Q ^ ↑x * Q ^ (n-↑x)) : ℚ) : sorry
    ... = ((p.coeff ↑x * P ^ ↑x * Q ^ (n-↑x)) / Q ^ n : ℚ) : sorry,
  },

  -- Tedious rewriting lemmas
  have h1 : ∀ x : ℕ, x ≤ n → rat.mk (P ^ x) (Q ^ x) =
    rat.mk (Q ^ (n - x) * P ^ x) (Q ^ n) := by {
    intros x hx,
    calc rat.mk (P ^ x) (Q ^ x)
      = rat.mk (Q ^ (n - x) * P ^ x) (Q ^ (n - x) * Q ^ x) :
        rat.mk_mul_num_and_denom (Qpow x) (Qpow (n - x))
    ... = rat.mk (Q ^ (n - x) * P ^ x) (Q ^ n) : by rw [←pow_add, nat.sub_add_cancel hx]
  },
  
  have h2 : (λ x : fin (n + 1), rat.mk (p.coeff ↑x) 1 * rat.mk (P ^ ↑x) (Q ^ ↑x)) =
    (λ x : fin (n + 1), rat.mk (p.coeff ↑x * Q ^ (n - ↑x) * P ^ ↑x) (Q ^ n)) := by {
    funext,
    rw [h1 x $ nat.le_of_lt_succ x.is_lt,
      rat.mul_def one_ne_zero (Qpow n),
      ←mul_assoc, one_mul]
  },

  rw [h2,
    rat.sum_same_denom,
    rat.mk_eq_zero $ Qpow n,
  -- Just to extract one term out...
    fin.sum_univ_eq_sum_range (λ x : ℕ, p.coeff x * Q ^ (n - x) * P ^ x) (n + 1),
    eq_add_of_sub_eq $ finset.sum_range_succ_sub_top _,
    ←fin.sum_univ_eq_sum_range (λ x : ℕ, p.coeff x * Q ^ (n - x) * P ^ x) n]
    at hp2,
  dsimp at hp2,
  clear h1 h2,
  
  have h3 : (λ x : fin n, (p.coeff (↑x : ℕ)) * Q ^ (n - (↑x : ℕ)) * P ^ (↑x : ℕ)) =
    (λ x : fin n, Q * ((p.coeff (↑x : ℕ)) * Q ^ (n - (↑x : ℕ) - 1) * P ^ (↑x : ℕ))) := by {
    funext,
    have : Q ^ (n - ↑x) = Q * Q ^ (n - ↑x - 1) :=
      calc Q ^ (n - ↑x) = Q ^ (n - ↑x).pred.succ : by rw nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt x.is_lt)
      ... = Q * Q ^ (n - ↑x - 1) : by rw [pow_succ, nat.pred_eq_sub_one],
    -- idk why `ring` tactic hangs
    rw [this, ←mul_assoc (p.coeff ↑x) _ _, mul_comm (p.coeff ↑x) Q,
      mul_assoc Q _ _, mul_assoc Q _ _]
  },

  rw [h3, ←finset.mul_sum, polynomial.monic.leading_coeff hp1,
    one_mul, nat.sub_self, pow_zero, one_mul] at hp2,
  clear h3,

  obtain ⟨a, b, hab⟩ := (is_coprime.pow_left_iff $ nat.pos_of_ne_zero h).mpr
    ((@int.coprime_iff_nat_coprime P Q).mpr r.cop),
  replace hp2 := congr_arg (λ x : ℤ, a * x) hp2,
  dsimp at hp2,
  rw [mul_add, mul_zero] at hp2,

  rw ←eq_sub_iff_add_eq at hab,
  rw [hab, int.sub_eq_add_neg, add_comm, add_assoc, add_eq_zero_iff_eq_neg,
    ←mul_assoc, mul_comm b Q, mul_comm a Q, mul_assoc Q a _,
    neg_mul_eq_mul_neg, ←mul_add, neg_mul_eq_mul_neg]
    at hp2,
  clear hab,

  rw [←int.nat_abs_of_nat r.denom,
    int.eq_one_of_dvd_one (le_of_lt $ int.pos_of_pos_nat r.pos) ⟨_, hp2⟩,
    int.nat_abs_one],
end