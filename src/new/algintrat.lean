import data.rat.defs
import data.polynomial.algebra_map
import algebra.group.basic
import algebra.algebra.basic
import algebra.big_operators.intervals
import ring_theory.algebraic
import ring_theory.int.basic

-- A bunch of basic lemmas that really should be in `mathlib`
namespace int
theorem pos_of_pos_nat (n : ℕ) (h : n > 0) : (↑n : ℤ) > 0 :=
  nat.succ_pred_eq_of_pos h ▸ int.coe_succ_pos n.pred
end int

namespace rat
theorem pow_def (a b : ℤ) (b0 : b ≠ 0) (n : ℕ) :
  rat.mk a b ^ n = rat.mk (a ^ n) (b ^ n) :=
begin
  induction n with i hi,
    simp,
  repeat {rw pow_succ},
  rwa [hi, rat.mul_def],
  exact pow_ne_zero i b0
end

theorem rat_eq_mk (r : ℚ) : r = rat.mk r.num r.denom :=
begin
  have coprime : r.num.gcd r.denom = 1 := (int.gcd_eq_one_iff_coprime.mpr $
    int.coprime_iff_nat_coprime.mpr $
    show r.num.nat_abs.coprime (↑r.denom : ℤ).nat_abs,
      from (int.nat_abs_of_nat r.denom) ▸ r.cop),
  have denompos : (↑r.denom : ℤ) > 0 := int.pos_of_pos_nat r.denom r.pos,
  have denomsign : (↑r.denom : ℤ).sign = 1 := int.sign_eq_one_of_pos denompos,
  ext,
    rw [rat.num_mk, coprime, denomsign],
    simp,
  rw [rat.denom_mk, if_neg (ne_of_gt denompos), coprime],
  simp
end
end rat

-- The ring of integers of ℚ is ℤ
theorem int_of_algebraic_rat (r : ℚ) (hr : is_algebraic ℤ r) : r.denom = 1 :=
begin
  obtain ⟨p, hp1, hp2⟩ := hr,
  rw [polynomial.aeval_eq_sum_range,
    sub_eq_iff_eq_add.mp $ finset.sum_range_succ_sub_top _,
    rat.rat_eq_mk r]
    at hp2,
  simp_rw [rat.pow_def r.num ↑r.denom $
    ne_of_gt $ int.pos_of_pos_nat r.denom r.pos] at hp2,
  -- TODO
end