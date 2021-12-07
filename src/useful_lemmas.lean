import algebra.ring.basic
import algebra.big_operators.basic
import algebra.group.units
import data.nat.basic
import data.polynomial.basic
import data.polynomial.coeff
import data.polynomial.degree.definitions
open finset tactic polynomial nat set
open_locale big_operators

variables {R : Type*} [comm_ring R] [nontrivial R]

lemma add_lt_of_lt_and_le {a b c d : ℕ} (h1 : a < b) (h2 : c ≤ d) :
  a + c < b + d :=
begin
  calc a + c < b + c : add_lt_add_right h1 c
  ... ≤ b + d : add_le_add_left h2 b,
end

lemma mul_left_of_eq {a b : R} (c : R) (h : a = b) : c * a = c * b :=
  by { rw h }

lemma mul_right_of_eq {a b : R} (c : R) (h : a = b) : a * c = b * c :=
  by { rw h }

lemma sub_sub' {a b : ℕ} (h : b ≤ a) : a - (a - b) = b :=
  by { rw [nat.sub_eq_iff_eq_add (nat.sub_le _ _),
            nat.add_sub_of_le h] }

lemma erase_nat_degree_lt {p : polynomial R} (dpos : p.nat_degree > 0) :
  (p.erase p.nat_degree).nat_degree < p.nat_degree :=
begin
  sorry
end

lemma const_or_erase_nat_degree_lt (p : polynomial R) :
  p.nat_degree = 0 ∨ (p.erase p.nat_degree).nat_degree < p.nat_degree :=
begin
  by_cases hd : p.nat_degree = 0,
  { left, assumption },
  { right,
    change p.nat_degree ≠ 0 at hd,
    rw ←pos_iff_ne_zero at hd,
    exact erase_nat_degree_lt hd }
end

lemma erase_const_eq {p : polynomial R} (dpos : p.nat_degree > 0) :
  (p.erase p.nat_degree).coeff 0 = p.coeff 0 :=
begin
  rw [coeff_erase, if_neg],
  exact ne_iff_lt_or_gt.mpr (or.inl dpos)
end

lemma orig_eq_erase_add_leading_term (p : polynomial R) :
  p = p.erase p.nat_degree + (monomial p.nat_degree) p.leading_coeff :=
begin
  conv_lhs { rw ←(monomial_add_erase p p.nat_degree) },
  rw [add_comm, add_right_inj],
  refl,
end

lemma erase_eq_orig_sub_leading_term (p : polynomial R) :
  p.erase p.nat_degree = p + -(monomial p.nat_degree) p.leading_coeff :=
begin
  have h := orig_eq_erase_add_leading_term p,
  conv_rhs { congr, rw h },
  simp,
end

lemma erase_coeff_eq_orig {p : polynomial R} {n : ℕ} (h : ¬n = p.nat_degree) :
  (p.erase p.nat_degree).coeff n = p.coeff n :=
by { rwa [coeff_erase, if_neg] }

lemma erase_coeff_eq_orig_or_zero (p : polynomial R) (n : ℕ) :
  (p.erase p.nat_degree).coeff n = 0 ∨ (p.erase p.nat_degree).coeff n = p.coeff n :=
begin
  by_cases hn : n = p.nat_degree,
  { left, rwa [coeff_erase, if_pos] },
  { right, exact erase_coeff_eq_orig hn }
end

lemma reduce_to_erase {P : R → Prop} {p : polynomial R} (n : ℕ)
  (h1 : P p.leading_coeff)
  (h2 : ∀ n, P ((p.erase p.nat_degree).coeff n)) :
  P (p.coeff n) :=
begin
  by_cases hn : n = p.nat_degree,
  { convert h1 },
  { rw ←erase_coeff_eq_orig hn, exact h2 n }
end