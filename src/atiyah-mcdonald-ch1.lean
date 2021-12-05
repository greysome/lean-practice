import algebra.ring.basic
import algebra.big_operators.basic
import algebra.group.units
import data.polynomial.basic
import data.polynomial.coeff
import data.polynomial.degree.definitions
import order.basic
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

  use inv,
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
      rw sum_const_zero, dsimp [S], rw hn, ring }
end

lemma nilpotent_of_mul_nilpotent (a r : R) (hr : is_nilpotent r) :
  is_nilpotent (a * r) :=
begin
  obtain ⟨n, hn⟩ := hr,
  use n,
  rw [mul_pow, hn, mul_zero]
end

theorem unit_of_unit_plus_nilpotent {u r : R} (hu : is_unit u) (hr : is_nilpotent r) :
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
lemma is_unit_const_of_unit {p : polynomial R} (h : is_unit p) :
  is_unit (p.coeff 0) :=
begin
  rw is_unit_iff_exists_inv at ⊢ h,
  obtain ⟨q, hpq⟩ := h,
  use q.coeff 0,
  rw polynomial.ext_iff at hpq,
  specialize hpq 0,
  rwa [mul_coeff_zero, coeff_one_zero] at hpq
end

lemma erase_const_eq {p : polynomial R} (dpos : p.nat_degree > 0) :
  (p.erase p.nat_degree).coeff 0 = p.coeff 0 :=
begin
  rw [coeff_erase, if_neg],
  exact ne_iff_lt_or_gt.mpr (or.inl dpos)
end

lemma nat_degree_erase_lt {p : polynomial R}
(dpos : p.nat_degree > 0) (hp : is_unit ((p.erase p.nat_degree).coeff 0)) :
  (p.erase p.nat_degree).nat_degree < p.nat_degree :=
begin
  set p' := p.erase p.nat_degree with p'_def,

  have h1 : p' ≠ 0,
  { by_contra h,
    rw polynomial.ext_iff at h,
    specialize h 0,
    rw coeff_zero at h,
    rw h at hp,
    exact not_is_unit_zero hp },
  
  have h2 : p'.degree < p.degree :=
    degree_erase_lt (ne_zero_of_nat_degree_gt dpos),
  rwa ←nat_degree_lt_nat_degree_iff h1 at h2,
end

lemma erase_add_leading_term (p : polynomial R) :
  p = p.erase p.nat_degree + (monomial p.nat_degree) p.leading_coeff :=
begin
  conv_lhs { rw ←(monomial_add_erase p p.nat_degree) },
  rw [add_comm, add_right_inj],
  refl,
end

lemma leading_term_nilpotent_of_unit {p : polynomial R}
(dpos : p.nat_degree > 0) (h : is_unit p) :
  is_nilpotent p.leading_coeff :=
begin
  rw is_unit_iff_exists_inv at h,
  obtain ⟨q, hpq⟩ := h,

  let n := p.nat_degree,
  let m := q.nat_degree,
  have h1 : n + m > 0 := sorry,

  have h2 : ∀ r, r ≥ 0 ∧ r ≤ m → p.coeff n ^ (r + 1) * q.coeff (m - r) = 0,
  { rintro r ⟨hr1, hr2⟩,
    apply nat.case_strong_induction_on r,
    { simp,
      rw polynomial.ext_iff at hpq,
      specialize hpq (n + m),
      rw [coeff_mul, coeff_one, if_neg] at hpq,
      { convert hpq,
        sorry },
      exact ne_of_lt h1, },
    { intros k hk,
      rw polynomial.ext_iff at hpq,
      specialize hpq (n + m - k.succ),
      have h : n + m - k.succ > 0 := sorry,
      rw [coeff_mul, coeff_one, if_neg] at hpq,
      { sorry },
      exact ne_of_lt h } },

  have h3 : ∀ r, r ≥ 0 ∧ r ≤ m → p.coeff n ^ m.succ * q.coeff (m - r) = 0,
  { intros r hr,
    have h := h2 r hr,
    have : ∀ (a b c : R), a = b → c * a = c * b :=
      by { intros a b c h, rw h },
    replace h := this _ _ (p.coeff n ^ (m + 1 - r.succ)) h,
    have ha : m.succ - r.succ + r.succ = m.succ :=
      nat.sub_add_cancel (nat.succ_le_succ_iff.mpr hr.right),
    rwa [←mul_assoc, mul_zero, ←pow_add, ha] at h },

  have h4 : p.coeff n ^ m.succ * eval 1 q = 0,
  { rw [eval_eq_finset_sum, mul_sum], simp,
    convert finset.sum_const_zero,
    ext i,
    by_cases hi : i ≥ 0 ∧ i ≤ m,
    sorry },

  have h5 : is_unit (eval 1 p) := sorry,

  have h6 : p.coeff n ^ m.scc = 0 :=
   by rw [←mul_one (p.coeff n ^ m.succ), ←is_unit.mul_coe_inv h5,
          ←mul_assoc, h4, zero_mul],
  use m, convert h6,
end

theorem ex1_2i (p : polynomial R) :
  is_unit p ↔ is_unit (p.coeff 0) ∧ ∀ (n : ℕ), n > 0 → is_nilpotent (p.coeff n) :=
begin
  split,
  { intro hp,
    split,
      exact is_unit_const_of_unit hp,

    { intros n npos,
      generalize hd : p.nat_degree = d,
      revert n hd p,
      apply nat.case_strong_induction_on d,
      { intros p hp n npos hd,
        rw coeff_eq_zero_of_nat_degree_lt _,
        exact is_nilpotent.zero, rwa hd },
      { intros i hi p hp n npos hd,

        set p' := erase p.nat_degree p with p'_def,
        have h1 := erase_add_leading_term p,
        replace h1 := eq.symm h1,
        rw [←p'_def, ←eq_add_neg_iff_add_eq] at h1,

        have dpos := nat.pos_of_ne_zero (nat.succ_ne_zero i),
        rw ←hd at dpos,

        have h2 : is_nilpotent (-(monomial p.nat_degree) p.leading_coeff),
        { obtain ⟨n, hn⟩ := leading_term_nilpotent_of_unit dpos hp,
          use n,
          rw [←monomial_neg, monomial_pow, monomial_eq_zero_iff],
          rw [neg_eq_neg_one_mul, mul_pow, hn, mul_zero] },

        have h3 := unit_of_unit_plus_nilpotent hp h2,
        rw ←h1 at h3,

        have h4 : is_unit (p'.coeff 0) :=
          by { rw erase_const_eq dpos, exact is_unit_const_of_unit hp },

        have h5 : p'.nat_degree < p.nat_degree :=
          nat_degree_erase_lt dpos h4,
          
        have h6 : ∀ n, n > 0 → is_nilpotent (p'.coeff n),
        { intros n npos,
          rw [hd, nat.lt_succ_iff] at h5,
          exact hi p'.nat_degree h5 p' h3 n npos rfl },
          
        by_cases hn : n = p.nat_degree,
        { convert (leading_term_nilpotent_of_unit dpos hp) },
        { specialize h6 n npos,
          convert h6 using 1,
          rwa [coeff_erase, if_neg] } } } },

  { rintro ⟨hconst, hp⟩,
    generalize hd : p.nat_degree = d,
    revert hd p,
    apply nat.case_strong_induction_on d,

    { intros p hconst _ hd,
      rw is_unit_iff_exists_inv at ⊢ hconst,
      obtain ⟨inv, mul_inv⟩ := hconst,
      rw eq_C_of_nat_degree_eq_zero hd,

      use C inv, rw [←C_mul, mul_inv], exact C_1 },

    { intros i hi p hconst hrest hd,
      have dpos := nat.pos_of_ne_zero (nat.succ_ne_zero i),
      rw ←hd at dpos,

      set p' := erase p.nat_degree p with p'_def,

      have h1 := erase_const_eq dpos,
      have hconst' : is_unit (p'.coeff 0) := by { rw h1, exact hconst },

      have h2 : p'.nat_degree < p.nat_degree :=
        nat_degree_erase_lt dpos hconst',

      have h3 : ∀ n, p'.coeff n = p.coeff n ∨ p'.coeff n = 0,
      { intro n,
        rw coeff_erase,
        by_cases hn : n = p.nat_degree,
        { rw if_pos, right, refl, assumption },
        { rw if_neg, left, refl, assumption } },

      have hrest' : ∀ n, n > 0 → is_nilpotent (p'.coeff n),
      { intro n, cases h3 n with ha hb,
          rw ha, exact hrest n,
          rw hb, intro _, exact is_nilpotent.zero },
      
      have h4 : is_unit p',
      { rw [hd, nat.lt_succ_iff] at h2,
        exact hi p'.nat_degree h2 p' hconst' hrest' rfl },
      
      let leading_term := (monomial p.nat_degree) p.leading_coeff,
      have h5 : is_nilpotent leading_term,
      { obtain ⟨n, hn⟩ := hrest p.nat_degree dpos,
        use n,
        rw [monomial_pow, monomial_eq_zero_iff],
        convert hn },

      rw [erase_add_leading_term p, ←p'_def],
      exact unit_of_unit_plus_nilpotent h4 h5 } }
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