import useful_lemmas
import algebra.ring.basic
import algebra.big_operators.basic
import algebra.group.units
import data.nat.basic
import data.polynomial.basic
import data.polynomial.coeff
import data.polynomial.degree.definitions
import order.basic
import order.locally_finite
import ring_theory.nilpotent
import ring_theory.polynomial.content
import tactic
open finset tactic polynomial nat set
open_locale big_operators

variables {R : Type*} [comm_ring R] [nontrivial R]

/-
1.1: sum of unit and nilpotent is a unit
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
          rw sum_Ico_succ_top (succ_le_iff.mpr npos),
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

lemma sum_antidiagonal_split {a b : ℕ} {f : ℕ × ℕ → R} :
  ∑ (x : ℕ × ℕ) in nat.antidiagonal (a + b), f x =
  ∑ x in nat.antidiagonal (a + b) \ {(a, b)}, f x + f (a, b) :=
begin
  have h : {(a, b)} ⊆ nat.antidiagonal (a + b),
  { intro x,
    rw [finset.mem_singleton, nat.mem_antidiagonal],
    intro hx, rw hx },
  rw [←sum_sdiff h, sum_singleton],
end

lemma antidiagonal_gt_of {a b : ℕ} {x : ℕ × ℕ}
  (h : x ∈ nat.antidiagonal (a + b) \ {(a, b)}):
  x.fst > a ∨ x.snd > b :=
begin
  rw [mem_sdiff, nat.mem_antidiagonal, finset.mem_singleton,
      prod.ext_iff, not_and_distrib] at h,
  rcases h with ⟨hx1, hx2⟩,
  dsimp at hx2,

  by_contra h,
  rw not_or_distrib at h,
  cases hx2,
  { have contra := add_lt_of_lt_and_le
      ((ne.le_iff_lt hx2).mp (le_of_not_gt h.left))
      (le_of_not_gt h.right),
    exact (ne_of_lt contra) hx1 },
  { have contra := add_lt_of_lt_and_le
      ((ne.le_iff_lt hx2).mp (le_of_not_gt h.right))
      (le_of_not_gt h.left),
    conv_lhs at contra { rw add_comm },
    conv_rhs at contra { rw add_comm },
    exact (ne_of_lt contra) hx1 }
end

lemma leading_term_nilpotent_of_unit {p : polynomial R}
(dpos : p.nat_degree > 0) (h : is_unit p) :
  is_nilpotent p.leading_coeff :=
begin
  rw is_unit_iff_exists_inv at h,
  obtain ⟨q, hpq⟩ := h,

  let n := p.nat_degree,
  let m := q.nat_degree,
  have nmpos : n + m > 0 := add_pos_left dpos m,

  have h1 : ∀ r, r ≤ m → p.coeff n ^ (r + 1) * q.coeff (m - r) = 0,
  { intros r,
    rw polynomial.ext_iff at hpq,
    apply nat.case_strong_induction_on r, clear r,

    { intro _, simp,
      rw ←coeff_mul_degree_add_degree,
      specialize hpq (n + m),
      rwa [coeff_one, if_neg] at hpq,
      exact ne_of_lt nmpos },

    { intros i hi him,
      set d' := n + (m - i.succ) with d'_def,
      have d'pos : d' > 0 :=
        calc 0 < n : dpos
        ... = n + 0 : by rw add_zero
        ... ≤ n + (m - i.succ) : add_le_add_left (zero_le _) n,

      -- Spaghetti code warning
      specialize hpq d',
      rw [coeff_mul, coeff_one, if_neg] at hpq,
      swap, exact ne_of_lt d'pos,
      { have h : ∑ x in nat.antidiagonal d' \ {(n, m - i.succ)},
          p.coeff n ^ i.succ * (p.coeff x.fst * q.coeff x.snd) = 0,
        { apply sum_eq_zero,
          intros x hx,

          by_cases hx' : x.fst > n ∨ x.snd > m,
          { cases hx',
              rw [coeff_eq_zero_of_nat_degree_lt hx', zero_mul, mul_zero],
              rw [coeff_eq_zero_of_nat_degree_lt hx', mul_zero, mul_zero] },

          rw not_or_distrib at hx',
          replace hx := antidiagonal_gt_of hx,
          cases hx,
            rw [coeff_eq_zero_of_nat_degree_lt hx, zero_mul, mul_zero],

          replace hx := add_lt_add_right hx i.succ,
          rw [nat.sub_add_cancel him, add_succ, lt_succ_iff] at hx,
          replace hx := nat.sub_le_sub_right hx x.snd,
          rw nat.add_sub_cancel_left x.snd i at hx,
          -- hx is now `m - x.snd ≤ i`

          have ha := hi (m - x.snd) hx (nat.sub_le _ _),
          rw sub_sub' (not_lt.mp hx'.right) at ha,

          have hb : i.succ = (i.succ - (m - x.snd + 1)) + (m - x.snd + 1),
          { rw nat.sub_add_cancel _,
            rwa succ_le_succ_iff },
          rw [hb, pow_add, mul_assoc],
          conv_lhs { congr, skip, congr, skip, rw mul_comm },
          conv_lhs { congr, skip, rw ←mul_assoc },
          rw [ha, zero_mul, mul_zero] },

        replace hpq := mul_left_of_eq (p.coeff n ^ i.succ) hpq,
        rw [mul_sum, mul_zero, sum_antidiagonal_split] at hpq,
        dsimp only at hpq,
        rw [h, zero_add] at hpq,
        convert hpq using 1,
        rw [←mul_assoc, pow_add, pow_one] } } },

  have h2 : ∀ r, r ≤ m → p.coeff n ^ m.succ * q.coeff (m - r) = 0,
  { intros r hr,
    have h := h1 r hr,
    replace h := mul_left_of_eq (p.coeff n ^ (m + 1 - r.succ)) h,
    have ha : m.succ - r.succ + r.succ = m.succ :=
      nat.sub_add_cancel (succ_le_succ_iff.mpr hr),
    rwa [←mul_assoc, mul_zero, ←pow_add, ha] at h },

  have h3 : p.coeff n ^ m.succ * eval 1 q = 0,
  { rw [eval_eq_finset_sum, mul_sum],
    convert finset.sum_const_zero,
    ext i, rw [one_pow, mul_one],
    by_cases hi : i ≤ m,
    { have := h2 (m - i) (nat.sub_le _ _),
      rwa sub_sub' hi at this },
    { rw [coeff_eq_zero_of_nat_degree_lt (not_le.mp hi), mul_zero] } },

  have h4 : p.coeff n ^ m.succ = 0,
  { have ha : eval 1 q * eval 1 p = 1 :=
      by rw [←eval_mul, mul_comm, hpq, eval_one],
    have hb := mul_right_of_eq (eval 1 p) h3,
    rwa [mul_assoc, ha, mul_one, zero_mul] at hb },

  use m.succ, convert h4
end

lemma monomial_nilpotent_of_nilpotent {r : R} (h : is_nilpotent r) (n : ℕ) :
  is_nilpotent ((monomial n) r) :=
by { obtain ⟨n, hn⟩ := h, use n, rwa [monomial_pow, monomial_eq_zero_iff] }

theorem polynomial_unit_iff (p : polynomial R) :
  is_unit p ↔ is_unit (p.coeff 0) ∧ ∀ (n : ℕ), n > 0 → is_nilpotent (p.coeff n) :=
begin
  split,
  { intro hp, split,
    { exact is_unit_const_of_unit hp },

    revert hp,
    induction hd : p.nat_degree using nat.case_strong_induction_on with i hi generalizing p,
    { intros hp n npos,
      rw coeff_eq_zero_of_nat_degree_lt _,
      exact is_nilpotent.zero, rwa hd },

    { intros hp n npos,
      set p' := p.erase p.nat_degree with p'_def,

      have dpos := nat.pos_of_ne_zero (succ_ne_zero i),
      rw ←hd at dpos,

      have h1 := unit_of_unit_plus_nilpotent hp
        (is_nilpotent.neg
          (monomial_nilpotent_of_nilpotent
            (leading_term_nilpotent_of_unit dpos hp) p.nat_degree)),
      rw ←orig_sub_monomial p at h1,

      have h2 : p'.nat_degree < p.nat_degree := erase_nat_degree_lt dpos,
        
      have h3 : ∀ n, n > 0 → is_nilpotent (p'.coeff n),
      { intros n npos,
        rw [hd, lt_succ_iff] at h2,
        exact hi p'.nat_degree h2 p' rfl h1 n npos },
        
      by_cases hn : n = p.nat_degree,
      { convert (leading_term_nilpotent_of_unit dpos hp) },
      { specialize h3 n npos,
        convert h3 using 1,
        rwa [coeff_erase, if_neg] } } },

  { induction hd : p.nat_degree using nat.case_strong_induction_on with i hi generalizing p,
    { rintro ⟨hconst, -⟩,
      rw is_unit_iff_exists_inv at ⊢ hconst,
      obtain ⟨inv, mul_inv⟩ := hconst,
      rw eq_C_of_nat_degree_eq_zero hd,
      use C inv, rw [←C_mul, mul_inv], exact C_1 },

    { rintro ⟨hconst, hrest⟩,
      have dpos := nat.pos_of_ne_zero (succ_ne_zero i),
      rw ←hd at dpos,

      set p' := p.erase p.nat_degree with p'_def,

      have h1 : p'.nat_degree < p.nat_degree := erase_nat_degree_lt dpos,

      have hconst' : is_unit (p'.coeff 0) := 
        by { rw (erase_const_eq dpos), exact hconst },
      have hrest' : ∀ n, n > 0 → is_nilpotent (p'.coeff n),
      { intro n, cases erase_coeff_eq_orig_or_zero p n with ha hb,
          rw ha, intro _, exact is_nilpotent.zero,
          rw hb, exact hrest n },
      
      have h2 : is_unit p',
      { rw [hd, lt_succ_iff] at h1,
        exact hi p'.nat_degree h1 p' rfl ⟨hconst', hrest'⟩ },
      
      let leading_term := (monomial p.nat_degree) p.leading_coeff,
      have h3 : is_nilpotent leading_term,
      { obtain ⟨n, hn⟩ := hrest p.nat_degree dpos,
        use n, rw [monomial_pow, monomial_eq_zero_iff], convert hn },

      rw [←monomial_add_erase p p.nat_degree, ←p'_def, add_comm],
      exact unit_of_unit_plus_nilpotent h2 h3 } }
end

lemma leading_term_nilpotent_of_nilpotent {p : polynomial R} (h : is_nilpotent p) :
  is_nilpotent p.leading_coeff :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw ←coeff_pow_degree_mul_degree p n,
  rw polynomial.ext_iff at hn,
  exact hn _,
end

theorem polynomial_nilpotent_iff (p : polynomial R) :
  is_nilpotent p ↔ ∀ (n : ℕ), is_nilpotent (p.coeff n) :=
begin
  split,
  { induction hd : p.nat_degree using nat.strong_induction_on with i hi generalizing p,
    intros hp n,
    dsimp at hi, subst hd,
    cases erase_nat_degree_lt_or_zero p with h,

    { by_cases hn : n = 0,
      { rw [hn, ←h], exact leading_term_nilpotent_of_nilpotent hp },
      { change n ≠ 0 at hn, rw [←pos_iff_ne_zero, ←h] at hn,
        rw coeff_eq_zero_of_nat_degree_lt hn,
        exact is_nilpotent.zero }},

    { set p' := p.erase p.nat_degree with p'_def, rw ←p'_def at *,
      have hp' := hi p'.nat_degree h p' rfl,
      have h1 := leading_term_nilpotent_of_nilpotent hp,
      have h2 := commute.is_nilpotent_add (by exact comm_ring.mul_comm _ _) hp
        (is_nilpotent.neg
          (monomial_nilpotent_of_nilpotent h1 p.nat_degree)),
      rw ←orig_sub_monomial p at h2,

      apply reduce_to_erase n,
      { exact h1 },
      { exact hp' h2 },
      -- very hacky, figure out how to remove this
      exact _inst_2 } },

  { induction hd : p.nat_degree using nat.strong_induction_on with i hi generalizing p,
    intros hp,
    dsimp at hi, subst hd,
    cases erase_nat_degree_lt_or_zero p with h,

    { replace h := eq_C_of_nat_degree_eq_zero h, rw h,
      obtain ⟨n, hn⟩ := hp 0,
      use n, rw [←C_pow, hn, C_eq_zero] },

    { set p' := p.erase p.nat_degree with p'_def, rw ←p'_def at *,
      have h1 : ∀ n, is_nilpotent (p'.coeff n),
      { intro n,
        cases erase_coeff_eq_orig_or_zero p n with h' h'; rw h',
        { exact is_nilpotent.zero },
        { exact hp n } },
      have h2 := hi p'.nat_degree h p' rfl h1,
      have h3 : is_nilpotent (monomial p.nat_degree p.leading_coeff) :=
        monomial_nilpotent_of_nilpotent (hp p.nat_degree) _,

      rw ←monomial_add_erase p p.nat_degree,
      exact commute.is_nilpotent_add (by exact comm_ring.mul_comm _ _) h3 h2 } }
end

def is_zero_divisor (a : R) : Prop := a ≠ 0 ∧ ∃ b, b ≠ 0 ∧ a * b = 0

theorem polynomial_zero_divisor_iff (p : polynomial R) :
  is_zero_divisor p ↔ ∃ (a : R), a ≠ 0 ∧ a • p = 0 :=
sorry

theorem polynomial_primitive_mul_iff (p q : polynomial R) :
  (p * q).is_primitive ↔ p.is_primitive ∧ q.is_primitive :=
sorry