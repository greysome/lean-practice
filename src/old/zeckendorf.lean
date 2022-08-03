import data.nat.fib
import data.fin.tuple
import data.fintype.card
import algebra.big_operators.basic
import algebra.big_operators.order
open_locale big_operators
open classical nat
local attribute [instance] prop_decidable

def is_zeckendorf_rep {k : ℕ} (kpos : k > 0) (f : fin k → ℕ) : Prop :=
  f ⟨0, kpos⟩ > 1 ∧ ∀ m n, m > n → f m > f n + 1

def has_zeckendorf_rep (n : ℕ) := 
  ∃ (k : ℕ) (kpos : k > 0) (f : fin k → ℕ),
    is_zeckendorf_rep kpos f ∧ ∑ (i : fin k), fib (f i) = n

lemma trivial_rep_is_zeckendorf (f : fin 1 → ℕ) (h : f ⟨0, by norm_num⟩ > 1) :
  is_zeckendorf_rep (by norm_num) f :=
begin
  split,
  { assumption },
  { intros m n hinductn,
    exfalso,
    have hinduct0 : m = 0 := fin.eq_zero m,
    have hn0 : n = 0 := fin.eq_zero n,
    subst hn0,
    exact (ne_of_gt hinductn) hinduct0, }
end

lemma fib_three : fib 3 = 2 := begin
  rw fib_succ_succ, ring
end

lemma eq_last_of_not_lt {k : ℕ} {m : fin k.succ} (h : ¬↑m < k) : ↑m = k :=
  le_antisymm (fin.is_le m) (le_of_not_gt h)

lemma fib_inv_strict_mono {m n : ℕ} (h : fib m < fib n) : m < n :=
begin
  by_contra h1, exact not_lt.mpr (fib_mono (not_lt.mp h1)) h,
end

theorem zeckendorf_existence (n : ℕ) : n > 0 → has_zeckendorf_rep n :=
begin
  apply nat.strong_induction_on n,
  clear n,
  intros n hinduct hn,

  -- Trivial cases
  by_cases n_eq_0 : n = 0,
  { exfalso, exact (ne_of_gt hn) n_eq_0 },
  
  by_cases n_eq_1 : n = 1,
  { use [1, by norm_num, (λ i, 2)], -- 1 = fib 2
    split,
    { exact trivial_rep_is_zeckendorf _ (by norm_num) },
    { rw [fintype.sum_unique, n_eq_1, fib_two] } },

  by_cases n_eq_2 : n = 2,
  { use [1, by norm_num, (λ i, 3)], -- 2 = fib 3
    split,
    { exact trivial_rep_is_zeckendorf _ (by norm_num) },
    { rw [fintype.sum_unique, n_eq_2, fib_three] } },

  -- Induction step
  have n_ge_2 : n > 2,
  { refine lt_of_le_of_ne _ (ne.symm n_eq_2),
    rw nat.succ_le_iff,
    refine lt_of_le_of_ne _ (ne.symm n_eq_1),
    rw nat.succ_le_iff,
    rwa pos_iff_ne_zero },
  clear n_eq_0 n_eq_1 n_eq_2,

  set fibs := λ i, ∃ k, i = fib k with hfibs,
  -- F = fib l is the greatest Fibonacci number ≤ n
  set F := nat.find_greatest fibs n with hF,

  have two_le_F : 2 ≤ F,
  { refine nat.le_find_greatest (le_of_lt n_ge_2) _,
    use 3, rw fib_three },
  have : ∃ m, m ≤ n ∧ ∃ k, m = fib k,
    use [1, one_le_of_lt n_ge_2, 1], rw fib_one,
  have F_fib := nat.find_greatest_spec this,
  clear this,
  cases F_fib with l hl,

  have l_gt_1 : l > 1,
  { by_contra h,
    replace h := fib_mono (not_lt.mp h),
    rw [fib_one, ←hl, ←hfibs, ←hF] at h,
    replace h := not_lt.mpr h,
    exact h (succ_le_iff.mp two_le_F) },

  have nF_lt_n : n - F < n,
  { refine nat.sub_lt _ (nat.succ_le_iff.mp (le_of_succ_le two_le_F)),
    exact pos_of_gt n_ge_2 },
  have F_le_n : F ≤ n := nat.find_greatest_le,
  have hnF := hinduct (n - F) nF_lt_n,

  cases hnF with nF0 hnF,
  -- n = F is a Fibonacci number, thus has trivial Zeckendorf representation
  { have n_eq_F : n = F :=
      nat.le_antisymm (nat.le_of_sub_eq_zero nF0) F_le_n,
    clear nF_lt_n nF0,

    use [1, by norm_num, (λ i, l)],
    split,
    { exact trivial_rep_is_zeckendorf _ l_gt_1 },
    { rw fintype.sum_unique, rw [n_eq_F, ←hl] } },

  -- Otherwise, add F to the Zeckendorf representation of n - F
  { rcases hnF with ⟨k, kpos, f, ⟨f0, frest⟩, fsum⟩,
    use [k.succ, succ_pos k,
      λ (i : fin k.succ), if h : ↑i < k then f (i.cast_lt h) else l],
    split,
    -- This is indeed a Zeckendorf representation
    { split,
      { convert f0, dsimp, rw dif_pos, refl },
      { intros m' n' hinductn',
        change n' < m' at hinductn',
        dsimp,
        split_ifs with h1 h2 h3,

        -- n < m < k → use the hypothesis
        { apply frest,
          change n'.cast_lt h2 < m'.cast_lt h1,
          rwa fin.lt_iff_coe_lt_coe at ⊢ hinductn' },

        -- m > n, m < k = n → contradiction
        { exfalso,
          rw fin.lt_iff_coe_lt_coe at hinductn',
          have : ¬↑n' < ↑m' := nat.lt_asymm (nat.lt_of_lt_of_le h1 (not_lt.mp h2)),
          exact this hinductn' },

        -- n < k = m → the interesting case
        { have ha : n-F < fib (l-1),
          { by_contra h,
            replace h := not_lt.mp h,
            rw ←nat.add_le_to_le_sub (fib (l-1)) F_le_n at h,
            rw [hF, hfibs, hl] at h,
            have l_sub_add : l-1+1 = l := nat.sub_add_cancel (le_of_lt l_gt_1),
            conv_lhs at h { congr, skip, rw ←l_sub_add },
            rw ←fib_succ_succ at h,
            change fib (l-1+1).succ ≤ n at h,
            rw (succ_inj'.mpr l_sub_add) at h,

            have contra : fib l.succ ≤ nat.find_greatest fibs n :=
              nat.le_find_greatest h (by use l.succ),
            rw [hfibs, hl, ←nat.sub_add_cancel l_gt_1] at contra,
            replace contra := not_lt_of_le contra,
            exact contra (fib_add_two_strict_mono (lt_add_one (l - 2))) },

          have hb : fib (f (n'.cast_lt h3)) < fib (l-1),
          { suffices h : fib (f (n'.cast_lt h3)) ≤ n - F,
            exact gt_of_gt_of_ge ha h,
            
            rw ←fsum,
            change (fib ∘ f) (n'.cast_lt h3) ≤ ∑ (i : fin k), (fib ∘ f) i,
            refine finset.single_le_sum _ _,
            { intros i hi_univ,
              change fib (f i) ≥ 0,
              exact zero_le _ },
            apply finset.mem_univ },
          
          replace hb := fib_inv_strict_mono hb,
          exact lt_tsub_iff_right.mp hb },

        -- m > n, m = k, n = k → contradiction
        { exfalso,
          replace h1 := eq_last_of_not_lt h1,
          replace h3 := eq_last_of_not_lt h3,
          rw fin.lt_iff_coe_lt_coe at hinductn',
          rw [h1, h3] at hinductn',
          exact nat.lt_asymm hinductn' hinductn' } } },

    -- It sums up to n
    { rw [←nat.sub_add_cancel F_le_n, ←fsum, hF, hfibs, hl],
      rw fin.sum_univ_cast_succ,
      dsimp,
      have sum_eq_of_eqs : ∀ (a b c d : ℕ), a = c → b = d → a + b = c + d,
        intros a b c d hac hbd, rw [hac, ←hbd],
      apply sum_eq_of_eqs,
      { refine fintype.sum_equiv (equiv.cast rfl) _ _ _,
        intro x, rw dif_pos, simp, apply fin.is_lt },
      { rw dif_neg, apply irrefl } } }
end