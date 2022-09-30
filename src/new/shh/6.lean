import data.real.irrational

lemma avg_between {a b : ℝ} (hab : a < b) :
  (a + b) / 2 ∈ set.Ioo a b :=
begin
  split,
  { calc a = (a + a) / 2 : by field_simp
    ... < (a + b) / 2 : (div_lt_div_right (by norm_num)).mpr (by linarith) },
  { calc (a + b) / 2 < (b + b) / 2 : (div_lt_div_right (by norm_num)).mpr (by linarith)
    ... = b : by field_simp }
end

example {a b : ℝ} (ha : irrational a) (hb : irrational b) (hab : a < b) :
  ∃ c, irrational c ∧ c ∈ set.Ioo a b :=
begin
  set c := (a + b) / 2,
  let h₁ := avg_between hab,
  by_cases irrational c,
  { exact exists.intro c ⟨h, h₁⟩ },
  { use (a + c) / 2,
    unfold irrational at h,
    push_neg at h,
    obtain ⟨q, hq⟩ := h,
    -- idk an easy way to prove this
    have : ↑(2 : ℕ) = (2 : ℝ) := by simp,
    exact ⟨
      this ▸ hq ▸ irrational.div_nat (irrational.add_rat q ha) two_ne_zero,
      let h₂ := avg_between h₁.1 in ⟨h₂.1, lt_trans h₂.2 h₁.2⟩⟩ },
end