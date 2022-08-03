import data.real.basic data.set.intervals.basic

open set

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

theorem continuous_function_about_an_open_interval {f a}
  (hcont : continuous_at f a) (hgt : f a > 0) :
  ∃ b c : ℝ, a ∈ Ioo b c ∧ ∀ x ∈ Ioo b c, f x > 0 := begin
  obtain ⟨δ, δpos, hδ⟩ := hcont (f a / 2) (half_pos hgt),
  use [a-δ, a+δ],
  split, 
    split; by {norm_num, assumption},

  intros x hx1,
  have hx2 : |x - a| < δ := by {
    rw abs_sub_lt_iff,
    dsimp [Ioo] at hx1,
    split; linarith,
  },
  have hfx := hδ x hx2,
  cases abs_sub_lt_iff.mp hfx with hfx1 hfx2,
  linarith [hfx2],
end