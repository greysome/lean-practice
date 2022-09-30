import tactic
open classical
local attribute [instance] prop_decidable

-- The code is very very messy...

noncomputable def truthteller : Prop → bool := λ P, if P then tt else ff
noncomputable def liar : Prop → bool := λ P, if P then ff else tt

lemma aux1 (P : Prop) : liar P = ! truthteller P :=
match classical.prop_decidable P with
| (is_true hP) := by calc liar P = ff : if_pos hP
    ... = ! tt : rfl
    ... = ! truthteller P : by unfold truthteller; rw (if_pos hP)
| (is_false hnP) := by calc liar P = tt : if_neg hnP
    ... = ! ff : rfl
    ... = ! truthteller P : by unfold truthteller; rw (if_neg hnP)
end

theorem solution (f : Prop → bool) (hf : f = truthteller ∨ f = liar)
  (P : Prop) : ∃ (Q : Prop), f Q = truthteller P :=
begin
  use [f P = tt],
  by_cases P,
  { have x : truthteller P = tt := @if_pos P _ h _ tt ff,
    cases hf; rw hf,
    { have y : truthteller (truthteller P = tt) = tt := @if_pos (truthteller P = tt) _ x _ tt ff,
      exact eq.trans y (eq.symm x),},
    { have x' : ¬ liar P = tt := by rwa [aux1, bool.bnot_not_eq],
      have y : liar (liar P = tt) = tt := @if_neg (liar P = tt) _ x' _ ff tt,
      exact eq.trans y (eq.symm x)}},
  have x : truthteller P = ff := if_neg h,
  cases hf; rw hf,
  { have x' : ¬ truthteller P = tt := (@bool.not_eq_bnot (truthteller P) ff).mpr x,
    have y : truthteller (truthteller P = tt) = ff := if_neg x',
    exact eq.trans y (eq.symm x)},
  { have z : liar P = tt := if_neg h,
    have y : liar (liar P = tt) = ff := if_pos z,
    exact eq.trans y (eq.symm x)}
end