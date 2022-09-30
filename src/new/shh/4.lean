import tactic
import tactic.swap_var
import data.set.basic

-- mathlib defines `symm_diff` in the general context
-- of Heyting algebras, but I choose to roll out my own
-- definition catered to the concrete setting of `set α`.
def symm_diff {α : Type*} (A B : set α) : set α := (A \ B) ∪ (B \ A)

infix ` ∆ `:100 := symm_diff

theorem inter_sdiff {α : Type*} (A B C : set α) :
  A ∩ (B ∆ C) = (A ∩ B) ∆ (A ∩ C) :=
begin
  ext, split; intro hx,
  { cases hx.2,
    work_on_goal 1 { refine or.inl ⟨⟨hx.1, h.1⟩, _⟩ },
    work_on_goal 2 { refine or.inr ⟨⟨hx.1, h.1⟩, _⟩ },
    all_goals { simpa using (λ _, h.2) } },
  { cases hx,
    work_on_goal 1 { refine ⟨hx.1.1, or.inl ⟨hx.1.2, _⟩⟩ },
    work_on_goal 2 { refine ⟨hx.1.1, or.inr ⟨hx.1.2, _⟩⟩ },
    all_goals {
      have h := hx.2,
      rw set.mem_inter_iff at h, push_neg at h,
      exact h hx.1.1
    } }
end

-- Needed for the following result
@[simp]
theorem symm_diff_self {α : Type*} (A : set α) : A ∆ A = ∅ :=
set.ext_iff.mpr (λ x,
  ⟨λ hx, (false.elim $ or.elim hx (λ h, h.2 h.1) (λ h, h.2 h.1)),
  λ hx, (false.elim $ (set.not_mem_empty x) hx)⟩
)

example : ∃ (α : Type*) (A B C : set α),
  A ∪ (B ∆ C) ≠ (A ∪ B) ∆ (A ∪ C) :=
by { use [ℕ, set.univ, set.univ, set.univ], simp }