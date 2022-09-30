import tactic
import data.nat.parity

example : ∃ (α : Type*) (P Q R : set α),
  (∀ x, P x → (Q x ∨ R x)) ∧ ¬ ((∀ x, P x → Q x) ∨ (∀ x, P x → R x)) :=
begin
  use [ℕ, set.univ, even, odd],
  split,
  { exact λ x _, nat.even_or_odd x },
  { push_neg,
    exact ⟨exists.intro 1 (by norm_num), exists.intro 0 (by norm_num)⟩ }
end