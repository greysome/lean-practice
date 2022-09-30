import tactic
import data.set.basic

-- Usually a family of sets is represented as a term
-- `f: F → set α`, but this leads to difficulties
-- composing `cl` twice. Thus I represent a family of sets
-- as a term of type `set (set α)` at the outset.

-- Writing out the definition is half the problem solved.
def cl {α : Type*} (F : set (set α)) : set (set α) :=
  {S : set α | ∃ (X ∈ F), S ⊆ X}

example {α : Type*} (F : set (set α)) : cl (cl F) = cl F :=
begin
  ext, split; intros hx,
  { obtain ⟨S, hS, hxS⟩ := hx,
    obtain ⟨T, hT, hST⟩ := hS,
    use T,
    exact ⟨hT, subset_trans hxS hST⟩ },
  { obtain ⟨S, hS, hxS⟩ := hx,
    use S,
    exact ⟨exists.intro S ⟨hS, subset_refl _⟩, hxS⟩ }
end