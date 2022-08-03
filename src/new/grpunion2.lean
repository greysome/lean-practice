import group_theory.subgroup.basic

universe u

#reduce subgroup.complete_lattice.lt
-- A group is not a union of two proper subgroups
theorem ne_union_of_proper {G : Type u} [group G] (S K : subgroup G) (hS : S < ⊤) (hK : K < ⊤) :
  (S : set G) ∪ K ≠ ⊤ :=
begin
  replace hS := hS.right,
  replace hK := hK.right,
  simp only [subgroup.coe_top, set.subset_def, set.mem_univ, true_implies_iff, not_forall] at hS hK,

  assume hunion,
  simp only [set.ext_iff, set.top_eq_univ, set.mem_univ, set.mem_union, iff_true] at hunion,

  have h1 : ∃ (g : G), g ∈ S ∧ g ∉ K := by {
    apply not_not.mp,
    simp only [not_exists, not_and_distrib, not_not],
    by_contra h,
    have : ∀ (g : G), g ∈ K := λ g,
      or.elim (h g) (λ h, or_iff_not_imp_left.mp (hunion g) h) id,
    exact not_forall.mpr hK this,
  },
  have h2 : ∃ (g : G), g ∈ K ∧ g ∉ S := by {
    apply not_not.mp,
    simp only [not_exists, not_and_distrib, not_not],
    by_contra h,
    have : ∀ (g : G), g ∈ S := λ g,
      or.elim (h g) (λ h, or_iff_not_imp_right.mp (hunion g) h) id,
    exact not_forall.mpr hS this
  },

  let x := h1.some * h2.some,
  suffices h3 : x ∉ S ∧ x ∉ K,
  simp_rw ←not_or_distrib at h3,
  exact absurd (hunion x) h3,

  split,
  exact λ h, absurd
    ((mul_mem_cancel_left h1.some_spec.left).mp h)
    h2.some_spec.right,
  exact λ h, absurd
    ((mul_mem_cancel_right h2.some_spec.left).mp h)
    h1.some_spec.right,
end

-- Kenny Lau's super short solution
theorem ne_union_of_proper2 {G : Type u} [group G] (S K : subgroup G) (hS : S < ⊤) (hK : K < ⊤) :
  (S : set G) ∪ K ≠ ⊤ :=
begin
  intro h, simp [set.ext_iff] at h,
  obtain ⟨x, _, hxs⟩ := set_like.exists_of_lt hS,
  obtain ⟨y, _, hyk⟩ := set_like.exists_of_lt hK,
  cases h (x * y) with hs hk,
  { exact hxs ((subgroup.mul_mem_cancel_right S $ (h y).resolve_right hyk).1 hs) },
  { exact hyk ((subgroup.mul_mem_cancel_left K $ (h x).resolve_left hxs).1 hk) }
end