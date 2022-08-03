import data.quot
import group_theory.subgroup.basic
import group_theory.quotient_group
import group_theory.specific_groups.cyclic
import tactic

variables {G : Type*} [group G]

variable (G)
-- Extra practice: rolling out my own definition of the center of a subgroup
def center : subgroup G :=
{ carrier := {g : G | ∀ (x : G), g * x = x * g},
  one_mem' := λ x, by group,
  mul_mem' := λ a b ha hb x, by conv_lhs {rw [ha b, mul_assoc, hb (a * x), ha x, mul_assoc]},
  inv_mem' := λ g hg x, begin
    apply (@mul_left_cancel G _ g _ _),
    apply (@mul_right_cancel G _ _ g _),
    simp [hg (x * g⁻¹)],
  end }

variable {G}
-- I'll use Lean's definition of a normal subgroup for convenience
instance center_normal : (center G).normal :=
⟨λ n hn g x, begin
  conv_lhs {rw [←hn g]},
  conv_rhs {rw [←hn g]},
  simp [hn x],
end⟩

-- Back to the original problem: if G/Z(G) is cyclic then G is abelian
-- Here I'll use the `subgroup.center` provided in the library instead of my own
theorem comm_of_quot_center_cyclic (hG : is_cyclic (G ⧸ subgroup.center G)) :
  ∀ (a b : G), a * b = b * a :=
begin
  intros a b,
  obtain ⟨gbar, h_gbar⟩ := hG.exists_generator,
  let g := quotient.out' gbar,
  simp_rw subgroup.mem_zpowers_iff at h_gbar,

  have h1 : ∀ (x : G), ∃ (y ∈ subgroup.center G) (k : ℤ), x = g ^ k * y := by {
    intro x,
    obtain ⟨k, hk⟩ := h_gbar x,
    have hh1 : ↑(g ^ k) = gbar ^ k := by {
      rw quotient_group.coe_zpow,
      congr,
      rw ←quotient.out_eq' gbar, refl
    },
    rw [←hh1, quotient_group.eq_iff_div_mem] at hk,

    have hh2 : x / g ^ k ∈ subgroup.center G := by rwa [←inv_div, inv_mem_iff],
    use x / g ^ k, split,
      assumption,
    use k,
    simp [hh2 (g ^ k)],
  },

  obtain ⟨ya, ha1, ka, ha2⟩ := h1 a,
  obtain ⟨yb, hb1, kb, hb2⟩ := h1 b,
  rw [ha2, hb2],
  calc g ^ ka * ya * (g ^ kb * yb) = g ^ ka * (ya * g ^ kb) * yb : by group
  ... = g ^ ka * (g ^ kb * ya) * yb : by rw ha1 _
  ... = g ^ ka * g ^ kb * (ya * yb) : by group
  ... = g ^ kb * g ^ ka * (yb * ya) : by {rw [ha1 _], group}
  ... = g ^ kb * (g ^ ka * yb) * ya : by group
  ... = g ^ kb * (yb * g ^ ka) * ya : by rw hb1 _
  ... = g ^ kb * yb * (g ^ ka * ya) : by group
end