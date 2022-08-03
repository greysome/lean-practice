import data.fintype.basic
import algebra.group.defs
import algebra.hom.group
import group_theory.subgroup.basic
import group_theory.order_of_element
import tactic

variables {G : Type*} [group G] [fintype G]

variable (G)
def cubedistr_prop : Prop := ∀ (a b : G), (a * b) ^ 3 = a ^ 3 * b ^ 3

variable {G}

lemma pow_three (a : G) : a ^ 3 = a * a * a := by group

lemma sq_antihom (cubedistr : cubedistr_prop G) (a b : G) :
  (a * b) ^ 2 = b ^ 2 * a ^ 2 :=
calc (a * b) ^ 2 = a * b * a * b : by {rw pow_two, group}
... = b⁻¹ * ((b * a) * (b * a) * (b * a)) * a⁻¹ : by group
... = b⁻¹ * (b * a) ^ 3 * a⁻¹ : by rw pow_three
... = b⁻¹ * (b ^ 3 * a ^ 3) * a⁻¹ : by rw cubedistr 
... = b ^ 2 * a ^ 2 : by group

lemma sqcube_comm (cubedistr : cubedistr_prop G) (a b : G) :
  a ^ 2 * b ^ 3 = b ^ 3 * a ^ 2 :=
calc a ^ 2 * b ^ 3 = a ^ 2 * b ^ 2 * b * a * a⁻¹ : by group
... = (b * a) * (b * a) * (b * a) * a⁻¹ : by {rw [←sq_antihom cubedistr, pow_two], group}
... = (b * a) ^ 3 * a⁻¹ : by rw pow_three
... = b ^ 3 * a ^ 3 * a⁻¹ : by rw cubedistr
... = b ^ 3 * a ^ 2 : by group

-- If G is a finite group such that (xy)^3 = x^3y^3 and 3 ∤ |G|, then G is abelian.
theorem comm_of_cubehom_group (cubedistr : cubedistr_prop G)
  (hord : ¬3 ∣ fintype.card G) :
  ∀ (a b : G), a * b = b * a :=
begin
  set cubehom : G →* G := {
    to_fun := λ x, x ^ 3,
    map_one' := by group,
    map_mul' := cubedistr,
  } with hcubehom,

  have hinj : function.injective ⇑cubehom := by {
    simp_rw [←monoid_hom.ker_eq_bot_iff, subgroup.eq_bot_iff_forall,
      monoid_hom.mem_ker, hcubehom],
    intros x hx,
    by_contra h,
    exact hord (order_of_eq_prime hx h ▸ order_of_dvd_card_univ),
  },
  have hsur : function.surjective ⇑cubehom := fintype.injective_iff_surjective.mp hinj,
  
  have sqcomm' : ∀ (a b : G), a ^ 2 * b = b * a ^ 2 := by {
    intros a b,
    obtain ⟨t, ht⟩ := hsur b,
    dsimp [hcubehom] at ht, subst ht,
    exact sqcube_comm cubedistr a t,
  },

  have sqcomm : ∀ (a b : G), a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 :=
    λ a b, calc a ^ 2 * b ^ 2 = a ^ 2 * b * b : by group
    ... = b * a ^ 2 * b : by rw sqcomm'
    ... = b * (a ^ 2 * b) : mul_assoc _ _ _
    ... = b * (b * a ^ 2) : by rw sqcomm'
    ... = b ^ 2 * a ^ 2 : by group,

  intros a b,
  calc a * b = a⁻¹ * (a ^ 2 * b ^ 2) * b⁻¹ : by group
  ... = a⁻¹ * (b ^ 2 * a ^ 2) * b⁻¹ : by rw sqcomm
  ... = a⁻¹ * (a * b) ^ 2 * b⁻¹ : by rw sq_antihom cubedistr
  ... = a⁻¹ * a * b * a * b * b⁻¹ : by {rw pow_two, group}
  ... = b * a : by group
end