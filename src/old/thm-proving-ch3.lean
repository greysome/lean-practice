-- First part
variables p q r : Prop
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (λ hpq, ⟨hpq.right, hpq.left⟩)
    (λ hqp, ⟨hqp.right, hqp.left⟩)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (λ hpq, or.elim hpq (λ hp, or.inr hp) (λ hq, or.inl hq))
    (λ hqp, or.elim hqp (λ hq, or.inr hq) (λ hp, or.inl hp))

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (λ hpq_r, ⟨hpq_r.left.left, hpq_r.left.right, hpq_r.right⟩)
    (λ hp_qr, ⟨⟨hp_qr.left, hp_qr.right.left⟩, hp_qr.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (λ hpq_r,
      or.elim hpq_r
        (λ hpq, or.elim hpq
          (λ hp, or.inl hp)
          (λ hq, or.inr (or.inl hq)))
        (λ hr, or.inr (or.inr hr)))
    (λ hp_qr,
      or.elim hp_qr
        (λ hp, or.inl (or.inl hp))
        (λ hqr, or.elim hqr
          (λ hq, or.inl (or.inr hq))
          (λ hr, or.inr hr)))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (λ hp_qr, or.elim hp_qr.right
      (λ hq, or.inl ⟨hp_qr.left, hq⟩)
      (λ hr, or.inr ⟨hp_qr.left, hr⟩))
    (λ hpq_pr, ⟨
      or.elim hpq_pr (λ hpq, hpq.left) (λ hpr, hpr.left),
      or.elim hpq_pr (λ hpq, or.inl hpq.right) (λ hpr, or.inr hpr.right)
    ⟩)
  
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (λ hp_qr, ⟨
      or.elim hp_qr (λ hp, or.inl hp) (λ hqr : q ∧ r, or.inr hqr.left),
      or.elim hp_qr (λ hp, or.inl hp) (λ hqr : q ∧ r, or.inr hqr.right)
    ⟩)
    (λ hpq_pr, or.elim hpq_pr.left
      (λ hp, or.inl hp)
      (λ hq, or.elim hpq_pr.right
        (λ hp, or.inl hp)
        (λ hr, or.inr ⟨hq, hr⟩)))

example : p → (q → r) ↔ (p ∧ q → r) :=
  iff.intro
    (λ hpqr,
      λ hpq, hpqr hpq.left hpq.right)
    (λ hpq_r,
      λ hp, λ hq, hpq_r ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (λ hpq_r,
      ⟨λ hp, hpq_r (or.inl hp),
       λ hq, hpq_r (or.inr hq)⟩)
    (λ hpr_qr,
      (λ hpq, or.elim hpq
        (λ hp, hpr_qr.left hp)
        (λ hq, hpr_qr.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (λ hnpq, ⟨λ hp, hnpq (or.inl hp),
              λ hq, hnpq (or.inr hq)⟩)
    (λ hnp_nq,
      λ hpq, or.elim hpq
        (λ hp, hnp_nq.left hp)
        (λ hq, hnp_nq.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ hnp_nq,
    λ hpq, or.elim hnp_nq
      (λ hnp, hnp hpq.left)
      (λ hnq, hnq hpq.right))

example : ¬(p ∧ ¬p) := λ hp_np, hp_np.right hp_np.left

example : p ∧ ¬q → ¬(p → q) :=
  λ hp_nq, λ hpq, hp_nq.right (hpq hp_nq.left)

example : ¬p → (p → q) := λ hnp, λ hp, false.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  λ hnp_q,
    λ hp, or.elim hnp_q
      (λ hnp, false.elim (hnp hp))
      (λ hq, hq)

example : p ∨ false ↔ p :=
  iff.intro
    (λ hpf, or.elim hpf (λ hp, hp) (λ hf, false.elim hf))
    (λ hp, or.inl hp)

example : p ∧ false ↔ false :=
  iff.intro
    (λ hpf, hpf.right)
    (λ hf, ⟨false.elim hf, hf⟩)

example : (p → q) → (¬q → ¬p) :=
  λ hpq, λ hnq, λ hp, hnq (hpq hp)

-- Second part
open classical
variable s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  λ hp_rs, by_cases
    (λ hp, or.elim (hp_rs hp)
      (λ hr, or.inl (λ hp', hr))
      (λ hs, or.inr (λ hp', hs)))
    (λ hnp, or.inl (λ hp', false.elim (hnp hp')))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ hnpq, by_cases
    (λ hp, or.inr (λ hq, hnpq ⟨hp, hq⟩))
    (λ hnp, or.inl hnp)

-- Brute force
example : ¬(p → q) → p ∧ ¬q :=
  λ hnpq, by_cases
    (λ hp, by_cases
      (λ hq, ⟨hp, false.elim (hnpq (λ hp', hq))⟩)
      (λ hnq, ⟨hp, hnq⟩))
    (λ hnp, by_cases
      (λ hq, ⟨false.elim (hnpq (λ hp', false.elim (hnp hp'))),
              false.elim (hnpq (λ hp', hq))⟩)
      (λ hnq, ⟨false.elim (hnpq (λ hp', false.elim (hnp hp'))), hnq⟩))

example : (p → q) → (¬p ∨ q) :=
  λ hpq, by_cases
    (λ hp, or.inr (hpq hp))
    (λ hnp, or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ hnq_np,
    λ hp, by_cases
      (λ hq, hq)
      (λ hnq, false.elim (hnq_np hnq hp))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  λ hpqp, by_contradiction
    (λ hnp, hnp (hpqp (λ hp, false.elim (hnp hp))))

-- No classical logic
example : ¬(p ↔ ¬p) :=
  λ hp_np,
    have hp : p, from hp_np.mpr (λ hp, hp_np.mp hp hp),
    show false, from hp_np.mp hp hp