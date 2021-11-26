import topology.metric_space.basic
open set metric metric_space

variables (M N : Type) (S : set M) [metric_space M] [metric_space N]

theorem uniformly_continuous_of_continuous_of_compact
  (f : M → N) (hS : is_compact S) (hf : continuous f) :
  uniform_continuous_on f S :=
begin
  rw uniform_continuous_on_iff,
  intros ε εpos,

  -- Construct a cover U of S consisting of preimages of all (ε/2)-balls in N
  let U : N → set M := λ q, f ⁻¹' (ball q (ε/2)),
  have Uopen : ∀ q, is_open (U q),
  { intro q,
    rw continuous_def at hf,
    exact hf (ball q (ε/2)) is_open_ball },
  have Ucover : S ⊆ ⋃ i, U i,
  { intros s hs,
    rw mem_Union,
    use f s,
    rw mem_preimage,
    exact mem_ball_self (by linarith)},
  
  -- U has a Lebesgue number δ by compactness of S
  have lebesgue_num := lebesgue_number_lemma_of_metric hS Uopen Ucover,
  rcases lebesgue_num with ⟨δ, δpos, hδ⟩,
  -- This δ is our desired one to prove uniform continuity
  use [δ, δpos],
  intros a b ha hb hab,
  -- Show that `a` and `b` lie in some `U i`
  have h_aball_U := hδ a ha,
  cases h_aball_U with i h_Ui,
  dsimp at h_Ui,
  have h_a_Ui : a ∈ U i := h_Ui (mem_ball_self δpos),
  have h_b_Ui : b ∈ U i,
    rw [←mem_ball, mem_ball_comm] at hab,
    exact h_Ui hab,
  -- Thus `f a` and `f b` lie in the same `ε/2`-ball,
  rw [mem_preimage, mem_ball] at h_a_Ui h_b_Ui,
  -- meaning `dist (f a) (f b) < ε` as desired.
  calc dist (f a) (f b) ≤ dist (f a) i + dist i (f b) : dist_triangle _ _ _
  ... = dist (f a) i + dist (f b) i : by rw dist_comm i (f b)
  ... < ε/2 + ε/2 : by linarith
  ... = ε : by ring,
end
