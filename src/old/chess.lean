import tactic
open classical
local attribute [instance] prop_decidable

structure gamestate (α : Type) :=
-- α represents the type of squares on the chessboard
(left : α → α → Prop)
(white_turn : Prop)
(K : α → Prop)  -- Is the White king on this square?
(k : α → Prop)  -- ...    Black ...
(left_nonrefl : ∀ x y, left x y → x ≠ y)
(left_trans : ∀ x y z, left x y ∧ left y z → left x z)
(square_one_piece_K : ∀ x, K x → ¬ k x)
(square_one_piece_k : ∀ x, k x → ¬ K x)

variables {α : Type} (G : gamestate α)

def adjleft (x y : α) := G.left x y ∧ (∀ z, ¬ G.left x z ∧ ¬ G.left z y)

-- `can'_<color> x y` iff a piece on `x` can
-- 1. reach `y`
-- *or*
-- 2. capture a different-colored piece on `y`
-- *or*
-- 3. protect a same-colored piece on `y`
def can'_white (x y : α) := G.K x ∧ (adjleft G x y ∨ adjleft G y x)
def can'_black (x y : α) := G.k x ∧ (adjleft G x y ∨ adjleft G y x)
def can' (x y : α) := (G.white_turn → can'_white G x y) ∧ (¬ G.white_turn → can'_black G x y)

-- `can_<color> x y` iff only 1 and 2 from above hold
def can_white (x y : α) := G.K x ∧ ¬ G.K y ∧ (adjleft G x y ∨ adjleft G y x)
def can_black (x y : α) := G.k x ∧ ¬ G.k y ∧ (adjleft G x y ∨ adjleft G y x)
def can (x y : α) := (G.white_turn → can_white G x y) ∧ (¬ G.white_turn → can_black G x y)

def checked_white := ∃ (x y : α), G.K y ∧ can_black G x y
def checked_black := ∃ (x y : α), G.k y ∧ can_white G x y
def checked := (G.white_turn → checked_white G) ∧ (¬ G.white_turn → checked_black G)
def checking := (G.white_turn → checked_black G) ∧ (¬ G.white_turn → checked_white G)

def move (x y : α) (h : can G x y) : gamestate α :=
{ left := G.left,
  white_turn := ¬ G.white_turn,
  -- Piece on source square always disappears on next move
  -- Piece on target square only present if it was moved from
  -- source square
  K := λ z, ite (z = x) false
    (ite (z = y) (G.K x) (G.K z)),
  k := λ z, ite (z = x) false
    (ite (z = y) (G.k x) (G.k z)),
  left_nonrefl := G.left_nonrefl,
  left_trans := G.left_trans,
  -- Mindless case bashing lol
  square_one_piece_K := begin
    intros z h1,
    by_contra h2,
    by_cases h3 : z = x,
      exfalso, rwa (if_pos h3) at h1,
    by_cases h4 : z = y;
    rw (if_neg h3) at h1,
    { rw (if_pos h4) at h1,
      rw [if_neg h3, if_pos h4] at h2,
      exact (G.square_one_piece_K x h1) h2 },
    rw (if_neg h4) at h1,
    rw [if_neg h3, if_neg h4] at h2,
    exact (G.square_one_piece_K z h1) h2
  end,
  square_one_piece_k := begin
    intros z h1,
    by_contra h2,
    by_cases h3 : z = x,
      exfalso, rwa (if_pos h3) at h1,
    by_cases h4 : z = y;
    rw (if_neg h3) at h1,
    { rw (if_pos h4) at h1,
      rw [if_neg h3, if_pos h4] at h2,
      exact (G.square_one_piece_k x h1) h2 },
    rw (if_neg h4) at h1,
    rw [if_neg h3, if_neg h4] at h2,
    exact (G.square_one_piece_k z h1) h2
  end }

-- legal moves don't leave the player in check
def legal (x y : α) (h : can G x y) := ¬ checking (move G x y h)
def got_can := ∃ (x y : α), can G x y
def got_legal := ∃ (x y : α) {h : can G x y}, legal G x y h
def stalemated := ¬ checked G ∧ (¬ got_can G ∨ ¬ got_legal G)
def checkmated := checked G ∧ (¬ got_can G ∨ ¬ got_legal G)

def winning : ℕ → gamestate α → Prop
| 0 := λ G, ¬ G.white_turn ∧ checkmated G
| (k+1) := λ G, ¬ stalemated G ∧ got_can G ∧
  (¬ G.white_turn → ∀ (x y : α) {h : can G x y}, legal G x y h ∧ winning k (move G x y h)) ∧
  (G.white_turn → ∃ (x y : α) (h : can G x y), legal G x y h ∧ winning k (move G x y h))

def losing : ℕ → gamestate α → Prop
| 0 := λ G, G.white_turn ∧ checkmated G
| (k+1) := λ G, ¬ stalemated G ∧ got_can G ∧
  (G.white_turn → ∀ (x y : α) {h : can G x y}, legal G x y h ∧ losing k (move G x y h)) ∧
  (¬ G.white_turn → ∃ (x y : α) (h : can G x y), legal G x y h ∧ losing k (move G x y h))

def draw := ∀ (k : ℕ), ¬ winning k G ∧ ¬ losing k G

-- Some basic results
-- When there is only one White/Black king on the board
lemma left_of_adjleft {x y : α} (h : adjleft G x y) : G.left x y := h.left
lemma check_of_checkmate (h : checkmated G) : checked G := h.left

def one_white_piece (x : α) := G.K x ∧ (∀ (z : α), G.K z → z = x)
def one_black_piece (x : α) := G.k x ∧ (∀ (z : α), G.k z → z = x)

lemma adj_of_can {x y : α} (hcan : can G x y) : adjleft G x y ∨ adjleft G y x := begin
  unfold can at hcan,
  by_cases hwhite : G.white_turn,
  { have h1 := hcan.left hwhite,
    unfold can_white at h1,
    exact h1.right.right },
  have h1 := hcan.right hwhite,
  unfold can_black at h1,
  exact h1.right.right,
end

lemma neq_of_adj {x y : α} (h : adjleft G x y ∨ adjleft G y x) : x ≠ y := begin
  cases h,
    exact G.left_nonrefl _ _ h.left,
  exact ne_comm.mp (G.left_nonrefl _ _ h.left),
end

lemma neq_of_can {x y : α} (hcan : can G x y) : x ≠ y := neq_of_adj G (adj_of_can G hcan)

lemma K_of_move {x y : α} (hK : G.K x) (hcan : can G x y) :
  (move G x y hcan).K y := begin
  unfold move, dsimp,
  rwa [if_neg _, if_pos _],
    refl,
  exact ne_comm.mp (neq_of_can G hcan),
end

lemma k_of_move {x y : α} (hk : G.k x) (hcan : can G x y) :
  (move G x y hcan).k y := begin
  unfold move, dsimp,
  rwa [if_neg _, if_pos _],
    refl,
  exact ne_comm.mp (neq_of_can G hcan),
end

lemma K_of_move_2 {x y z : α} (hK : G.K x) (hk : G.k z) (hcan : can G x y)
  (hxz : x ≠ z) (hyz : y ≠ z) : (move G x y hcan).k z := begin
  unfold move, dsimp,
  rwa [if_neg (ne_comm.mp hyz), if_neg (ne_comm.mp hxz)],
end

lemma k_of_move_2 {x y z : α} (hk : G.k x) (hK : G.K z) (hcan : can G x y)
  (hxz : x ≠ z) (hyz : y ≠ z) : (move G x y hcan).K z := begin
  unfold move, dsimp,
  rwa [if_neg (ne_comm.mp hyz), if_neg (ne_comm.mp hxz)],
end

-- Making a move preserves the number of pieces of your color
lemma one_white_piece_preserved_1 {x y : α} (hone : one_white_piece G x) (hcan : can G x y) :
  one_white_piece (move G x y hcan) y := begin
  unfold one_white_piece,
  split,
    exact K_of_move G hone.left hcan,
  intros z hz,
  unfold move at hz, dsimp at hz,
  have hzx : z ≠ x := λ h, by rwa (if_pos h) at hz,
  by_contra h,
  rw [if_neg hzx, if_neg h] at hz,
  exact hzx (hone.right z hz),
end

lemma one_black_piece_preserved_1 {x y : α} (hone : one_black_piece G x) (hcan : can G x y) :
  one_black_piece (move G x y hcan) y := begin
  unfold one_black_piece,
  split,
    exact k_of_move G hone.left hcan,
  intros z hz,
  unfold move at hz, dsimp at hz,
  have hzx : z ≠ x := λ h, by rwa (if_pos h) at hz,
  by_contra h,
  rw [if_neg hzx, if_neg h] at hz,
  exact hzx (hone.right z hz),
end

-- Non-capturing moves by the opponent preserve the number of pieces of your color
lemma one_white_piece_preserved_2 {x y z : α} (hblack : ¬ G.white_turn) (hone : one_white_piece G z)
  (hcan : can G x y) (hyz : y ≠ z) :
  one_white_piece (move G x y hcan) z := begin
  unfold one_white_piece,
  split,
  { unfold move, dsimp,
    by_cases hxz : x = z,
    { subst hxz,
      rw (if_pos rfl),
      have hkx := (hcan.right hblack).left,
      exact G.square_one_piece_K x hone.left hkx },
    rw [if_neg (ne_comm.mp hxz), if_neg (ne_comm.mp hyz)],
    exact hone.left },
  intros w hw,
  unfold move at hw, dsimp at hw,
  rw [if_neg _, if_neg _] at hw,
  exact hone.right w hw,
  { by_contra h1,
    rw (if_pos h1) at hw,
    have h2 := (hcan.right hblack).left,
    exact G.square_one_piece_K x hw h2 },
  by_contra h1,
  rwa (if_pos h1) at hw,
end

lemma one_black_piece_preserved_2 {x y z : α} (hwhite : G.white_turn) (hone : one_black_piece G z)
  (hcan : can G x y) (hyz : y ≠ z) :
  one_black_piece (move G x y hcan) z := begin
  unfold one_black_piece,
  split,
  { unfold move, dsimp,
    by_cases hxz : x = z,
    { subst hxz,
      rw (if_pos rfl),
      have hkx := (hcan.left hwhite).left,
      exact G.square_one_piece_k x hone.left hkx },
    rw [if_neg (ne_comm.mp hxz), if_neg (ne_comm.mp hyz)],
    exact hone.left },
  intros w hw,
  unfold move at hw, dsimp at hw,
  rw [if_neg _, if_neg _] at hw,
  exact hone.right w hw,
  { by_contra h1,
    rw (if_pos h1) at hw,
    have h2 := (hcan.left hwhite).left,
    exact G.square_one_piece_k x hw h2 },
  by_contra h1,
  rwa (if_pos h1) at hw,
end

lemma adj_of_move {x y : α} (hcan : can G x y) : adjleft G x y ∨ adjleft G y x := begin
  by_cases hwhite : G.white_turn,
    exact (hcan.left hwhite).right.right,
  exact (hcan.right hwhite).right.right,
end

-- Define a `KvK position` to be a position with only one non-adjacent White and Black king
-- I show that KvK positions are draws
def KvK := ∃ (x y : α), one_white_piece G x ∧ one_black_piece G y ∧ ¬ adjleft G x y ∧ ¬ adjleft G y x

-- 1. A KvK position is a check for neither player
lemma KvK_no_check (h : KvK G) : ¬ checked G :=
begin
  unfold checked,
  simp only [not_and_distrib, not_not, not_imp],
  by_cases hturn : G.white_turn,
  { left, split,
      assumption,
    unfold checked_white,
    simp only [not_exists, not_and_distrib],
    intros y x,

    by_cases hK : G.K x, swap,
      left, assumption,
    right,
    unfold can_black,
    simp only [not_and_distrib, not_not, not_or_distrib],
    
    by_cases hk : G.k y, swap,
      left, assumption,
    right, right,
    rcases h with ⟨x', y', hx', hy', hnotadj⟩,
    rw and_comm at hnotadj,
    convert hnotadj,
    repeat { exact hy'.right y hk <|> exact hx'.right x hK } },

  -- The same thing
  right, split,
    assumption,
  unfold checked_black,
  simp only [not_exists, not_and_distrib],
  intros x y,

  by_cases hk : G.k y, swap,
    left, assumption,
  right,
  unfold can_white,
  simp only [not_and_distrib, not_not, not_or_distrib],
  
  by_cases hK : G.K x, swap,
    left, assumption,
  right, right,
  rcases h with ⟨x', y', hx', hy', hnotadj⟩,
  convert hnotadj,
  repeat { exact hy'.right y hk <|> exact hx'.right x hK },
end

-- 2. Legal moves preserve KvK positions
lemma KvK_preserved {x y : α} (hG : KvK G) (hcan : can G x y) (hlegal : legal G x y hcan) :
  KvK (move G x y hcan) :=
begin
  rcases hG with ⟨x1, x2, hx1, hx2, hnotadj⟩,
  unfold KvK,
  by_cases hwhite : G.white_turn,
  { have : x = x1 := hx1.right x (hcan.left hwhite).left,
    subst this,

    have hy_x2 : y ≠ x2 := begin
      by_contra h, subst h,
      apply not_or_distrib.mpr hnotadj,
      exact adj_of_move G hcan,
    end,

    use [y, x2],
    split,
    { apply one_white_piece_preserved_1,
      convert hx1 },
    split,
    { apply one_black_piece_preserved_2,
      repeat { assumption } },

    let G' := move G x y hcan,
    -- Expanding the monstrous expression out
    rename hlegal h1,
    unfold legal checking checked_white checked_black can_white can_black at h1,
    simp only [not_and_distrib, not_imp, not_not] at h1,
    cases h1,
      exact false.elim (not_not.mpr hwhite h1.left),
    replace h1 := h1.right,
    simp only [not_exists, not_and_distrib, not_not, not_or_distrib] at h1,
    replace h1 := h1 x2 y,
    cases h1,
      exact false.elim (h1 (K_of_move G hx1.left hcan)),
    cases h1,
    { refine false.elim (h1 (K_of_move_2 G hx1.left hx2.left hcan _ hy_x2)),
      by_contra h2,
      subst h2,
      exact (G.square_one_piece_K x hx1.left) hx2.left },
    cases h1,
    { refine false.elim ((G'.square_one_piece_K y _) h1),
      apply K_of_move G hx1.left },
    rwa and_comm },

  -- EXACT SAME THING
  have : x = x2 := hx2.right x (hcan.right hwhite).left,
  subst this,

  have hy_x2 : y ≠ x1 := begin
    by_contra h, subst h,
    apply not_or_distrib.mpr hnotadj,
    rw or_comm,
    exact adj_of_move G hcan,
  end,

  use [x1, y],
  split,
  { apply one_white_piece_preserved_2,
    repeat { assumption } },
  split,
  { apply one_black_piece_preserved_1,
    assumption },

  let G' := move G x y hcan,
  have : G'.white_turn := hwhite,
  -- Expanding the monstrous expression out
  rename hlegal h1,
  unfold legal checking checked_white checked_black can_white can_black at h1,
  simp only [not_and_distrib, not_imp, not_not] at h1,
  cases h1, swap,
    exact false.elim (h1.left this),
  replace h1 := h1.right,
  simp only [not_exists, not_and_distrib, not_not, not_or_distrib] at h1,
  replace h1 := h1 x1 y,
  cases h1,
    exact false.elim (h1 (k_of_move G hx2.left hcan)),
  cases h1,
  { refine false.elim (h1 (k_of_move_2 G hx2.left hx1.left hcan _ hy_x2)),
    by_contra h2,
    subst h2,
    exact (G.square_one_piece_K x hx1.left) hx2.left },
  cases h1,
  { refine false.elim ((G'.square_one_piece_k y _) h1),
    apply k_of_move G hx2.left },
  assumption,
end

-- The main result
theorem KvK_draw (h : KvK G) : draw G := begin
  unfold draw, intro k, revert G,
  induction k with k hk; intros G hG,
  { split,
    { unfold winning,
      rw [not_and_distrib, not_not],
      right,
      exact (λ h, (KvK_no_check G hG) (check_of_checkmate G h)) },
    unfold losing,
    rw not_and_distrib,
    right,
    exact (λ h, (KvK_no_check G hG) (check_of_checkmate G h)) },

  split,
  { unfold winning,
    simp only [not_and_distrib, not_not, not_imp, not_forall, not_exists],
    by_cases h1 : stalemated G,
      left, assumption,
    right,

    by_cases h2 : G.white_turn,
    { right, right,
      use h2,
      intros x y hcan,
      by_cases h3 : legal G x y _, swap,
        left, assumption,
      right,
      let G' := move G x y _,
      exact (hk G' (KvK_preserved G hG hcan h3)).left },

    by_cases h3 : got_can G, swap,
      left, assumption, 
    right, left,
    rcases h3 with ⟨x, y, hxy⟩,
    use [h2, x, y, hxy],

    by_cases h4 : legal G x y _, swap,
      left, assumption,
    right,
    let G' := move G x y _,
    exact (hk G' (KvK_preserved G hG hxy h4)).left, },

  -- The exact same thing but replace `winning` with `losing`
  unfold losing,
  simp only [not_and_distrib, not_not, not_imp, not_forall, not_exists],
  by_cases h1 : stalemated G,
    left, assumption,
  right,

  by_cases h2 : G.white_turn, swap,
  { right, right,
    use h2,
    intros x y hcan,
    by_cases h3 : legal G x y _, swap,
      left, assumption,
    right,
    let G' := move G x y _,
    exact (hk G' (KvK_preserved G hG hcan h3)).right },

  by_cases h3 : got_can G, swap,
    left, assumption, 
  right, left,
  rcases h3 with ⟨x, y, hxy⟩,
  use [h2, x, y, hxy],

  by_cases h4 : legal G x y _, swap,
    left, assumption,
  right,
  let G' := move G x y _,
  exact (hk G' (KvK_preserved G hG hxy h4)).right
end