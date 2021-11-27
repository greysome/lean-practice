-- The type of each function is a Π-type on α, β and γ
def Do_Twice {α : Type} : (α → α) → α → α :=
  λ f x, f (f x)

def curry {α β γ : Type} (f : α × β → γ) : α → β → γ :=
  λ x, λ y, f (x, y)

def uncurry {α β γ : Type} (f : α → β → γ) : α × β → γ :=
  λ x, f x.fst x.snd

constant vec : Type → ℕ → Type
constant vec_add {n : ℕ} : vec ℕ n → vec ℕ n → vec ℕ n
constant vec_reverse {α : Type} {n : ℕ} : vec α n → vec α n

constant mat : Type → ℕ → ℕ → Type
constant mat_add {n m : ℕ} : mat ℕ n m → mat ℕ n m  → mat ℕ n m
constant mat_mul {n m l : ℕ} : mat ℕ n m → mat ℕ m l → mat ℕ n l
constant mat_mul_vec {n m : ℕ} : mat ℕ n m → vec ℕ m → vec ℕ n