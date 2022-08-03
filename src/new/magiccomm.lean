universe u

structure is_magical {α : Type u} (f : α → α → α) :=
  (left : ∀ x y, f (f x y) y = x)
  (right : ∀ x y, f y (f y x) = x)

-- the proof: ab = (b(ba))b = (b(ba))((b(ba))(ba)) = ba
theorem magic_is_comm {α : Type u} (f : α → α → α) (hf : is_magical f) :
  is_commutative α f :=
⟨λ a b, by { conv {
  to_lhs, congr,
  rw ←hf.right a b, skip,
  rw ←hf.left b (f b a),
}, rw hf.right }⟩