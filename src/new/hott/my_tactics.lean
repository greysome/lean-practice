prelude
import tactic
import .bootstrap
open tactic expr

namespace hott
open_locale hott

meta def spamrfl_aux : expr → tactic unit
| (pi _ _ _ _) := do
  get_unused_name >>= intro,
  target >>= spamrfl_aux
| `(_ = _) := do refine ``(rfl) <|> fail "rfl failed"
| _ := fail "target type must be a Π-expression or hott.Eq"

-- Like the tactic `refl` but also eliminates Π-binders
meta def spamrfl : tactic unit :=
do target >>= spamrfl_aux, skip

meta def pinduction_aux (a b h : name) : tactic unit :=
do
  e ← resolve_name h,
  e ← to_expr e,
  tp ← infer_type e,
  match tp with
  | `(%%lhs = %%rhs) := do
    lhs_tp ← infer_type lhs,
    a ← resolve_name a,
    b ← resolve_name b,
    refine ``(@Eq.ind_on %%lhs_tp _ %%a %%b %%e _),
    skip
  | _ := fail "argument is not an equality"
  end

-- HoTT-style `rw`
-- If `lhs_or_rhs` is none then rewrite LHS, else rewrite RHS.
-- Note this is a *lot* less powerful than the actual `rw`, because
-- I haven't figured out how they programmed in.
meta def hrw_aux (e : expr) (lhs_or_rhs : option name) : tactic unit :=
do
  match lhs_or_rhs with
  | some _ := do refine ``(_ ⬝ %%e), refine ``(rfl) <|> skip, skip
  | none := do refine ``(%%e ⬝ _), refine ``(rfl) <|> skip, skip
  end

-- HoTT-style `apply`
-- A *lot* less powerful than the actual `apply`
meta def happ_aux (e : expr) : tactic unit :=
do refine ``(%%e ▸ _),
  refine ``(rfl) <|> skip,
  skip

end hott


namespace tactic
namespace interactive
setup_tactic_parser

-- Path induction tactic
meta def pinduction (a b h : parse ident) : tactic unit :=
do hott.pinduction_aux a b h

meta def hrw (e : parse parser.pexpr) (lhs_or_rhs : parse ident?)
  : tactic unit :=
do e ← to_expr e, hott.hrw_aux e lhs_or_rhs

meta def happ (e : parse parser.pexpr) : tactic unit :=
do e ← to_expr e, hott.happ_aux e

end interactive
end tactic