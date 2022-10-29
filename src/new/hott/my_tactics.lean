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

end hott


namespace tactic
namespace interactive
setup_tactic_parser

-- Path induction tactic
meta def pinduction (a b h : parse ident) : tactic unit :=
do hott.pinduction_aux a b h

end interactive
end tactic