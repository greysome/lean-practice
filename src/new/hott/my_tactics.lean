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
| `(hott.Eq %%a %%b) := do refine ``(rfl)
| _ := skip

-- Like the tactic `refl` but also eliminates Π-binders
meta def spamrfl : tactic unit :=
do target >>= spamrfl_aux, skip

end hott
