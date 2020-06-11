import tactic
import data.option.basic

namespace option

instance coe_option {A B} [has_lift_t A B]: has_lift_t (option A) (option B)
:= ⟨λ (x : option A), x.map (λ a, ↑a)⟩

@[norm_cast]
lemma coe_option_get_or_else {A B} [has_lift_t A B] (o : option A) (a : A)
: (↑(o.get_or_else a) : B) = ((↑o : option B).get_or_else (↑a : B))
:= begin cases o, simpa, simpa, end


end option
