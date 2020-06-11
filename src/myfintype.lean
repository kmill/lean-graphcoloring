import data.set
import data.list.basic
import data.vector
import tactic

namespace fintype

instance set.fintype_subtype_lt_nat (n : ℕ) : fintype {i : ℕ // i < n} := set.fintype_lt_nat n

def vector_list_filter_equiv {A} (n : ℕ) (p : list A → Prop)
: {x : vector A n // p x.1} ≃ {x : list A // x.length = n ∧ p x} :=
⟨(λ v, ⟨v.1.1, v.1.2, v.2⟩), (λ ls, ⟨⟨ls.1, ls.2.1⟩, ls.2.2⟩), by rintros ⟨x,h⟩; simp, by rintros ⟨x,h⟩; simp⟩

instance list_sep_fintype {A} [fintype A] (n : ℕ) (p : list A → Prop) [decidable_pred p]
: fintype {x : list A | x.length = n ∧ p x} :=
begin
  change fintype {x : list A // x.length = n ∧ p x},
  exact fintype.of_equiv {x : vector A n // p x.1} (vector_list_filter_equiv n p),
end

end fintype
