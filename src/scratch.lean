import data.set
import tactic
import data.fintype.basic

open set

-- ι n = [0,1,2,...,n-1]
def ι : ℕ → list ℕ
| 0 := []
| (n+1) := append (ι n) [n]

def list.to_set {X} : list X → set X
| [] := ∅
| (x::xs) := {x} ∪ list.to_set xs

protected
lemma nat_well_ordered {P : ℕ → Prop} (n : ℕ) (pn : P n) : (∃ m, P m ∧ ∀ k, P k → k ≥ m)
:= begin
  set A := {n | P n} with Aeq,
  have Asup := well_founded.has_min nat.lt_wf A ⟨n, pn⟩,
  rcases Asup with ⟨m, m_in, Asup⟩,
  use [m, m_in],
  intros k pk,
  specialize Asup k pk,
  have r : nat.lt = has_lt.lt, refl,
  rw r at Asup, linarith,
end
