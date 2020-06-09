import data.set
import data.finset
import tactic

attribute [instance] classical.prop_decidable

open set finset

namespace finset

lemma inj_range {α} (S : finset α)
: ∃ (f : α → ℕ), (∀ x ∈ S, f x < card S) ∧ (∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
:= begin
  induction S using finset.induction with x S' hasnt ih,
  use (λ y, 0), tauto,
  rcases ih with ⟨f, ih1, ih2⟩,
  set f' := λ y, if y = x then card S' else f y with f'eq,
  use f',
  split, {
    intros y yin,
    rw finset.mem_insert at yin,
    cases yin, {
      rw [yin, card_insert_of_not_mem hasnt],
      dsimp only [f'],
      simp,
    }, {
      specialize ih1 y yin,
      have neq : x ≠ y, by_contradiction, push_neg at a, rw a at hasnt, tauto,
      dsimp only [f'],
      have eqfalse : y = x ↔ false, tauto,
      rw eqfalse, simp,
      linarith [card_insert_of_not_mem hasnt],
    },
  }, {
    intros y₁ yin₁ y₂ yin₂, contrapose, intro neq,
    by_cases h₁ : y₁ = x, {
      rw h₁ at yin₁,
      by_cases h₂ : y₂ = x, {
        rw [h₁, h₂] at neq, tauto,
      }, {
        rw finset.mem_insert at yin₁,
        dsimp only [f'],
        have eqfalse : y₂ = x ↔ false, tauto,
        rw [h₁, eqfalse],
        simp,
        rw finset.mem_insert at yin₂,
        cases yin₂, tauto,
        linarith [ih1 y₂ yin₂],
      }
    }, {
      rw finset.mem_insert at yin₁,
      cases yin₁, tauto,
      have eqfalse : y₁ = x ↔ false, tauto,
      by_cases h₂ : y₂ = x, {
        dsimp only [f'],
        rw [eqfalse, h₂], simp,
        linarith [ih1 y₁ yin₁],
      }, {
        rw finset.mem_insert at yin₂, cases yin₂, tauto,
        have eqfalse₂ : y₂ = x ↔ false, tauto,
        dsimp only [f'], rw [eqfalse, eqfalse₂], simp,
        have ih2' := ih2 y₁ yin₁ y₂ yin₂,
        tauto,
      }
    }
  },
end

lemma range_sup (f : ℕ → ℕ) (n m : ℕ) (him : ∀ (x : ℕ), x < n → f x < m) : (finset.image f (range n)).card ≤ m
:= begin
  have g : m = (range m).card, simp,
  rw g,
  have g' : image f (range n) ⊆ range m,
    rw subset_iff, intros x xin,
    simp, simp at xin,
    rcases xin with ⟨y, hlt, hfeq⟩,
    specialize him y hlt, rw hfeq at him, assumption,
  exact card_le_of_subset g',
end

end finset
