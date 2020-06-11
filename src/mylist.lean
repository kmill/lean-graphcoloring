import data.list
import data.finset
import tactic
import myoption

open list

namespace list

universe u

lemma init_length_is_pred {A : Type u} {xs : list A} (h : xs ≠ [])
: xs.init.length = xs.length - 1 :=
begin
  induction xs with x₀ xs ih, refl,
  cases xs with x₁ xs, refl,
  simp [init] at ⊢ ih,
  exact ih,
end

lemma init_nth {A : Type u} {xs : list A} (i : ℕ) (h : i + 1 < xs.length)
: xs.init.nth i = xs.nth i :=
begin
  induction xs with x₀ xs ih generalizing i, refl,
  simp at h,
  cases xs with x₁ xs, dsimp at h, exfalso, linarith only [h],
  cases i, refl,
  dsimp [init] at ⊢,
  exact ih i h,
end

lemma init_rep_nth {A : Type u} (f : ℕ → list A)
(sys : ∀ k, f k = (f k.succ).init) (lens : ∀ k, (f k).length = k)
(i a b : ℕ) (h₁ : i < a) (h₂ : a ≤ b)
: list.nth (f a) i = list.nth (f b) i :=
begin
  induction b with b ihb generalizing a,
  exfalso, linarith only [h₁, h₂],
  change a ≤ b + 1 at h₂,
  cases nat.eq_or_lt_of_le h₂ with h₃ h₃, rw h₃,
  rw ← init_nth i (_ : i + 1 < (f b.succ).length),
  rw ← sys,
  exact ihb a h₁ (by linarith),
  rw lens,
  change _ < _ + 1, linarith,
end

@[norm_cast]
lemma coe_nth {A B} [has_lift_t A B] (xs : list A) (i : ℕ)
: (↑xs : list B).nth i = (↑(xs.nth i) : option B) :=
begin
  unfold_coes, simp,
end


-- Produces a function ℕ → A starting with the given list, then a constant value after that.
def as_fn {A : Type u} : list A → A → ℕ → A
| xs a i := option.get_or_else (xs.nth i) a

lemma as_fn_inrange {A : Type u} {a : A} {xs : list A} {i : ℕ} (h : i < xs.init.length)
: xs.init.as_fn a i = xs.as_fn a i :=
begin
  dsimp only [as_fn, nth],
  have h' : i + 1 < xs.length, {
    cases xs with x₀ xs, dsimp [init] at h, linarith only [h],
    have neq : (list.cons x₀ xs) ≠ [], tauto,
    rw init_length_is_pred neq at h, simp at h ⊢, exact h,
  },
  rw init_nth i h',
end

-- range2 a n is the list [a, a+1, a+2, ..., a+n-1]
@[simp] def range2 : ℕ → ℕ → list ℕ
| _ 0 := []
| a (b+1) := a :: range2 (a + 1) b

protected
lemma range2_red_nth (a b i : ℕ)
: (range2 a (b + i)).nth i = (range2 (a+i) b).nth 0 :=
begin
  induction i with i ih generalizing a b,
  refl,
  change (range2 (a + 1) (b + i)).nth i = _,
  rw ih,
  ring,
end

@[simp] lemma range2_nth (a b i : ℕ) (h : i < b)
: (range2 a b).nth i = some (a + i) :=
begin
  have eq : b = (b - i) + i, omega,
  rw eq,
  rw list.range2_red_nth,
  cases (b - i), exfalso, linarith,
  refl,
end

@[simp] lemma range2_length (a b : ℕ) : (range2 a b).length = b :=
begin
  induction b with b ihb generalizing a,
  refl, simp, rw ihb,
end

end list
