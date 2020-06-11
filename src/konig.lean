-- König's lemma (weak form)

import data.set
import tactic
import data.fintype.basic

namespace konig

open set

attribute [instance] classical.prop_decidable

universe u
variable {X : Type u}

def inv_system {X} (S : ℕ → set X) (fns : ℕ → X → X) :=
∀ n, ∀ x ∈ S(n+1), fns n x ∈ S n

section S_and_fns

variables {S : ℕ → set X} {fns : ℕ → X → X}

def inv_limit (sys : inv_system S fns) (u : ℕ → X) :=
∀ n, u n ∈ S n ∧ u n = fns n (u (n + 1))

def partial_inv_limit (sys : inv_system S fns) (u : ℕ → X) (m : ℕ) :=
(∀ n ≤ m, u n ∈ S n) ∧ (∀ n < m, u n = fns n (u (n + 1)))

-- Given an element x ∈ S m, one can take recursive images of x
-- through the directed system to produce a "partial" inverse limit
-- that's defined for 0, 1, ..., m.
def partial_inv_limit_from (sys : inv_system S fns) (m : ℕ) (x : X) (xel : x ∈ S m)
: ∃ (u : ℕ → X), partial_inv_limit sys u m ∧ u m = x :=
begin
  induction m with m ih generalizing x,
  use (λ n, x), simp, split, simpa, simp,
  rcases ih (fns m x) (sys m x xel) with ⟨u₀, ih⟩,
  use (λ n, if n > m then x else u₀ n),
  split, {
    split, {
      intros n nlt,
      dsimp only,
      split_ifs,
      change n ≥ m.succ at h,
      rwa (by linarith : n = m.succ),
      refine ih.left.left _ _,
      push_neg at h, exact h,
    }, {
      intros n nlt, change n < m + 1 at nlt,
      dsimp only,
      split_ifs,
      exfalso, linarith,
      exfalso, linarith,
      rwa (by linarith : n = m),
      exact ih.2,
      exact ih.1.2 n (by linarith),
    },
  }, {
    split_ifs, refl,
    push_neg at h,
    change m + 1 ≤ m at h,
    exfalso, linarith only [h],
  },
end

-- Given a partial limit up to n, one can restrict it to a shorter partial limit.
lemma partial_inv_limit_restrict (sys : inv_system S fns) (u : ℕ → X) (n m : ℕ)
(h : n ≥ m) (lim : partial_inv_limit sys u n)
: partial_inv_limit sys u m :=
⟨(λ k h, lim.left k (by linarith)), (λ k h, lim.right k (by linarith))⟩

-- Given a "choice function," construct a sequence starting with a given value.
def construct (f : ℕ → X → X) (x₀ : X) : ℕ → X
| 0 := x₀
| (n+1) := (f n (construct n))

-- An element x of (S n) is "very extendable" if partial inverse limits u with u n = x exist for all lengths.
def very_extendable (sys : inv_system S fns) (n : ℕ) (x : X) :=
∀ m ≥ n, ∃ u, partial_inv_limit sys u m ∧ u n = x

-- In an inverse system of finite sets, every set has at least one very extendable element.
lemma exists_very_extendable
(sys : inv_system S fns) (nonempty : ∀ n, ∃ x, x ∈ S n) [fin : ∀ n, fintype (S n)]
: ∀ n, ∃ x, x ∈ S n ∧ very_extendable sys n x :=
begin
  by_contradiction f,
  dsimp only [very_extendable] at f, push_neg at f,
  rcases f with ⟨N,f⟩,
  have f' : ∀ x, ∃ m, m ≥ N ∧ ∀ (u : ℕ → X), x ∈ S N → u N = x → ¬partial_inv_limit sys u m, {
    intro x,
    cases f x,
    use [N, (by linarith)], intros u xnel, tauto,
    rcases h with ⟨m, m_ge_n, f⟩, use [m, m_ge_n], intros u unx, specialize f u, tauto,
  },
  choose v fv using f',
  let N' := (S N).to_finset.sup v,
  have N'big : N ≤ N', {
    rcases nonempty N with ⟨x, xin⟩,
    have h : v x ≤ N', apply finset.le_sup, simp, exact xin,
    linarith [(fv x).1],
  },
  rcases nonempty N' with ⟨xN', xN'in⟩,
  rcases partial_inv_limit_from sys N' xN' xN'in with ⟨u, hplim, uisx⟩,
  set x := u N with xeq,
  rcases fv x with ⟨vxge, uprop⟩,
  have xelt := hplim.left N N'big,
  rw ←xeq at xelt,
  have vx_lt_N' : v x ≤ N', apply finset.le_sup, simp, exact xelt,
  exact uprop u xelt xeq (partial_inv_limit_restrict sys u N' (v x) vx_lt_N' hplim),
end

lemma sys_restrict_very_extendable (sys : inv_system S fns)
: inv_system (λ n, {x ∈ S n | very_extendable sys n x}) fns :=
begin
  intros n x xel, simp at xel ⊢,
  use sys n x xel.left,
  intros m mge,
  rcases xel.right (max m (n + 1)) le_sup_right with ⟨u, plim, un1_eq_x⟩,
  use u,
  use partial_inv_limit_restrict sys u (max m (n + 1)) m le_sup_left plim,
  rw ← un1_eq_x,
  have hle : n < max m (n + 1), linarith [le_max_right m (n + 1)],
  exact plim.right n hle,
end

lemma lift_very_extendable (sys : inv_system S fns) {n : ℕ} {x : X} [fin : ∀ n, fintype (S n)]
(h : very_extendable sys n x)
: ∃ x', x = fns n x' ∧ x' ∈ S(n + 1) ∧ very_extendable sys (n + 1) x' :=
begin
  dsimp [very_extendable] at h,  
  let Sx := λ k, {y ∈ S k | ∃ u, partial_inv_limit sys u (max n k) ∧ u n = x ∧ u k = y},
  have Sx_nonempty : ∀ k, ∃ y, y ∈ Sx k, {
    intro k,
    by_cases klt : k < n, {
      rcases h n (by linarith) with ⟨u, plim, uneq⟩,
      use [u k, plim.left k (by linarith), u],
      rw (max_eq_left_of_lt klt),
      exact ⟨plim, uneq, rfl⟩,
    }, {
      push_neg at klt,
      rcases h k klt with ⟨u, plim, un_eq⟩,
      use [u k, plim.left k (by linarith), u],
      rw (max_eq_right klt),
      use [plim, un_eq],
    },
  },
  have Sx_invsys : inv_system Sx fns, {
    rintros k y ⟨yelt, u, plim, un_eq, uk_eq⟩,
    split,
    exact sys k y yelt,
    have mle : max n k ≤ max n (k + 1) := max_le (le_max_left _ _) (by linarith [le_max_right n (k + 1)]),
    use [u, partial_inv_limit_restrict sys u _ _ mle plim, un_eq],
    rw ←uk_eq,
    exact (plim.2 k) (by linarith [le_max_right n (k + 1)]),
  },
  rcases exists_very_extendable Sx_invsys Sx_nonempty (n + 1) with ⟨x', ⟨x'elt, u, plim, ueq_x, ueq_x'⟩, vext⟩,
  use x',
  split,
  rw [←ueq_x, ←ueq_x'],
  rw max_eq_right (by linarith : n ≤ n + 1) at plim,
  use plim.2 n (by linarith),
  use x'elt,
  intros m mgen,
  rcases vext m mgen with ⟨v, plim, veq_x'⟩,
  exact ⟨v, ⟨(λ n nlem, (plim.1 n nlem).1), (λ n nltm, plim.2 n nltm)⟩, veq_x'⟩,
end

lemma surj_inv_sys_has_inv_lim (sys : inv_system S fns) (s : ∀ n x, x ∈ S n → ∃ x', x' ∈ S (n + 1) ∧ x = fns n x') (start : ∃x₀, x₀ ∈ S 0)
: ∃ u, inv_limit sys u :=
begin
  have s' : ∀ n x, ∃ x', x ∈ S n → x' ∈ S (n + 1) ∧ x = fns n x', {
    intros n x,
    by_cases xel : x ∈ S n, {
      rcases s n x xel with ⟨x', h⟩,
      use x', intro, exact h,
    }, {
      use x,
    },
  },
  choose u hu using s',
  rcases start with ⟨x₀, x₀elt⟩,
  use construct u x₀,
  intro n,
  induction n with n ih, {
    exact ⟨x₀elt, (hu 0 x₀ x₀elt).2⟩,
  }, {
    exact ⟨(hu _ _ ih.1).1, (hu _ _ (hu _ _ ih.1).1).2⟩,
  },
end

-- This is that an ℕ-indexed inverse system of finite sets has a nonempty inverse limit.
-- This would follow from Tychonoff's theorem applied to the product of these finite sets.
-- One could also prove this using ultrafilters.
lemma weak_konig_lemma (sys : inv_system S fns) (nonempty : ∀ n, ∃ x, x ∈ S n) [fin : ∀ n, fintype (S n)]
: ∃ (u : ℕ → X), inv_limit sys u
:= begin
  let S' := λ n, {x | x ∈ S n ∧ very_extendable sys n x},
  have nonempty' : ∀ n, ∃ x, x ∈ S' n := exists_very_extendable sys nonempty,

  have liftable : ∀ n x, x ∈ S' n → ∃ x', x' ∈ S' (n + 1) ∧ x = fns n x', {
    intros n x xel,
    rcases lift_very_extendable sys xel.2 with ⟨x', xeq, x'el⟩,
    exact ⟨x', x'el, xeq⟩,
  },
  have sys' : inv_system S' fns := sys_restrict_very_extendable sys,
  have stronger : ∃ (u : ℕ → X), inv_limit sys' u := surj_inv_sys_has_inv_lim sys' liftable (nonempty' 0),
  
  rcases stronger with ⟨u, invlim⟩,
  use u, intro n,
  specialize invlim n,
  exact ⟨invlim.left.left, invlim.right⟩,
end

end S_and_fns

end konig
