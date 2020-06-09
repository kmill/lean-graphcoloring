-- König's lemma (weak form)

import data.set
import tactic
import data.fintype.basic

namespace konig

open set

attribute [instance] classical.prop_decidable

def inv_system {X} (S : ℕ → set X) (fns : ℕ → X → X)
:= ∀ n, ∀ x ∈ S(n+1), fns n x ∈ S n


section
variables {X : Type} {S : ℕ → set X} {fns : ℕ → X → X}

def inv_limit (sys : inv_system S fns) (u : ℕ → X)
:= ∀ n, u n ∈ S n ∧ u n = fns n (u (n + 1))

def partial_inv_limit (sys : inv_system S fns) (u : ℕ → X) (m : ℕ)
:= (∀ n ≤ m, u n ∈ S n) ∧ (∀ n < m, u n = fns n (u (n + 1)))

-- Given an element x ∈ S m, one can take recursive images of x
-- through the directed system to produce a "partial" inverse limit
-- that's defined for 0, 1, ..., m.
def partial_inv_limit_from (sys : inv_system S fns) (m : ℕ) (x : X) (xel : x ∈ S m)
: ∃ (u : ℕ → X), u m = x ∧ partial_inv_limit sys u m
:= begin
  induction m with m ih generalizing x, {
    use λ n, x, split, refl,
    split, intro n, cases n, simp, assumption, simp,
      have h : n.succ = 0 ↔ false, tauto,
      rw h, tauto,
    intro n,
    have h : n < 0 ↔ false, split, intro, linarith, intro, tauto, rw h, simp,
  }, {
    specialize ih (fns m x) (sys m x xel),
    rcases ih with ⟨u₀, ih⟩,
    let u := λ n, if n > m then x else u₀ n,
    use u,
    have msucc : m.succ = m+1 := rfl,
    split, {
      dsimp only [u],
      have h : (m.succ > m) ↔ true, rw msucc, split, tauto, intro, linarith,
      rw h, simp,
    }, {
      split,
      intros n nlt,
      dsimp only [u],
      by_cases n = m + 1, {
        have ineqtrue : n > m ↔ true,
          split, tauto, intro, linarith,
        rw ineqtrue, simp, rw h, exact xel,
      }, {
        have n_le_m : n ≤ m,
          cases nat.eq_or_lt_of_le nlt,
            tauto, linarith,
        have ineqfalse : n > m ↔ false,
          split, intro, cases nat.eq_or_lt_of_le nlt, change n = m + 1 at h_1, tauto, linarith, tauto,
        rw ineqfalse, simp,
        exact ih.right.left n n_le_m,
      },

      intros n nlt, {
        rw msucc at nlt,
        dsimp only [u],
        by_cases eq : n = m, rw eq, simp,
        have irr : m < m ↔ false, split, intro, exact nat.lt_irrefl m a, tauto,
        rw irr, simp, tauto,
        have false1 : n > m ↔ false, split, intro, linarith, tauto,
        have lt : n ≤ m, linarith,
        have lt2 := nat.eq_or_lt_of_le lt,
        have false2 : n + 1 > m ↔ false, split, intro,
          cases lt2, tauto,
          linarith, tauto,
        rw [false1, false2], simp,
        have lt : n < m, cases lt2, tauto, assumption,
        have g := ih.right.right n lt, tauto,
      },
    },
  },
end

-- Given a partial limit up to n, one can restrict it to a shorter partial limit.
lemma partial_inv_limit_restrict (sys : inv_system S fns) (u : ℕ → X) (n m : ℕ) (h : n ≥ m) (lim : partial_inv_limit sys u n)
: partial_inv_limit sys u m
:= begin
  split, {
    intros k k_le_m,
    have h: k ≤ n, linarith,
    exact lim.left k h,
  }, {
    intros k k_lt_m,
    have h : k < n, linarith,
    exact lim.right k h,
  },
end

-- Given a "choice function," construct a sequence starting with a given value.
def construct (f : ℕ → X → X) (x₀ : X) : ℕ → X
| 0 := x₀
| (n+1) := (f n (construct n))

-- An element x of (S n) is "very extendable" if partial inverse limits u with u n = x exist for all lengths.
def very_extendable (sys : inv_system S fns) (n : ℕ) (x : X)
:= ∀ m ≥ n, ∃ u, partial_inv_limit sys u m ∧ u n = x

-- In an inverse system of finite sets, every set has at least one very extendable element.
lemma exists_very_extendable
(sys : inv_system S fns) (nonempty : ∀ n, ∃ x, x ∈ S n) [fin : ∀ n, fintype (S n)]
: ∀ n, ∃ x, x ∈ S n ∧ very_extendable sys n x
:= begin
    by_contradiction f,
    unfold very_extendable at f,
    push_neg at f,
    rcases f with ⟨N,f⟩,
    have f' : ∀ x, ∃ m, m ≥ N ∧ ∀ (u : ℕ → X), x ∈ S N → u N = x → ¬partial_inv_limit sys u m,
      intro x, specialize f x,
      cases f, {
        use [N, (by linarith)],
        intros u xnel, tauto,
      }, {
        rcases f with ⟨m, m_ge_n, f⟩, use m, use m_ge_n, intros u unx,
        specialize f u, tauto,
      },
    choose v fv using f',
    let SN := set.to_finset (S N),
    let N' := finset.sup SN v,
    have N'big : N ≤ N',
      rcases nonempty N with ⟨x, xin⟩,
      specialize fv x,
      have h : v x ≤ N', apply finset.le_sup, simp, assumption, linarith,
    rcases nonempty N' with ⟨xN', xN'in⟩,
    rcases partial_inv_limit_from sys N' xN' xN'in with ⟨u, uisx, hplim⟩,
    set x := u N with xeq,
    rcases fv x with ⟨vxge, uprop⟩,
    specialize uprop u,
    have xelt := hplim.left N N'big, rw ←xeq at xelt,
    specialize uprop xelt xeq,
    have vx_lt_N' : v x ≤ N',
      apply finset.le_sup, simp, assumption,
    have hplim' : partial_inv_limit sys u (v x) := partial_inv_limit_restrict sys u N' (v x) vx_lt_N' hplim,

    exact uprop hplim',
end

-- This is that an ℕ-indexed inverse system of finite sets has a nonempty inverse limit.
-- This would follow from Tychonoff's theorem applied to the product of these finite sets.
-- One could also prove this using ultrafilters.
lemma weak_konig_lemma (sys : inv_system S fns) (nonempty : ∀ n, ∃ x, x ∈ S n) [fin : ∀ n, fintype (S n)]
: ∃ (u : ℕ → X), inv_limit sys u
:= begin
  let S' := λ n, {x | x ∈ S n ∧ very_extendable sys n x},
  have nonempty' : ∀ n, ∃ x, x ∈ S' n := exists_very_extendable sys nonempty,

  have liftable : ∀ (n : ℕ) (x ∈ S' n), ∃ (x' ∈ S' (n + 1)), x = fns n x', {
    rintros n x ⟨xin,xvext⟩,
    set Sx := λ k, finset.filter (λ y, ∃ u m, m ≥ n ∧ m ≥ k ∧ partial_inv_limit sys u m ∧ u n = x ∧ u k = y) (S k).to_finset,
    have Sx_nonempty : ∀ k, ∃ y, y ∈ Sx k, {
      intro k,
      by_cases h : k < n, {
        rcases partial_inv_limit_from sys n x xin with ⟨u, un_eq, plim⟩,
        use u k, simp,
        use plim.left k (by linarith),
        use [u, n, by linarith, by linarith, plim, un_eq],
      }, {
        push_neg at h,
        rcases xvext k h with ⟨u, plim, un_eq⟩,
        use u k, simp, use plim.left k (by linarith),
        use [u, k, by linarith, plim, un_eq],
      },
    },
    have sys' : inv_system (λ k, ↑(Sx k)) fns, {
      intros k y yin,
      simp at yin, simp,
      use sys k y yin.left,
      rcases yin.right with ⟨u, m, n_le_m, k_le, plim, un_eq, uk_eq⟩,
      use [u, m, n_le_m, by linarith, plim, un_eq],
      rw ← uk_eq,
      exact plim.right k (by linarith),
    },
    have Sx_ve := exists_very_extendable sys' Sx_nonempty,
    rcases Sx_ve (n + 1) with ⟨x', x'el, x've⟩,
    use x',
    simp at x'el, simp,
    split, split,
    exact x'el.left,
    {
      intros m mge,
      rcases x've m mge with ⟨u, plim, ueq⟩,
      use u,
      split, split,
      intros n nle,
      have hh := plim.left n nle, simp at hh, tauto,
      intros n nlt,
      exact plim.right n nlt,
      exact ueq,
    },
    rcases x'el.right with ⟨u, m, n_le_m, n1_le_m, plim, un_eq_x, un1_eq_x'⟩,
    rw ← un_eq_x, rw ← un1_eq_x',
    have ineq : n < m, linarith,
    exact plim.right n ineq,
  },

  have liftable' : ∀ n x, ∃ x', x ∈ S' n → (x' ∈ S' (n + 1) ∧ x = fns n x'), {
    intros n x,
    by_cases xel : x ∈ S' n,
      rcases liftable n x xel with ⟨x', x'el, p⟩, use x', intro, use [x'el, p],
      use x,
  },
  have sys' : inv_system S' fns, {
    intros n x xel,
    simp at xel, simp,
    use sys n x xel.left,
    intros m mge,
    rcases xel.right (max m (n + 1)) le_sup_right with ⟨u, plim, un1_eq_x⟩,
    use u,
    use partial_inv_limit_restrict sys u (max m (n + 1)) m le_sup_left plim,
    rw ← un1_eq_x,
    have hle : n < max m (n + 1), linarith [le_max_right m (n + 1)],
    exact plim.right n hle,
  },
  have stronger : ∃ (u : ℕ → X), inv_limit sys' u, {
    choose u₀ hu₀ using liftable',
    rcases nonempty' 0 with ⟨x₀, x₀el⟩,
    simp at x₀el,
    use construct u₀ x₀,
    intro n,
    induction n with m ih, {
      dsimp only [construct],
      exact ⟨x₀el, (hu₀ 0 x₀ x₀el).right⟩,
    }, {
      dsimp only [construct],
      split, {
        exact (hu₀ m (construct u₀ x₀ m) ih.left).left,
      }, {
        dsimp only [construct] at ih,
        set y := construct u₀ x₀ m with yeq,
        have hu₀0 := hu₀ m y ih.left,
        have hu₀1 := hu₀ (m + 1) (u₀ m y) hu₀0.left,
        rw ← hu₀1.right,
      },
    },
  },
  
  rcases stronger with ⟨u, invlim⟩,
  use u, intro n,
  specialize invlim n,
  exact ⟨invlim.left.left, invlim.right⟩,
end

end

end konig
