import data.set
import data.finset
import data.list.basic
import data.vector
import data.option.basic
import tactic

import myoption
import mylist
import myfinset
import myfintype
import konig

namespace graph

open set finset

attribute [instance] classical.prop_decidable

-- A graph is a collection of vertices with at most one edge between
-- any pair of vertices.  Self-loops are allowed.
structure graph (X : Type) :=
  mk :: (V : set X) (E : X → X → Prop) (sym : symmetric E)

-- A subgraph consists of a subset of vertices and a "subset" of edges.
protected def is_subgraph {X} (G' : graph X) (G : graph X)
:= G'.V ⊆ G.V ∧ ∀ v ∈ G'.V, ∀ w ∈ G'.V, G'.E v w → G.E v w

-- use G' ⊆ G to denote subgraphs
instance (X) : has_subset (graph X) := ⟨graph.is_subgraph⟩

-- A graph containing an edge between every pair of distinct vertices
def complete_graph {X} (V : set X) := graph.mk V (λ v w, v ≠ w) (by tauto)

-- Gives the induced subgraph with vertex set W
def induced {X} (G : graph X) (W : set X) (sub : W ⊆ G.V) :=
  graph.mk W G.E G.sym

lemma induced_is_subgraph {X} (G : graph X) (W : set X) (sub : W ⊆ G.V)
: induced G W sub ⊆ G
:=
begin
  split,
  exact sub,
  intros v w vin win indedge,
  exact indedge,
end

-- A graph coloring is an assignment of a "color" to each vertex such
-- that adjacent vertices have distinct colors.
def graph_coloring {X} {C} (G : graph X) (c : X → C) :=
  ∀ v ∈ G.V, ∀ w ∈ G.V, G.E v w → c v ≠ c w

-- A graph is n-colorable if it is colorable using only the colors 0 through (n-1).
def ncolorable {X} (G : graph X) (n : ℕ) :=
  ∃ (c : X → ℕ), c '' G.V ⊆ ↑(range n) ∧ graph_coloring G c

lemma std_ncoloring {X} {C} {G : graph X} (C' : finset C) (c : X → C)
(nc : graph_coloring G c) (cod : ∀ v ∈ G.V, c v ∈ C')
: ncolorable G (card C')
:= begin
  rcases finset.inj_range C' with ⟨f, hfdom, hfinj⟩,
  use (f ∘ c),
  simp,
  split, {
    intros n nelt, simp at nelt,
    rcases nelt with ⟨v, velt, fcv_n⟩,
    simp,
    rw ← fcv_n,
    exact hfdom (c v) (cod v velt),
  }, {
    intros v vin w win hedge f,
    specialize hfinj (c v) (cod v vin) (c w) (cod w win) f,
    exact nc v vin w win hedge hfinj,
  },
end

def chromatic_number {X} (G : graph X) (n : ℕ) :=
  ncolorable G n ∧ ∀ m < n, ¬ncolorable G m

-- A complete graph of n vertices can be colored with n or more colors but no fewer.
lemma complete_graph_chromatic_number (n : ℕ): chromatic_number (complete_graph (↑(range n) : set ℕ)) n
:=
begin
  split, {
    set f := λ (v : ℕ), v with feq,
    use f,
    split, {
      dsimp only [complete_graph],
      intros c cin,
      rcases cin with ⟨x,h⟩, rw feq at h, dsimp only at h, rw ←h.2, tauto,
    }, {
      intros v vin w win hedge,
      dsimp [complete_graph] at vin, simp at vin,
      dsimp [complete_graph] at win, simp at win,
      dsimp [complete_graph] at hedge,
      rw feq, dsimp only, tauto,
    },
  }, {
    intros m msmall notcolor,
    rcases notcolor with ⟨f,fim,coloring⟩,
    dsimp [complete_graph] at fim,
    dsimp [graph_coloring,complete_graph] at coloring, simp at coloring,
    have h : ∀ x < n, f x < m, {
      intros x xin,
      have xin' : x ∈ range n, rw ← finset.mem_range at xin, exact xin,
      have fxin' : f x ∈ f '' ↑(range n), exact mem_image_of_mem f xin',
      specialize fim fxin', simp at fim, exact fim,
    },
    have rangen := range n,
    have coloring' : ∀ v ∈ range n, ∀ w ∈ range n, f v = f w → v = w,
      intros v velt w welt, simp at velt, simp at welt, specialize coloring v velt w welt, contrapose, assumption,
    have hh := card_image_of_inj_on coloring',
    have hh' := range_sup f n m h,
    dsimp only at hh, rw hh at hh',
    simp at hh', linarith,
  },
end

-- An n-colored graph can be colored with more than n colors.
lemma can_color_with_more {X} (G : graph X) (n m : ℕ) (gt : m ≥ n) (able : ncolorable G n) : ncolorable G m
:=
begin
  rcases able with ⟨c, cod, col⟩,
  have dom' : ∀ v ∈ G.V, c v < m,
    intros v vin,
    have code' := cod (mem_image_of_mem c vin),
    simp at code',
    linarith,
  unfold ncolorable,
  use c,
  split, {
    intros c celt,
    rcases celt with ⟨v, velt, cv_eq⟩,
    specialize dom' v velt,
    rw cv_eq at dom', simpa,
  }, {
    assumption,    
  },
end

lemma can_color_subgraph {X} {H G : graph X} (sub : H ⊆ G) (c : X → ℕ) (is_coloring : graph_coloring G c)
: graph_coloring H c
:=
begin
  intros v vin w win vwedgeH,
  have vwedgeG : G.E v w := sub.2 v vin w win vwedgeH,
  exact is_coloring v (sub.1 vin) w (sub.1 win) vwedgeG,
end

-- The following theorem is an application of König's lemma, pointed
-- out by C. St. J. A. Nash-Williams in "Infinite graphs --- a survey"
-- (1967).
theorem can_color_countable_infinite (n : ℕ) (pos : n > 0)
(G : graph ℕ) (fcol : ∀ (V : finset ℕ) (sub : ↑V ⊆ G.V), ncolorable (induced G ↑V sub) n)
: ncolorable G n
:= begin
  let Vfin := λ n, G.V ∩ ↑(finset.range n),
  have sub : ∀ n, Vfin n ⊆ G.V, {
    intro n, exact G.V.sep_subset _,
  },
  let Gfin := λ k, induced G (Vfin k) (sub k),

  let zero : {i : ℕ // i < n} := ⟨0, pos⟩,
  let X := list {i : ℕ // i < n},
  let S : ℕ → set X := λ (k : ℕ), {v : X | v.length = k ∧ graph_coloring (Gfin k) (v.as_fn zero)},
  let fns := λ (k : ℕ) (v : X), v.init,

  have sys : konig.inv_system S fns, {
    intros k x xel,
    simp [fns] at xel ⊢,
    rcases xel with ⟨xlen, coloring⟩,
    have nonnil : x ≠ [], {
      by_contradiction f, push_neg at f,
      rw f at xlen, simp at xlen, exact (nat.succ_ne_zero k).symm xlen,
    },
    have h := list.init_length_is_pred nonnil,
    rw xlen at h, simp at h, rw h, simp,

    intros v vel w wel hedge,
    dsimp only [Gfin, Vfin, induced] at hedge,
    dsimp only [Gfin, Vfin, induced] at vel wel, simp at vel wel,
    dsimp only [graph_coloring, Gfin, Vfin, induced] at coloring, simp at coloring,
    specialize coloring v vel.1 (by linarith) w wel.1 (by linarith) hedge,
    have x_nonnil : x ≠ [], intro is_nil, rw is_nil at xlen, simp at xlen, tauto,
    have xinit_len : x.init.length = k,
      have hlen := list.init_length_is_pred x_nonnil, rw xlen at hlen, exact hlen,
    have vtineq : v < x.init.length,
      rw ← xinit_len at vel, exact vel.right,
    have wtineq : w < x.init.length,
      rw ← xinit_len at wel, exact wel.right,
    rw list.as_fn_inrange vtineq,
    rw list.as_fn_inrange wtineq,
    exact coloring,
  },
  have nonempty : ∀ k, ∃ c, c ∈ S k, {
    intro k,
    specialize fcol ((finset.range k).filter(λ k, k ∈ G.V)),
    have sub : ↑(filter (λ (k : ℕ), k ∈ G.V) (range k)) ⊆ G.V, {
      simp, exact (↑(finset.range k) : set ℕ).inter_subset_right G.V,
    },
    specialize fcol sub, simp at fcol,
    rcases fcol with ⟨c, hcdom, hcol⟩,
    let c' := λ i, if i ∈ G.V then c i else 0,
    have rng : ∀ i < k, c' i < n, {
      intros i iineq,
      dsimp [c'],
      by_cases h : i ∈ G.V,
      have htrue : i ∈ G.V ↔ true, tauto,
      rw htrue, simp,
      dsimp [induced] at hcdom,
      have elt : i ∈ {x ∈ ↑(range k) | x ∈ G.V}, {
        have irange : i ∈ (↑(range k) : set ℕ), simpa,
        exact mem_sep irange h,
      },
      have celt : c i ∈ range n, {
        apply hcdom, exact mem_image_of_mem c elt,
      },
      simp at celt, exact celt,
      have hfalse : i ∈ G.V ↔ false, tauto,
      rw hfalse, simp, linarith,
    },
    let c'' := λ i, if i < k then c' i else 0,
    have rng' : ∀ i, c'' i < n, {
      intro i,
      dsimp [c''],
      by_cases h : i < k, {
        have htrue : i < k ↔ true, tauto,
        rw htrue, simp,
        exact rng i h,
      }, {
        have hfalse : i < k ↔ false, tauto,
        rw hfalse, simp,
        linarith,
      },
    },
    let c''' : ℕ → {x : ℕ // x < n} := λ i, ⟨c'' i, rng' i⟩,
    let clis := (list.range2 0 k).map c''',
    use clis,
    dsimp [S],
    split, {
      dsimp [clis], simp,
    }, {
      intros v vin w win hedge,
      dsimp [Gfin, Vfin, induced] at vin win hedge, simp at vin win,
      dsimp [clis, list.as_fn], simp,
      have rngv := list.range2_nth 0 k v vin.2,
      have rngw := list.range2_nth 0 k w win.2,
      rw [rngv, rngw], simp,
      dsimp [c'', c'],
      have vkt : v < k ↔ true, tauto,
      have wkt : w < k ↔ true, tauto,
      have vint : v ∈ G.V ↔ true, tauto,
      have wint : w ∈ G.V ↔ true, tauto,
      simp [vkt, wkt, vint, wint],
      dsimp [graph_coloring, induced] at hcol, simp at hcol,
      exact hcol v vin.2 vin.1 w win.2 win.1 hedge,
    },
  },

  rcases konig.weak_konig_lemma sys nonempty with ⟨u, invlim⟩,
  use (λ v, list.as_fn ↑(u (v+1)) zero v),
  have zup : (0:ℕ) = ↑zero, unfold_coes,
  split, {
    intros c cin,
    simp at cin, simp,
    rcases cin with ⟨v, vin, cdef⟩,
    dsimp [list.as_fn] at cdef,
    rw zup at cdef,
    norm_cast at cdef, unfold_coes at cdef,
    set lu := ((list.nth (u (v + 1)) v).get_or_else zero) with lueq,
    rw ← cdef, exact lu.property,
  }, {
    intros v vin w win hedge,
    dsimp [list.as_fn], rw zup, norm_cast, unfold_coes,
    have rsys : ∀ k, u k = list.init (u (k + 1)), {
      intro k,
      have f := invlim k,
      dsimp [fns] at f,
      exact f.right,
    },
    have lens : ∀ k, (u k).length = k, {
      intro k,
      have f := (invlim k).left,
      dsimp [S] at f, exact f.1,
    },
    let K := max (v + 1) (w + 1),
    have liftv := list.init_rep_nth u rsys lens v (v + 1) K (by linarith) (le_max_left (v + 1) (w + 1)),
    have liftw := list.init_rep_nth u rsys lens w (w + 1) K (by linarith) (le_max_right (v + 1) (w + 1)),
    rw [liftv, liftw],
    have uKelt := (invlim K).left,
    dsimp [S,graph_coloring,Gfin,Vfin,list.as_fn,induced] at uKelt, simp at uKelt,
    have vlt : v < v + 1 ∨ v < w + 1, left, linarith,
    have wlt : w < v + 1 ∨ w < w + 1, right, linarith,
    have uKelt' := uKelt.right v vin vlt w win wlt hedge,
    intro as_eq,
    have as_eq' := subtype.eq as_eq,
    exact uKelt' as_eq',
  },

end

end graph
