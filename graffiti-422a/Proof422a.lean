import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

/-! Graffiti.pc #422a, December 8, 2010. The 45-vertex construction is due
to Claude Opus 5 (AI Village, graffiti-verification, README section 7bd).
This file checks the lambda = 1 instance of that prior counterexample. -/
namespace Graffiti422a
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

def Independent (D : Finset V) : Prop := ∀ x ∈ D, ∀ y ∈ D, ¬G.Adj x y
def Dominates (D : Finset V) : Prop := ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

noncomputable def iNum : ℕ := sInf {n | ∃ D : Finset V, Independent G D ∧ Dominates G D ∧ D.card = n}
noncomputable def alphaOn (R : Finset V) : ℕ := sSup {n | ∃ D : Finset V, D ⊆ R ∧ Independent G D ∧ D.card = n}

variable [Fintype V] [DecidableRel G.Adj]

def maxSet : Finset V := univ.filter (fun v => ∀ w, G.degree w ≤ G.degree v)

/-- Each unordered edge in the induced graph has two orientations. -/
def edgesOn (S : Finset V) : ℕ := ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card / 2

abbrev Vertex := Fin 45

private def seesCore (m u : Vertex) : Bool :=
  decide (36 ≤ m.val ∧ u.val < 36) &&
    (if u.val < 18 then decide ((m.val-36)/3 ≠ u.val/6)
     else decide ((m.val-36)%3 ≠ (u.val-18)/6))

private def edge (u v : Vertex) : Bool :=
  decide (u ≠ v ∧ u.val < 36 ∧ v.val < 36 ∧ u.val/18 = v.val/18) ||
    seesCore u v || seesCore v u

def graph : SimpleGraph Vertex where
  Adj v w := edge v w = true
  symm := by change ∀ u v : Vertex, edge u v = true → edge v u = true; decide
  loopless := by change ∀ u : Vertex, ¬ edge u u = true; decide

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (edge u v = true))

private theorem degrees : ∀ v : Vertex, graph.degree v = if 36 ≤ v.val then 24 else 23 := by
  decide +kernel

private theorem max_mem (v : Vertex) : v ∈ maxSet graph ↔ 36 ≤ v.val := by
  simp only [maxSet,mem_filter,mem_univ,true_and,degrees]
  constructor
  · intro h
    have at36 := h 36
    by_contra small
    rw [if_pos (by decide),if_neg small] at at36
    omega
  · intro h w
    rw [if_pos h]
    split <;> decide

private theorem connected : graph.Connected := by
  have joins : ∀ v : Vertex, v = 0 ∨ graph.Adj 0 v ∨ graph.Adj 40 v ∨ graph.Adj 18 v ∨ graph.Adj 6 v := by decide
  have reach40 := (show graph.Adj 0 40 by decide).reachable
  have reach18 := reach40.trans (show graph.Adj 40 18 by decide).reachable
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0,fun v => ?_⟩
  rcases joins v with rfl | e | e | e | e
  · rfl
  · exact e.reachable
  · exact reach40.trans e.reachable
  · exact reach18.trans e.reachable
  · exact (show graph.Adj 0 6 by decide).reachable.trans e.reachable

private theorem max_edges : edgesOn graph (maxSet graph) = 0 := by
  have none : ∀ u v : Vertex, 36 ≤ u.val → 36 ≤ v.val → ¬ graph.Adj u v := by decide
  unfold edgesOn
  rw [filter_eq_empty_iff.mpr ?_]
  · rfl
  · rintro ⟨u,v⟩ huv
    obtain ⟨hu,hv⟩ := mem_product.mp huv
    exact none u v ((max_mem _).mp hu) ((max_mem _).mp hv)

private theorem alpha_le_two : alphaOn graph (maxSet graph)ᶜ ≤ 2 := by
  apply csSup_le'
  rintro n ⟨D,sub,ind,rfl⟩
  have core {u : Vertex} (hu : u ∈ D) : u.val < 36 :=
    Nat.lt_of_not_ge (fun hm => (mem_compl.mp (sub hu)) ((max_mem _).mpr hm))
  have same : ∀ a b : Vertex, a ≠ b → a.val < 36 → b.val < 36 →
      a.val/18 = b.val/18 → graph.Adj a b := by decide
  by_contra! large
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp large
  have A := core ha
  have B := core hb
  have C := core hc
  by_cases eq : a.val/18 = b.val/18
  · exact ind _ ha _ hb (same _ _ ab A B eq)
  by_cases eq' : a.val/18 = c.val/18
  · exact ind _ ha _ hc (same _ _ ac A C eq')
  exact ind _ hb _ hc (same _ _ bc B C (by omega))

private theorem missed_pair : ∀ u v : Vertex, ¬graph.Adj u v →
    ∃ w, w ≠ u ∧ w ≠ v ∧ ¬graph.Adj w u ∧ ¬graph.Adj w v := by decide +kernel

private theorem not_dom_pair (u v : Vertex) (ind : Independent graph {u,v}) :
    ¬Dominates graph {u,v} := by
  have ne := ind u (by simp) v (by simp)
  obtain ⟨w,wu,wv,noU,noV⟩ := missed_pair u v ne
  intro dom
  rcases dom w with inside | ⟨y,hy,e⟩
  · simp [wu,wv] at inside
  · rcases mem_insert.mp hy with rfl | hy
    · exact noU e
    · exact noV (mem_singleton.mp hy ▸ e)

private def triple : Finset Vertex := {0,18,36}

private theorem triple_properties : Independent graph triple ∧ Dominates graph triple ∧ triple.card = 3 := by
  unfold Independent Dominates
  decide

private theorem i_eq_three : iNum graph = 3 := by
  obtain ⟨ind,dom,card⟩ := triple_properties
  have non : {n | ∃ D : Finset Vertex, Independent graph D ∧ Dominates graph D ∧ D.card = n}.Nonempty :=
    ⟨3,triple,ind,dom,card⟩
  apply le_antisymm (Nat.sInf_le (s := {n | ∃ D : Finset Vertex, Independent graph D ∧ Dominates graph D ∧ D.card = n}) ⟨triple,ind,dom,card⟩)
  obtain ⟨D,hi,hd,size⟩ := Nat.sInf_mem non
  change D.card = iNum graph at size
  by_contra h
  have small : iNum graph < 3 := Nat.lt_of_not_ge h
  have casesD : D.card = 0 ∨ D.card = 1 ∨ D.card = 2 := by omega
  rcases casesD with zero | one | two
  · obtain rfl := card_eq_zero.mp zero
    simpa using hd 0
  · obtain ⟨u,rfl⟩ := card_eq_one.mp one
    exact not_dom_pair u u (by simpa using hi) (by simpa using hd)
  · obtain ⟨u,v,_,rfl⟩ := card_eq_two.mp two
    exact not_dom_pair u v hi hd

theorem counterexample422a : graph.Connected ∧ 3 < Fintype.card Vertex ∧
    ¬(iNum graph ≤ alphaOn graph (maxSet graph)ᶜ + 2 * (edgesOn graph (maxSet graph) / 3)) := by
  refine ⟨connected,by decide,?_⟩
  rw [i_eq_three,max_edges]
  have bound := alpha_le_two
  omega

#print axioms counterexample422a
end Graffiti422a
