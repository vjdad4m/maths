import PortBudget180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With four neighbors and allowance two, an independence bound of two
in the neighborhood forces both deletions to be neighbors. There is no
outside deletion and no search for a larger retained independent set. -/
theorem four_ports_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a : V)
    (ak : a∈A∩insert r (parity G r p)) (N : Finset V) (nb : ∀ x,x∈N ↔ G.Adj a x)
    (four : N.card=4) (two : allowance G r p A=2) (small : ∀ H⊆N,Indep G H → H.card≤2) :
    Protected G r p A ↔ ∃ c : V→Bool,ProperOn G (outer a N) c ∧
      ∃ u∈N,∃ v∈N,u≠v ∧ PortsFit G (outer a N) {u,v} c := by
  classical
  rw [protected_ports_iff G gc hn r p A ai a ak N nb]
  constructor
  · rintro ⟨F,H,_,_,sub,budget,c,cp,pairs⟩
    have fit := (ports_pairwise G _ H c).mpr pairs
    have limit := small H sub fit.1
    have size := card_sdiff_add_card_eq_card sub
    have fe : F=∅ := card_eq_zero.mp (by omega)
    subst F
    rw [sdiff_empty] at cp fit
    obtain ⟨u,v,ne,eq⟩ := card_eq_two.mp (show H.card=2 by have := card_empty (α:=V);omega)
    subst H
    exact ⟨c,cp,u,sub (mem_insert_self ..),v,sub (mem_insert_of_mem (mem_singleton_self _)),ne,fit⟩
  · rintro ⟨c,cp,u,un,v,vn,uv,fit⟩
    have sub : ({u,v}:Finset V)⊆N := insert_subset un (singleton_subset_iff.mpr vn)
    have size := card_sdiff_add_card_eq_card sub
    rw [card_pair uv,four] at size
    refine ⟨∅,{u,v},empty_subset _,(by simp),sub,by simp only [card_empty,zero_add,two];omega,c,?_,?_⟩
    · simpa only [sdiff_empty] using cp
    · simpa only [sdiff_empty] using (ports_pairwise G (outer a N) {u,v} c).mp fit

omit [Fintype V] in
/-- The neighborhood independence premise follows, for example, from a
partition into two adjacent pairs. -/
theorem two_edges_cap (G : SimpleGraph V) (x y u v : V) (xy : G.Adj x y) (uv : G.Adj u v)
    (H : Finset V) (sub : H⊆({x,y}∪{u,v}:Finset V)) (hi : Indep G H) : H.card≤2 := by
  classical
  have half (i j : V) (ed : G.Adj i j) : (H∩{i,j}).card≤1 := by
    by_cases im : i∈H
    · have jm : j∉H := fun jm => hi i im j jm ed.ne ed
      have inc : H∩{i,j}⊆{i} := fun t tm => mem_singleton.mpr ((mem_insert.mp (mem_inter.mp tm).2).resolve_right
        (fun eq => jm ((mem_singleton.mp eq) ▸ (mem_inter.mp tm).1)))
      exact (card_le_card inc).trans_eq (card_singleton i)
    · have inc : H∩{i,j}⊆{j} := fun t tm => (mem_insert.mp (mem_inter.mp tm).2).resolve_left
        (fun eq => im (eq ▸ (mem_inter.mp tm).1))
      exact (card_le_card inc).trans_eq (card_singleton j)
  have all : H=(H∩{x,y})∪(H∩{u,v}) := by rw [←inter_union_distrib_left,inter_eq_left.mpr sub]
  have bound := card_union_le (H∩{x,y}) (H∩{u,v})
  rw [←all] at bound
  have h := half x y xy
  have k := half u v uv
  omega

#print axioms four_ports_iff
#print axioms two_edges_cap
end Minimal180.PairRepair
