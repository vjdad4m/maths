import Diversity35_384b
import CliqueFrontier34_384b
import Below33Boundary384b
import SwitchMargins384b

universe u
namespace Graffiti384b.Frontier34
open Finset SimpleGraph LowSample
open private Repair.triangles_le_choose from Repair384b
open private LowSample.two_degree from LowSample384b
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem minimum_order (res : Minimal.Residual G) : Fintype.card V ≤34 := by
  obtain ⟨r,ord,cap,conn,_,fail⟩ := Diversity35.induced_bound G res.2.1 res.1.1 res.2.2.1
  exact (res.2.2.2.2.2.2.2.2 r.card ⟨r,inferInstance,inferInstance,_,inferInstance,Fintype.card_coe _,ord,conn,fail⟩).trans cap

/-- A least-order counterexample of order 34 has exactly 33 nonleaves
and 33 triangle-count types. -/
theorem boundary (res : Minimal.Residual G) (n : Fintype.card V=34) :
    (nonleaves G).card=33 ∧ (types G).card=33 ∧ ((high G).card=31 ∨ (high G).card=32) := by
  obtain ⟨⟨hn,_⟩,hc,bad,_,odd,_,_,_,least⟩ := res
  have size : (types G).card≤34 := n ▸ (show (types G).card≤Fintype.card V from card_image_le.trans_eq card_univ)
  have q := Below35.nonleaf_cap G (by omega) hc hn bad
  obtain ⟨r,_,cap,ord,conn,_,fail⟩ := Prune.prune_failure G hc hn bad
  have le := least r.card ⟨r,inferInstance,inferInstance,_,inferInstance,Fintype.card_coe _,ord,conn,fail⟩
  have qeq : (nonleaves G).card=33 := by omega
  have t : (types G).card=33 := by
    by_contra no
    have small : (types G).card<33 := by omega
    have up := Below33.nonleaf_cap G small hc hn bad
    omega
  have lb := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) bad)
  exact ⟨qeq,t,by omega⟩

/-- All vertices of degree two in this frontier are ears. When there
are two, the ears have distinct neighborhoods and equal triangle count one. -/
theorem ears (res : Minimal.Residual G) (n : Fintype.card V=34) :
    (twos G).card=33-(high G).card ∧
    (∀ z∈twos G, trianglesAt G z=1) ∧
    (∀ z∈twos G, ∀ w∈twos G, z≠w → G.neighborFinset z≠G.neighborFinset w) := by
  obtain ⟨q,_,_⟩ := boundary G res n
  have sub : high G⊆nonleaves G := fun z hz => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp hz).2; omega⟩
  refine ⟨(card_sdiff sub).trans (congrArg (fun k => k-(high G).card) q),?_,?_⟩
  · intro z zm
    have dz := LowSample.two_degree G zm
    have zero : trianglesAt G z≠0 := by
      intro sc
      have low : (G.neighborFinset z).card≤1 := card_le_one.mpr (fun a ha b hb => res.2.2.2.1.2.1 z sc a b
        ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb))
      rw [card_neighborFinset_eq_degree,dz] at low; omega
    have up := Repair.triangles_le_choose G z
    rw [dz,Nat.choose_self] at up; omega
  · intro z zm w _ ne same
    exact (not_lt_of_ge (Repair.exact_of_twin_degree_two G ne (LowSample.two_degree G zm) same)) res.2.2.1

/-- The number 33 is the only diversity for which the order-34
endpoint is still needed in the induced-counterexample reduction. -/
theorem induced_alternative (hc : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G) :
    ∃ r : Finset V, 2<r.card ∧ (G.induce (r : Set V)).Connected ∧
      types (G.induce (r : Set V))=types G ∧ bound (G.induce (r : Set V))<gamma (G.induce (r : Set V)) ∧
      (r.card≤33 ∨ (r.card=34 ∧ (types G).card=33 ∧ ¬(G.induce (r : Set V)).CliqueFree 5)) := by
  by_cases top : (types G).card=33
  · obtain ⟨r,lo,up,conn,same,fail⟩ := Diversity35.induced_bound G hc hn bad
    have five : ¬(G.induce (r : Set V)).CliqueFree 5 := fun free =>
      (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free _ conn (by change 2<Fintype.card r; rw [Fintype.card_coe]; exact lo)
        (by rw [same,top]) free)) fail
    exact ⟨r,lo,conn,same,fail,by by_cases sm : r.card≤33; exact Or.inl sm; exact Or.inr ⟨by omega,top,five⟩⟩
  · have cap : (types G).card<34 := Nat.lt_of_not_ge (fun h => (not_lt_of_ge (Diversity35.exact_of_at_least_34_types G hc hn h)) bad)
    obtain ⟨r,lo,up,conn,same,fail⟩ := Below33.induced_bound G (by omega) hc hn bad
    exact ⟨r,lo,conn,same,fail,Or.inl up⟩

end Graffiti384b.Frontier34
#print axioms Graffiti384b.Frontier34.minimum_order
#print axioms Graffiti384b.Frontier34.boundary
#print axioms Graffiti384b.Frontier34.ears
#print axioms Graffiti384b.Frontier34.induced_alternative
