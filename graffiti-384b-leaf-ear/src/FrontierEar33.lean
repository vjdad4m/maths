import SpanningEar33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph
open private TrianglePrune.reach_closed from TrianglePrune384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Global diversity-33 reduction. The first graph is induced. The final
connected leaf-and-ear graph is spanning inside it and preserves its scores. -/
theorem diversity33_frontier (conn : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G)
    (t : (types G).card=33) :
    ∃ (s : Finset V) (F : SimpleGraph s) (d : DecidableRel F.Adj), letI := d
      s.card=33 ∧ F≤G.induce (s : Set V) ∧ F.Connected ∧ bound F<gamma F ∧
      types F=types G ∧ (∀ v : s,trianglesAt F v=trianglesAt (G.induce (s : Set V)) v) ∧
      Function.Injective (trianglesAt F) ∧ ¬F.CliqueFree 5 ∧
      ∃ z a y,trianglesAt F z=0 ∧ F.neighborFinset z={a} ∧
        (∀ w,F.degree w=1 → w=z) ∧ trianglesAt F y=1 ∧ ¬F.Adj z y ∧
        F.degree y=2 ∧ (∀ w,F.degree w=2 → w=y) := by
  classical
  obtain ⟨s,sz,jc,same,inj,_,⟨z,zero,_⟩,fail⟩ := OneEar.diversity33_failure G conn hn bad t
  let J := G.induce (s : Set V)
  have n : Fintype.card s=33 := (Fintype.card_coe s).trans sz
  have tj : (types J).card=33 := (congrArg card same).trans t
  have edge : ∃ a,J.Adj z a := by
    apply Classical.byContradiction; intro none
    have all (v : s) : v∈({z} : Finset s) := TrianglePrune.reach_closed J {z} (by
      intro u um w uw; obtain rfl := mem_singleton.mp um; exact (none ⟨w,uw⟩).elim) (mem_singleton_self _) (jc z v)
    have num := congrArg card (eq_univ_of_forall all)
    rw [card_singleton,card_univ,n] at num; omega
  obtain ⟨a,za⟩ := edge
  obtain ⟨F,d,fg,fc,fb,sc,leaf,⟨y,one,no,dy,only⟩⟩ := spanning_leaf_ear J n tj jc fail inj zero za
  letI := d
  have ty : types F=types J := congrArg (fun f : s → ℕ => univ.image f) (funext sc)
  have distinct : Function.Injective (trianglesAt F) := fun u v h =>
    inj ((sc u).symm.trans (h.trans (sc v)))
  have five : ¬F.CliqueFree 5 := fun free => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free F fc
    (by change 2<Fintype.card s; rw [n]; decide) (by rw [ty,tj]) free)) fb
  refine ⟨s,F,d,sz,fg,fc,fb,ty.trans same,sc,distinct,five,z,a,y,(sc z).trans zero,leaf,?_,
    (sc y).trans one,fun adj => no (fg adj),dy,only⟩
  intro w dw
  have up := Repair.triangles_le_choose F w
  rw [dw] at up
  apply distinct
  rw [sc z,zero]
  exact Nat.eq_zero_of_le_zero up

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.diversity33_frontier
