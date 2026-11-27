import ZeroNeighbor33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph PositiveCore33
open private OneEar.deg2 from OneEarFinish384b
open private PositiveCore33.gamma_mono from LeafReduction33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Retaining triangle edges gives a spanning graph with the same scores.
Every positive-only such graph satisfies the normal-form degree estimate. -/
theorem supported_degree (base : V) (pos : ∀ v,0<trianglesAt G v) (v : V) :
    (backbone G base).degree v≤2*trianglesAt G v := by
  classical
  let J := backbone G base
  have jp (u : V) : 0<trianglesAt J u := (backbone_scores G base u) ▸ pos u
  have normal : TrianglePrune.Normal J := by
    refine ⟨fun u _ h _ => ((jp u).ne' h).elim,fun u h => ((jp u).ne' h).elim,?_⟩
    intro u w edge _ _
    obtain ⟨uw,y,uy,wy⟩ := (backbone_adj G).mp edge
    exact ⟨y,(backbone_adj G).mpr ⟨uy,w,uw,wy.symm⟩,(backbone_adj G).mpr ⟨wy,u,uw.symm,uy.symm⟩⟩
  have empty : ((J.neighborFinset v).filter (fun w => trianglesAt J w=0))=∅ :=
    filter_eq_empty_iff.mpr (fun w _ => (jp w).ne')
  have d := (Minimal.degree_score J normal v (jp v)).1
  rw [empty,card_empty,Nat.add_zero,backbone_scores G base v] at d
  exact d

/-- Every five-clique and every edge of the ear triangle survive retaining
only triangle edges. This forces five supported neighbors at either endpoint. -/
theorem supported_endpoints {e a c : V} (n : Fintype.card V=32) (de : G.degree e=2)
    (ea : G.Adj e a) (ec : G.Adj e c) (ac : G.Adj a c)
    (pos : ∀ v,0<trianglesAt G v) (inj : Function.Injective (trianglesAt G))
    {C : Finset V} (cl : G.IsNClique 5 C) (hi : 16≤gamma G) :
    5≤(backbone G e).degree a ∧ 5≤(backbone G e).degree c := by
  classical
  let J := backbone G e
  have le : J≤G := fun _ _ h => ((backbone_adj G).mp h).1
  have jc : J.IsNClique 5 C := by
    refine ⟨?_,cl.2⟩
    intro u um v vm ne
    obtain ⟨w,wm,wu⟩ := exists_ne_of_one_lt_card (by rw [card_erase_of_mem vm,cl.2]; decide : 1<(C.erase v).card) u
    obtain ⟨wv,wc⟩ := mem_erase.mp wm
    exact (backbone_adj G).mpr ⟨cl.1 um vm ne,w,cl.1 um wc wu.symm,cl.1 vm wc wv.symm⟩
  have ja : J.Adj e a := (backbone_adj G).mpr ⟨ea,c,ec,ac⟩
  have jb : J.Adj e c := (backbone_adj G).mpr ⟨ec,a,ea,ac.symm⟩
  have ab : J.Adj a c := (backbone_adj G).mpr ⟨ac,e,ea.symm,ec.symm⟩
  have sub : J.neighborFinset e⊆G.neighborFinset e := fun w wm =>
    (G.mem_neighborFinset _ _).mpr (le ((J.mem_neighborFinset _ _).mp wm))
  have cap := card_le_card sub
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de] at cap
  have low := OneEar.deg2 J ac.ne ja jb
  have dj : J.degree e=2 := by omega
  have pj (u : V) : 0<trianglesAt J u := (backbone_scores G e u) ▸ pos u
  have ij : Function.Injective (trianglesAt J) := fun u v eq =>
    inj ((backbone_scores G e u).symm.trans (eq.trans (backbone_scores G e v)))
  exact EarPalette.extremal_endpoints J n dj ja jb ab pj ij ⟨C,jc⟩
    (hi.trans (PositiveCore33.gamma_mono G J le))

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.supported_degree
#print axioms Graffiti384b.ForcedCubics.supported_endpoints
