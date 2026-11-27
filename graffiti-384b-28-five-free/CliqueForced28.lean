import ThreeTrials28

namespace Graffiti384b.Sparse28
open Finset SimpleGraph HighEar Four28 Core28 EarFrame33
open private Four28.core_data Four28.ear_one from FourFrontier28
open private CubicShore.square_frame from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the 29-type, 28-nonleaf profile, the catalogue inequality holds
whenever the triangle-edge graph of the induced core has no five-clique. -/
theorem five_free_bound (ty : (types G).card=29) (nl : (nonleaves G).card=28)
    (free : (triangleEdges (G.induce (nonleaves G:Set V))).CliqueFree 5) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  let J := triangleEdges (G.induce (nonleaves G:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data G ty nl bad
  obtain ⟨_,_,_,⟨e,a,b,_,ab,en,_⟩,_⟩ := Core28.original G ty nl bad
  obtain ⟨⟨s,sm⟩,_,_,_,T,Y,_,_,u,v,_,_,du,dv,su,sv,_,_⟩ :=
    HighSquare28.disjoint_frontier G ty nl bad free e a b ab en
  obtain ⟨se,as',bs⟩ := (additional_mem J).mp sm
  have ea : J.Adj e a := (J.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eb : J.Adj e b := (J.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  let P : Finset _ := {a,b}
  let R : Finset _ := {e,s}
  have fr' := CubicShore.square_frame J ea eb as' bs se.symm ab.ne
  have fr : Frame J P R := ⟨fr'.1.symm,fr'.2.2,fr'.2.1⟩
  have ps : P.card=2 := card_pair ab.ne
  have rs : R.card=2 := card_pair se.symm
  have sr : s∈R := mem_insert_of_mem (mem_singleton_self _)
  have er : e∈P∪R := mem_union_right _ (mem_insert_self ..)
  have cardV : Fintype.card ↥(nonleaves G:Set V)=28 := n
  change 14≤gamma J at half
  have ws : (P∪R)ᶜ.card=24 := by rw [card_compl,card_union_of_disjoint fr.1,ps,rs,cardV]
  have contact (x : _) (xm : x∈(P∪R)ᶜ) : nbr J x R=nbr J x {s} := by
    have no : ¬J.Adj x e := by
      intro ed
      have ep : x∈J.neighborFinset e := (J.mem_neighborFinset ..).mpr ed.symm
      change J.neighborFinset e=P at en
      exact mem_compl.mp xm (mem_union_left R (en ▸ ep))
    simp [nbr,R,filter_insert,no]
  have needed := total_needed J fr ps rs sr ws half
  have allowed := total_allowed J fr ps sr ws er pos fi (Four28.ear_one J ab.ne en pos) su sv du dv free (by omega) contact
  exact (by decide : ¬ 27111480≤26398538) (needed.trans allowed)

/-- Any failure of this exact nonleaf and diversity profile therefore
contains a five-clique even after all nontriangle edges are deleted. -/
theorem five_clique_required (ty : (types G).card=29) (nl : (nonleaves G).card=28)
    (bad : bound G<gamma G) : ∃ C,(triangleEdges (G.induce (nonleaves G:Set V))).IsNClique 5 C := by
  by_contra! h
  exact (Nat.not_lt_of_ge (five_free_bound G ty nl h)) bad

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.five_free_bound
#print axioms Graffiti384b.Sparse28.five_clique_required
