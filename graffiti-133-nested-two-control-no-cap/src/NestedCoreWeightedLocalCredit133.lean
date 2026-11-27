import C7MultiWeightedLocal133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack Graffiti133MultiWeighted
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem marked_incidence (H : Hole G 7) (x : V) :
    (markedNeighbors H x).card≤triangleIncidence G x ∧
    ((∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) →
      (markedNeighbors H x).card+1≤triangleIncidence G x) := by
  classical
  let M := markedNeighbors H x
  let T := (G.cliqueFinset 3).filter (fun A=>x∈A)
  have fact (y : V) (ym : y∈M) : Outside H.c y ∧ G.Adj x y ∧
      ∃ i∈contactSet H x,G.Adj y (H.c i) := by
    obtain ⟨e,t⟩ := Finset.mem_filter.mp ym
    have h := (Finset.mem_filter.mp e).2
    exact ⟨h.1,h.2,t⟩
  choose tag tagMem tagAdj using (fun y : {y // y∈M} => (fact y.val y.property).2.2)
  let f (y : V) : Finset V :=
    if ym : y∈M then {x,y,H.c (tag ⟨y,ym⟩)} else ∅
  have eval (y : V) (ym : y∈M) : f y={x,y,H.c (tag ⟨y,ym⟩)} := dif_pos ym
  have inj : Set.InjOn f (M : Set V) := by
    intro y ym z zm eq
    change y∈M at ym
    change z∈M at zm
    have mem : y∈f y := by rw [eval y ym]; simp
    rw [eq,eval z zm] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with e|e|e
    · exact ((fact y ym).2.1.ne e.symm).elim
    · exact e
    · exact ((fact y ym).1 _ e).elim
  have cardIm : (M.image f).card=M.card := Finset.card_image_of_injOn inj
  have sub : M.image f⊆T := by
    intro A am
    obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp am
    rw [eval y ym]
    exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨(fact y ym).2.1,(mem_contactSet H _ _).mp (tagMem ⟨y,ym⟩),tagAdj ⟨y,ym⟩⟩),by simp⟩
  have first := Finset.card_le_card sub
  rw [cardIm] at first
  refine ⟨first,?_⟩
  rintro ⟨i,im,j,jm,ij⟩
  let A : Finset V := {x,H.c i,H.c j}
  have am : A∈T := Finset.mem_filter.mpr
    ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨(mem_contactSet H _ _).mp im,(mem_contactSet H _ _).mp jm,(H.adj i j).mpr ij⟩),by simp [A]⟩
  have an : A∉M.image f := by
    intro ai
    obtain ⟨y,ym,eq⟩ := Finset.mem_image.mp ai
    have m : y∈A := by rw [←eq,eval y ym]; simp
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with e|e|e
    · exact (fact y ym).2.1.ne e.symm
    · exact (fact y ym).1 i e
    · exact (fact y ym).1 j e
  have sz := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨am,sub⟩)
  rw [Finset.card_insert_of_not_mem an,cardIm] at sz
  exact sz



theorem improved_multi_local_credit (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x) (multi : 2≤(contactSet H x).card)
    (priority : Bool)
    (adjcap : ((contactSet H x).card=2 ∧ ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) →
      (exteriorNeighbors H x).card≤2)
    (farcap : priority=true → (contactSet H x).card=2 →
      (¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) →
      ((exteriorNeighbors H x) \ markedNeighbors H x).card=0) :
    2*row G x Finset.univ ≤ 4+3*triangleIncidence G x+
      (if (contactSet H x).card=2 then
        if (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) then 1
        else if priority then 0 else 2
       else 0) := by
  classical
  have deg := split_degree_contacts H x
  have marked := marked_incidence H x
  have regular := local_multi_weight H h4 dom x off multi
  by_cases two : (contactSet H x).card=2
  · rw [if_pos two]
    by_cases adj : ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j
    · rw [if_pos adj]
      have t := marked.2 adj
      have d := adjcap ⟨two,adj⟩
      omega
    · rw [if_neg adj]
      by_cases pr : priority=true
      · rw [if_pos pr]
        have m := farcap pr two adj
        have size := Finset.card_sdiff_add_card_eq_card
          (Finset.filter_subset _ (exteriorNeighbors H x) : markedNeighbors H x⊆exteriorNeighbors H x)
        change ((exteriorNeighbors H x) \ markedNeighbors H x).card+(markedNeighbors H x).card=(exteriorNeighbors H x).card at size
        omega
      · rw [if_neg pr]
        simp only [two,adj,if_false,show ¬(2:Nat)=3 by decide,add_zero] at regular
        exact regular
  · rw [if_neg two]
    rcases geometry_cap _ (contacts_are_allowed H h4 x off) multi with ⟨e,_⟩|⟨e,_⟩
    · exact (two e).elim
    · simp only [e,if_true,add_zero] at regular
      omega

#print axioms improved_multi_local_credit
end Graffiti133NestedWeightedCore
