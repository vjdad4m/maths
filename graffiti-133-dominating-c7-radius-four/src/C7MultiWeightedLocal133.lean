import C7MultiSmallScopes133
import BicycleExactTriangleCharge133

namespace Graffiti133MultiWeighted
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def markedNeighbors (H : Hole G 7) (x : V) : Finset V :=
  (exteriorNeighbors H x).filter (fun y=>∃ i∈contactSet H x,G.Adj y (H.c i))

theorem clean_neighbor_card (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x) :
    ((exteriorNeighbors H x) \ (markedNeighbors H x)).card≤
      ((cleanSites (contactSet H x)) \ (contactSet H x)).card := by
  classical
  let X := exteriorNeighbors H x \ markedNeighbors H x
  have side (y : V) (hy : y∈X) : Outside H.c y ∧ G.Adj x y ∧
      ¬∃ i∈contactSet H x,G.Adj y (H.c i) := by
    have t := Finset.mem_sdiff.mp hy
    have ext := (Finset.mem_filter.mp t.1).2
    exact ⟨ext.1,ext.2,fun q=>t.2 (Finset.mem_filter.mpr ⟨t.1,q⟩)⟩
  choose tag adj using (fun y : {y // y∈X}=>dom y.val (side y.val y.property).1)
  let f (y : V) := if hm : y∈X then tag ⟨y,hm⟩ else 0
  have eval (y : V) (hy : y∈X) : f y=tag ⟨y,hy⟩ := dif_pos hy
  change X.card≤_
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    change y∈X at hy
    rw [eval y hy]
    have s := side y hy
    exact Finset.mem_sdiff.mpr ⟨neighbor_sites_clean H h4 off s.1 s.2.1 _ (adj ⟨y,hy⟩),
      fun z=>s.2.2 ⟨tag ⟨y,hy⟩,z,adj ⟨y,hy⟩⟩⟩
  · intro y hy z hz eq
    change y∈X at hy
    change z∈X at hz
    rw [eval y hy,eval z hz] at eq
    exact h4 x (H.c (tag ⟨y,hy⟩)) y z (off _) (side y hy).2.1 (adj ⟨y,hy⟩).symm
      (side z hz).2.1 (by rw [eq]; exact (adj ⟨z,hz⟩).symm)

private theorem marked_triangle_count (H : Hole G 7) (x : V) :
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

theorem local_multi_weight (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x) (multi : 2≤(contactSet H x).card) :
    (2*(row G x Finset.univ) + (if (contactSet H x).card=3 then 1 else 0)) ≤
      4 + 3*triangleIncidence G x +
        (if (contactSet H x).card=3 then 0 else
          if (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) then 3 else 2) := by
  classical
  let A := contactSet H x
  let M := markedNeighbors H x
  let B := exteriorNeighbors H x
  have sub : M⊆B := Finset.filter_subset _ _
  have size := Finset.card_sdiff_add_card_eq_card sub
  have cap := clean_neighbor_card H h4 dom x off
  have degree := split_degree_contacts H x
  have tri := marked_triangle_count H x
  rcases geometry_profits A (contacts_are_allowed H h4 x off) multi with
    ⟨ac,adj,cap'⟩|⟨ac,no,cap'⟩|⟨ac,adj,cap'⟩
  · have ad := tri.2 adj
    simp only [show (contactSet H x).card=2 from ac,show (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) from adj,
      if_true,if_false,show ¬(2:Nat)=3 by decide,add_zero]
    change (B\M).card+M.card=B.card at size
    change (B\M).card≤(cleanSites A\A).card at cap
    change row G x Finset.univ=A.card+B.card at degree
    change M.card+1≤triangleIncidence G x at ad
    omega
  · have nad : ¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j := by
      rintro ⟨i,hi,j,hj,h⟩
      exact no i hi j hj h
    simp only [show (contactSet H x).card=2 from ac,nad,if_false,show ¬(2:Nat)=3 by decide,add_zero]
    have ad := tri.1
    change (B\M).card+M.card=B.card at size
    change (B\M).card≤(cleanSites A\A).card at cap
    change row G x Finset.univ=A.card+B.card at degree
    change M.card≤triangleIncidence G x at ad
    omega
  · have ad := tri.2 adj
    simp only [show (contactSet H x).card=3 from ac,if_true,add_zero]
    change (B\M).card+M.card=B.card at size
    change (B\M).card≤(cleanSites A\A).card at cap
    change row G x Finset.univ=A.card+B.card at degree
    change M.card+1≤triangleIncidence G x at ad
    omega

#print axioms local_multi_weight
end Graffiti133MultiWeighted
