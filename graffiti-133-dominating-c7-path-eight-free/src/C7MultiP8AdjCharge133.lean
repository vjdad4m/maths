import C7MultiWeightedLocal133
import P8ModelLift133

namespace Graffiti133MultiP8
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133Eighth
  Graffiti133P8Heawood Graffiti133MultiWeighted Graffiti133ExteriorSlack Graffiti133BicycleCharge
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def atTag (j k : Fin 7) : Bool := decide (k=j)
def lastTag (j : Fin 7) (k : Fin 8) : Bool := decide (k.val=j.val)

def DoubleLeaf (i j : Fin 7) : Fin 9→Fin 9→Prop :=
  ext (ext (@Cyclic 7) (atTag i)) (lastTag j)

instance (i j : Fin 7) : DecidableRel (DoubleLeaf i j) :=
  inferInstanceAs (DecidableRel (ext (ext (@Cyclic 7) (atTag i)) (lastTag j)))

def ci (j : Fin 7) : Fin 9 := Fin.castLE (by decide) j

def leafArc (i j : Fin 7) : Fin 8→Fin 9 :=
  if j=i+2 then ![7,ci i,ci (i-1),ci (i-2),ci (i-3),ci (i-4),ci (i-5),8]
  else ![7,ci i,ci (i+1),ci (i+2),ci (i+3),ci (i+4),ci (i+5),8]

theorem leaf_arc_checks : ∀ i j : Fin 7,i≠j → (∃ k,Cyclic i k ∧ Cyclic j k) →
    (∀ a b : Fin 8,leafArc i j a=leafArc i j b→a=b) ∧
    (∀ a b : Fin 8,a<b → (DoubleLeaf i j (leafArc i j a) (leafArc i j b) ↔ a.val+1=b.val)) :=
  by decide

theorem p8_free_two_step_singletons_adjacent
    (H : Hole G 7) (h8 : ¬∃ p : Fin 8→V,InducedPath G p)
    (x y : V) (xo : Outside H.c x) (yo : Outside H.c y) (xy : x≠y)
    (i j : Fin 7) (ij : i≠j) (two : ∃ k,Cyclic i k ∧ Cyclic j k)
    (hx : ∀ k,G.Adj x (H.c k) ↔ k=i) (hy : ∀ k,G.Adj y (H.c k) ↔ k=j) :
    G.Adj x y := by
  by_contra noxy
  let M : Model G (@Cyclic 7) := ⟨H.c,H.inj,fun a b=>(H.adj a b).symm⟩
  have xi (k : Fin 7) : atTag i k=true ↔ G.Adj x (M.f k) := by
    simpa [atTag,M] using (hx k).symm
  let N := M.extend x xo xi
  have fresh : N.Fresh y := by
    intro k
    refine Fin.lastCases ?_ (fun z=>?_) k
    · rw [show N.f (Fin.last 7)=x from Model.extend_f_new M x xo xi]
      exact xy.symm
    · simpa [N,M] using yo z
  have yAdj (k : Fin 8) : lastTag j k=true ↔ G.Adj y (N.f k) := by
    refine Fin.lastCases ?_ (fun z=>?_) k
    · rw [show N.f (Fin.last 7)=x from Model.extend_f_new M x xo xi]
      have jj : (7:Nat)≠j.val := by have := j.isLt; omega
      simp only [lastTag,decide_eq_true_eq]
      refine ⟨fun q=>(jj q).elim,fun q=>(noxy q.symm).elim⟩
    · rw [show N.f z.castSucc=M.f z from Model.extend_f_old M x xo xi z]
      simpa [lastTag,M,Fin.ext_iff] using (hy z).symm
  let L : Model G (DoubleLeaf i j) := N.extend y fresh yAdj
  have cert := leaf_arc_checks i j ij two
  exact h8 ⟨L.f ∘ leafArc i j,L.inj.comp (fun a b e=>cert.1 a b e),
    fun a b lt=>(L.adj ..).symm.trans (cert.2 a b lt)⟩

#print axioms p8_free_two_step_singletons_adjacent
end Graffiti133MultiP8


namespace Graffiti133MultiP8
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133ExteriorSlack Graffiti133BicycleCharge
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem saturated_exterior_has_singletons_at_all_clean_sites
    (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x)
    (full : (cleanSites (contactSet H x)).card≤(exteriorNeighbors H x).card) :
    ∀ i∈cleanSites (contactSet H x),∃ y,Outside H.c y ∧ G.Adj x y ∧
      ∀ j,G.Adj y (H.c j) ↔ j=i := by
  classical
  let E := exteriorNeighbors H x
  let A := cleanSites (contactSet H x)
  have prop (y : V) (ym : y∈E) : Outside H.c y ∧ G.Adj x y := (Finset.mem_filter.mp ym).2
  choose tag ed using (fun y : {y // y∈E}=>dom y.val (prop y.val y.property).1)
  let f (y : V) := if ym : y∈E then tag ⟨y,ym⟩ else 0
  have ev (y : V) (ym : y∈E) : f y=tag ⟨y,ym⟩ := dif_pos ym
  have inj : Set.InjOn f (E : Set V) := by
    intro y ym z zm eq
    change y∈E at ym
    change z∈E at zm
    rw [ev y ym,ev z zm] at eq
    exact h4 x (H.c (tag ⟨y,ym⟩)) y z (off _) (prop y ym).2 (ed ⟨y,ym⟩).symm
      (prop z zm).2 (by rw [eq]; exact (ed ⟨z,zm⟩).symm)
  have sub : E.image f⊆A := by
    intro i im
    obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp im
    rw [ev y ym]
    exact neighbor_sites_clean H h4 off (prop y ym).1 (prop y ym).2 _ (ed ⟨y,ym⟩)
  have eq : E.image f=A := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Finset.card_image_of_injOn inj]
    exact full

  have via (i : Fin 7) (im : i∈A) : ∃ y∈E,f y=i := by
    rw [←eq] at im
    exact Finset.mem_image.mp im
  intro i im
  obtain ⟨y,ym,yi⟩ := via i im
  have htag : tag ⟨y,ym⟩=i := (ev y ym).symm.trans yi
  refine ⟨y,(prop y ym).1,(prop y ym).2,?_⟩
  intro j
  constructor
  · intro yj
    have jm : j∈A := neighbor_sites_clean H h4 off (prop y ym).1 (prop y ym).2 j yj
    obtain ⟨z,zm,zj⟩ := via j jm
    have ze : G.Adj z (H.c j) := by rw [←zj,ev z zm]; exact ed ⟨z,zm⟩
    have yz := h4 x (H.c j) y z (off _) (prop y ym).2 yj.symm (prop z zm).2 ze.symm
    exact zj.symm.trans ((congrArg f yz).symm.trans yi)
  · rintro rfl
    rw [←htag]
    exact ed ⟨y,ym⟩


theorem adjacent_clean_sites_contain_distance_two :
    ∀ A : Finset (Fin 7),C4Allowed A→A.card=2→(∃ i∈A,∃ j∈A,Cyclic i j) →
      ∃ i∈cleanSites A,∃ j∈cleanSites A,i≠j ∧ ∃ k,Cyclic i k ∧ Cyclic j k := by decide

private theorem incidence_cycle_and_outer_triangles (H : Hole G 7) (x : V)
    (around : ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j)
    {y z : V} (yo : Outside H.c y) (xy : G.Adj x y) (xz : G.Adj x z) (yz : G.Adj y z) :
    2≤triangleIncidence G x := by
  classical
  obtain ⟨i,im,j,jm,ij⟩ := around
  let A : Finset V := {x,H.c i,H.c j}
  let B : Finset V := {x,y,z}
  let T := (G.cliqueFinset 3).filter (fun t=>x∈t)
  have am : A∈T := Finset.mem_filter.mpr
    ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨(mem_contactSet H _ _).mp im,
        (mem_contactSet H _ _).mp jm,(H.adj i j).mpr ij⟩),by simp [A]⟩
  have bm : B∈T := Finset.mem_filter.mpr
    ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨xy,xz,yz⟩),by simp [B]⟩
  have ne : A≠B := by
    intro e
    have m : y∈A := by rw [e]; simp [B]
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with r|r|r
    · exact xy.ne r.symm
    · exact yo i r
    · exact yo j r
  change 2≤T.card
  exact Finset.one_lt_card.mpr ⟨A,am,B,bm,ne⟩

private theorem incidence_cycle_triangle (H : Hole G 7) (x : V)
    (around : ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) :
    1≤triangleIncidence G x := by
  classical
  obtain ⟨i,im,j,jm,ij⟩ := around
  apply Finset.card_pos.mpr
  exact ⟨{x,H.c i,H.c j},Finset.mem_filter.mpr
    ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨(mem_contactSet H _ _).mp im,
        (mem_contactSet H _ _).mp jm,(H.adj i j).mpr ij⟩),by simp⟩⟩

theorem P8_free_adjacent_multi_charge (H : Hole G 7)
    (h4 : FourCycleFree G) (h8 : ¬∃ p : Fin 8→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x) (two : (contactSet H x).card=2)
    (around : ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) :
    2*row G x Finset.univ ≤4+3*triangleIncidence G x+1 := by
  have permitted := contacts_are_allowed H h4 x off
  have erow := split_degree_contacts H x
  by_cases small : (exteriorNeighbors H x).card≤2
  · have one := incidence_cycle_triangle H x around
    omega
  · have geom : (cleanSites (contactSet H x)).card=3 := by
      rcases geometry_cap _ permitted two.ge with ⟨_,h⟩|⟨q,_⟩
      · exact h
      · omega
    have cap := exterior_degree_capacity H h4 dom x off
    have full : (cleanSites (contactSet H x)).card≤(exteriorNeighbors H x).card := by omega
    have exist := saturated_exterior_has_singletons_at_all_clean_sites H h4 dom x off full
    obtain ⟨i,im,j,jm,ij,twoStep⟩ := adjacent_clean_sites_contain_distance_two _ permitted two around
    obtain ⟨y,yo,xy,ySite⟩ := exist i im
    obtain ⟨z,zo,xz,zSite⟩ := exist j jm
    have ne : y≠z := by
      intro e
      subst z
      exact ij ((zSite i).mp ((ySite i).mpr rfl))
    have yz := p8_free_two_step_singletons_adjacent H h8 y z yo zo ne i j ij twoStep ySite zSite
    have tri := incidence_cycle_and_outer_triangles H x around yo xy xz yz
    omega

#print axioms saturated_exterior_has_singletons_at_all_clean_sites
#print axioms P8_free_adjacent_multi_charge
end Graffiti133MultiP8
