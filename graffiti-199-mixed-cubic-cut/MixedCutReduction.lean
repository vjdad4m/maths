import AdjacentComplete
import CrossingCubicProfile

open private exists_two_of_natCard from CrossingCubicProfile
open private large_component_of_edge from CrossingCutReduction

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

namespace CubicMixedCut

theorem cubic_root (M : CubicMixedCut G) : G.degree M.r = 3 := by
  classical
  have actual : G.neighborFinset M.r = ({M.a,M.b,M.c} : Finset V) := by
    ext x
    simp only [G.mem_neighborFinset,M.neighbors,Finset.mem_insert,Finset.mem_singleton]
  rw [← G.card_neighborFinset_eq_degree,actual]
  rw [Finset.card_insert_of_not_mem (by simp [M.apart_ne M.aA M.bB,M.apart_ne M.aA M.cB]),
    Finset.card_pair M.bc]

/-- The independent-cubic hypothesis supplies the degree-four bounds on
the two neighbors of the cubic port in the nonclique component. -/
theorem traceable_of_independent_cubics (M : CubicMixedCut G)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b) : Traceable G := by
  have high (v : V) (edge : G.Adj M.r v) : 4 ≤ G.degree v := by
    have low := degree_of_small_deletion_preconnected (G := G)
      (by have n := conn.1; omega : 4 ≤ Fintype.card V) (fun D h => (conn.2 D h).preconnected) v
    have ne : G.degree v ≠ 3 := fun eq => ind M.r v M.cubic_root eq edge
    omega
  exact M.traceable_of_mixed_cut conn budget (high _ M.rb) (high _ M.rc)

end CubicMixedCut

private theorem build_mixed {D : Finset V} {r : V} {A B : Set V}
    (rD : r ∈ D) (cutSize : D.card = 3) (degree : G.degree r = 3)
    (bigA : 3 ≤ Nat.card A)
    (apart : Disjoint A B)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (noCut : ∀ d ∈ D, ¬ G.Adj r d)
    (unique : ∃! a, a ∈ A ∧ G.Adj r a)
    (clique : A.Pairwise G.Adj) (notClique : ¬ B.Pairwise G.Adj)
    (connected : (G.induce B).Connected) :
    ∃ M : CubicMixedCut G, M.r = r := by
  classical
  have two : (D.erase r).card = 2 := by rw [Finset.card_erase_of_mem rD,cutSize]
  obtain ⟨p,q,pq,portEq⟩ := Finset.card_eq_two.mp two
  have cutEq : D = {r,p,q} := by rw [← Finset.insert_erase rD,portEq]
  have rp : r ≠ p := fun eq => (Finset.mem_erase.mp (portEq.symm ▸ (by simp : p ∈ ({p,q} : Finset V)))).1 eq.symm
  have rq : r ≠ q := fun eq => (Finset.mem_erase.mp (portEq.symm ▸ (by simp : q ∈ ({p,q} : Finset V)))).1 eq.symm
  obtain ⟨a,⟨aA,ra⟩,only⟩ := unique
  obtain ⟨x,xA,y,yA,xy⟩ := exists_two_of_natCard bigA
  have tail : ∃ t ∈ A, a ≠ t := by
    by_cases ea : a = x
    · exact ⟨y,yA,ea.trans_ne xy⟩
    · exact ⟨x,xA,ea⟩
  obtain ⟨t,tA,atEdge⟩ := tail
  let N := G.neighborFinset r
  have aN : a ∈ N := (G.mem_neighborFinset _ _).mpr ra
  have n2 : (N.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem aN,G.card_neighborFinset_eq_degree,degree]
  obtain ⟨b,c,bc,nEq⟩ := Finset.card_eq_two.mp n2
  have nAll : N = {a,b,c} := by rw [← Finset.insert_erase aN,nEq]
  have bN : b ∈ N.erase a := nEq.symm ▸ (by simp : b ∈ ({b,c} : Finset V))
  have cN : c ∈ N.erase a := nEq.symm ▸ (by simp : c ∈ ({b,c} : Finset V))
  have B_of_other (v : V) (vN : v ∈ N.erase a) : v ∈ B := by
    obtain ⟨va,vr⟩ := Finset.mem_erase.mp vN
    have edge := (G.mem_neighborFinset _ _).mp vr
    rcases cover v with av|bv|dv
    · exact (va (only _ ⟨av,edge⟩)).elim
    · exact bv
    · exact (noCut _ dv edge).elim
  have nb (v : V) : G.Adj r v ↔ v = a ∨ v = b ∨ v = c := by
    rw [← G.mem_neighborFinset]
    change v ∈ N ↔ _
    rw [nAll]
    simp only [Finset.mem_insert,Finset.mem_singleton]
  exact ⟨⟨r,p,q,rp,rq,pq,A,B,apart,cutEq ▸ offA,cutEq ▸ offB,
    cutEq ▸ boundA,cutEq ▸ boundB,cutEq ▸ cover,clique,connected,notClique,
    a,t,b,c,aA,tA,atEdge,B_of_other b bN,B_of_other c cN,bc,nb⟩,rfl⟩

/-- A component split witnessing failure of surviving-edge crossing in
the independent-cubic branch has no cubic vertex in its three-cut. -/
theorem LargeCrossingFailure.cut_has_no_cubics (F : LargeCrossingFailure G)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    {r : V} (hr : r ∈ F.cut) : G.degree r ≠ 3 := by
  intro degree
  have profile := F.cubic_port_profile conn budget no hr degree
  dsimp only at profile
  obtain ⟨cover,off,shape⟩ := profile
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have bdA := componentShore_boundary F.cut F.first
  have bdB := componentShore_boundary F.cut F.second
  have sep := componentShore_disjoint F.different
  rcases shape with ⟨unique,clique,nonclique⟩|⟨unique,clique,nonclique⟩
  · obtain ⟨M,_⟩ := build_mixed hr F.size degree F.first_large sep offA offB bdA bdB
      cover off unique clique nonclique (componentShore_connected F.cut F.second)
    exact no (M.traceable_of_independent_cubics conn budget ind)
  · have swapCover (v : V) :
        v ∈ componentShore F.cut F.second ∨ v ∈ componentShore F.cut F.first ∨ v ∈ F.cut := by
      rcases cover v with a|b|d
      · exact Or.inr (Or.inl a)
      · exact Or.inl b
      · exact Or.inr (Or.inr d)
    obtain ⟨M,_⟩ := build_mixed hr F.size degree F.second_large sep.symm offB offA bdB bdA
      swapCover off unique clique nonclique (componentShore_connected F.cut F.first)
    exact no (M.traceable_of_independent_cubics conn budget ind)

/-- Every surviving-edge crossing failure now supplies a three-cut
whose vertices all have degree at least four. -/
theorem high_cut_of_crossing_failure_of_independent_cubics
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) :
    ∃ F : LargeCrossingFailure G, ∀ v ∈ F.cut, 4 ≤ G.degree v := by
  obtain ⟨F⟩ := large_crossing_failure_of_independent_cubics smaller conn budget order no ind fail
  refine ⟨F,?_⟩
  intro v hv
  have low := degree_of_small_deletion_preconnected (G := G) (by omega : 4 ≤ Fintype.card V)
    (fun D h => (conn.2 D h).preconnected) v
  have ne := F.cut_has_no_cubics conn budget no ind hv
  omega

/-- Edge-to-edge reachability holds for each deletion of at most three
vertices containing a cubic vertex in this minimum-order branch. -/
theorem edge_reach_of_cut_with_cubic
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    {D : Finset V} (small : D.card ≤ 3) {r : V} (hr : r ∈ D) (rdeg : G.degree r = 3)
    {a b c d : Survives D} (ab : G.Adj a.val b.val) (cd : G.Adj c.val d.val) :
    (DeletionGraph G D).Reachable a c := by
  by_cases fewer : D.card < 3
  · exact (conn.2 D fewer).preconnected a c
  apply Classical.byContradiction
  intro noReach
  have size : D.card = 3 := by omega
  let H := DeletionGraph G D
  have dif : H.connectedComponentMk a ≠ H.connectedComponentMk c :=
    fun eq => noReach (ConnectedComponent.exact eq)
  let F : LargeCrossingFailure G :=
    ⟨D,size,H.connectedComponentMk a,H.connectedComponentMk c,dif,
      large_component_of_edge smaller conn budget order size no ind ab,
      large_component_of_edge smaller conn budget order size no ind cd⟩
  exact F.cut_has_no_cubics conn budget no ind hr rdeg

#print axioms edge_reach_of_cut_with_cubic
#print axioms CubicMixedCut.traceable_of_independent_cubics
#print axioms LargeCrossingFailure.cut_has_no_cubics
#print axioms high_cut_of_crossing_failure_of_independent_cubics

end Graffiti199Depleted.Catalogue
