import CenteredCapExportZ5
import PetersenTwoPortKit
import CentralTwoPort

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute CopyMimic FourRingCyclicEquivalence
open CentralLeafObstruction
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem mapped_difference (f : Fin 10 ↪ V) (U X : Finset (Fin 10)) :
    (U\X).map f = U.map f \ X.map f := by
  ext y
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := mem_map.mp h
    have ⟨a,b⟩ := mem_sdiff.mp hu
    refine mem_sdiff.mpr ⟨mem_map.mpr ⟨u,a,rfl⟩,?_⟩
    intro z
    obtain ⟨d,hd,ed⟩ := mem_map.mp z
    exact b (f.injective ed ▸ hd)
  · intro h
    obtain ⟨yes,no⟩ := mem_sdiff.mp h
    obtain ⟨u,hu,rfl⟩ := mem_map.mp yes
    exact mem_map.mpr ⟨u,mem_sdiff.mpr ⟨hu,fun b=>no (mem_map.mpr ⟨u,b,rfl⟩)⟩,rfl⟩

/-- The marked Petersen quotient (0,2,8) with shore residues (0,0,2)
can be assembled conditional on the cyclic-four ordinary conjecture,
without requiring vertex transitivity. No extra mode at either of the
zero shores is needed. -/
theorem cyclic4_petersen_junction
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V}
    {A B C : Finset V} {x : V} (f : Fin 10 ↪ V) (ports : Fin 10→V)
    (capA : CappedRegion G A x) (capB : CappedRegion G B x) (capC : CappedRegion G C x)
    (dvd : 6∣Fintype.card (↑(insert x A):Type u))
    (resB : Fintype.card (↑(insert x B):Type u)%6=4)
    (resC : Fintype.card (↑(insert x C):Type u)%6=4)
    (exactPorts : ∀ v,capA.rootAdj v → ∃ i,pet.Adj 8 i ∧ ports i=v)
    (links : ∀ i, pet.Adj 8 i → G.Adj (ports i) (f i))
    (keep : ∀ i∈core,∀ j∈core,pet.Adj i j→G.Adj (f i) (f j))
    (ar : Disjoint A (core.map f))
    (ab : Disjoint (A∪core.map f) B) (ac : Disjoint (A∪core.map f) C)
    (bc : Disjoint B C) (whole : A∪core.map f∪B∪C=univ) :
    KelmansStarter.HasP3Factor G := by
  obtain ⟨a,b,ne,ra,rb,ca⟩ := capA.centered_export_z5 promise dvd
  obtain ⟨i,ei,hi⟩ := exactPorts a ra
  obtain ⟨j,ej,hj⟩ := exactPorts b rb
  have ij : i≠j := fun h=>ne (hi.symm.trans ((congrArg ports h).trans hj))
  obtain ⟨ur,wr,ds,pa,pb,⟨M,MF⟩⟩ := pet_repairs_with_center_port ei ej ij
  have EU : ({i,mate i}:Finset (Fin 10)).map f = {f i,f (mate i)} := by simp
  have EW : ({j,mate j}:Finset (Fin 10)).map f = {f j,f (mate j)} := by simp
  have rangeU : ({f i,f (mate i)}:Finset V)⊆core.map f := by
    rw [←EU]
    exact map_subset_map.mpr ur
  have rangeW : ({f j,f (mate j)}:Finset V)⊆core.map f := by
    rw [←EW]
    exact map_subset_map.mpr wr
  have dsNew : Disjoint ({f i,f (mate i)}:Finset V) {f j,f (mate j)} := by
    rw [←EU,←EW]
    exact (disjoint_map f).mpr ds
  have rest := local_map f (fun u hu v hv e=>keep u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1 e) MF
  rw [mapped_difference,map_union,EU,EW] at rest
  have all : Closed G (A∪core.map f) := join_two_singletons_to_two_edges
    ra.choose rb.choose ne rangeU rangeW dsNew ar (hi ▸ links i ei) (keep _ (ur (by simp)) _ (ur (by simp)) pa)
    (hj ▸ links j ej) (keep _ (wr (by simp)) _ (wr (by simp)) pb) ca ⟨_,rest⟩
  have merged := add_closed (add_closed all (capB.zero promise resB) ab)
    (capC.zero promise resC) (disjoint_union_left.mpr ⟨ac,bc⟩)
  obtain ⟨P,hP⟩ := merged
  exact ⟨P,hP.tile,hP.disj,hP.cover.trans whole⟩
#print axioms cyclic4_petersen_junction
end
end KelmansCactus.AtomicBridge
