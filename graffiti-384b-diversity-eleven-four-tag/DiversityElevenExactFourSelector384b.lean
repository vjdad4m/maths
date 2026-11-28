import DiversityElevenPendantCounterFour384b
import DiversityElevenNormalizeTags384b
import Q8Original384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open PendantCircuit PendantCircuit.K4
open private Q8Original.triangle_comap from Q8Original384b
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The normalized tagged finite selector, on a genuine simple graph. -/
theorem exact_four_on_ordered_graph (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (deg : ∀ i,3≤G.degree i) (small : ∀ i : Fin 8,i.val<4 → 2≤trianglesAt G i)
    (up : ∀ i j : Fin 8,i<j → j.val<4 → trianglesAt G i<trianglesAt G j)
    (ports : ∀ i j : Fin 8, i≤j → (4 : Nat) ≤ i.val →
      (if G.Adj 1 i then 1 else 0)+(if G.Adj 0 i then 2 else 0)≤
      (if G.Adj 1 j then 1 else 0)+(if G.Adj 0 j then 2 else 0)) :
    ∃ K : Finset (Fin 8), K.card=3 ∧ ∀ v∉K,
      (if v.val<4 then 2 else 1)≤nbr G v K := by
  let E := graphWires G
  have pb (i : Fin 8) : portRank E i =
      (if G.Adj 1 i then 1 else 0)+(if G.Adj 0 i then 2 else 0) := by
    dsimp only [E,portRank]
    have edgeBool (a b : Fin 8) : edge (graphWires G) a b = decide (G.Adj a b) := by
      apply Bool.eq_iff_iff.mpr
      exact (edge_graphWires G a b).trans decide_eq_true_iff.symm
    rw [edgeBool,edgeBool]
    simp
  have port (i j : Fin 8) (ord : i≤j) (s : (4 : Nat) ≤ i.val) : portRank E i≤portRank E j := by
    rw [pb,pb]
    exact ports i j ord s
  obtain ⟨a,b,c,ab,bc,h⟩ := have_triple_of_exact_counts E
    (by rw [degree0_graphWires]; exact deg 0)
    (by rw [degree1_graphWires]; exact deg 1)
    (by rw [degree2_graphWires]; exact deg 2)
    (by rw [degree3_graphWires]; exact deg 3)
    (by rw [degree4_graphWires]; exact deg 4)
    (by rw [degree5_graphWires]; exact deg 5)
    (by rw [degree6_graphWires]; exact deg 6)
    (by rw [degree7_graphWires]; exact deg 7)
    (by rw [score0_graphWires]; exact small 0 (by decide))
    (by rw [score0_graphWires,score1_graphWires]; exact up 0 1 (by decide) (by decide))
    (by rw [score1_graphWires,score2_graphWires]; exact up 1 2 (by decide) (by decide))
    (by rw [score2_graphWires,score3_graphWires]; exact up 2 3 (by decide) (by decide))
    (port 4 5 (by decide) (by decide))
    (port 5 6 (by decide) (by decide))
    (port 6 7 (by decide) (by decide))
  let K : Finset (Fin 8) := {a,b,c}
  have ac := lt_trans ab bc
  have aa : a∉({b,c}:Finset (Fin 8)) := by simp [ab.ne,ac.ne]
  refine ⟨K,by dsimp [K]; rw [card_insert_of_not_mem aa,card_pair bc.ne],?_⟩
  intro i ik
  have ia : i≠a := fun e => ik (e ▸ mem_insert_self ..)
  have ib : i≠b := fun e => ik (e ▸ mem_insert_of_mem (mem_insert_self ..))
  have ic : i≠c := fun e => ik (e ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  have data := h i ia ib ic
  let L := ([a,b,c]:List (Fin 8)).filter (edge E i)
  have ln : L.Nodup := (show ([a,b,c]:List (Fin 8)).Nodup by
    simp [ab.ne,ac.ne,bc.ne]).filter _
  have lf : L.toFinset=K.filter (G.Adj i) := by
    ext j
    simp only [L,K,List.mem_filter,List.mem_toFinset,List.mem_cons,List.not_mem_nil,
       or_false,mem_filter,mem_insert,mem_singleton,E,edge_graphWires]
  have le : countTrue [edge E i a,edge E i b,edge E i c]=nbr G i K := by
    calc
      _ = L.length := by
        exact K4.countTrue_map (edge E i) [a,b,c]
      _ = _ := by rw [←List.toFinset_card_of_nodup ln,lf]; rfl
  rwa [le] at data

private theorem degree_relabel (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (p : Fin 8 ≃ Fin 8) (i : Fin 8) :
    (G.comap p).degree i = G.degree (p i) := by
  have h : ((G.comap p).neighborFinset i).map p.toEmbedding = G.neighborFinset (p i) := by
    ext x
    obtain ⟨j,rfl⟩ := p.surjective x
    have m := Finset.mem_map' p.toEmbedding (a:=j) (s:=(G.comap p).neighborFinset i)
    change p j ∈ _ ↔ j ∈ _ at m
    rw [m,SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborFinset]
    rfl
  rw [←G.card_neighborFinset_eq_degree,←h,Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree]

/-- Strict closure of the finite selector for arbitrary tagged boards. -/
theorem exact_four_selector (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (Z : Finset (Fin 8)) (sz : Z.card=4) (deg : ∀ i,3≤G.degree i)
    (mn : ∀ i∈Z,2≤trianglesAt G i) (inj : Set.InjOn (trianglesAt G) (Z : Set (Fin 8))) :
    ∃ K : Finset (Fin 8), K.card=3 ∧ ∀ i∉K,
      (if i∈Z then 2 else 1)≤nbr G i K := by
  obtain ⟨e,tag,order,ports⟩ := order_tags_at G Z 4 sz (by decide) (by decide) inj
  let H := G.comap (e : Fin 8→Fin 8)
  let dc : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.comap (e : Fin 8→Fin 8)).Adj)
  letI := dc
  have hd (i : Fin 8) : 3≤H.degree i := (degree_relabel G e i).symm ▸ deg (e i)
  have tr (i : Fin 8) : trianglesAt H i=trianglesAt G (e i) := Q8Original.triangle_comap G e i
  have small (i : Fin 8) (iz : i.val<4) : 2≤trianglesAt H i :=
    (tr i).symm ▸ mn _ ((tag i).mpr iz)
  have up (i j : Fin 8) (ij : i<j) (jz : j.val<4) :
      trianglesAt H i<trianglesAt H j := by
    rw [tr,tr]
    exact order i j ij jz
  obtain ⟨K,k3,good⟩ := exact_four_on_ordered_graph H hd small up ports
  let M := K.map e.toEmbedding
  refine ⟨M,(card_map ..).trans k3,?_⟩
  intro v vm
  obtain ⟨i,rfl⟩ := e.surjective v
  have ik : i∉K := fun hi => vm (mem_map.mpr ⟨i,hi,rfl⟩)
  have cnt : nbr H i K=nbr G (e i) M := by
    unfold nbr
    have ee : (K.filter (H.Adj i)).map e.toEmbedding=M.filter (G.Adj (e i)) := by
      ext v
      obtain ⟨j,rfl⟩ := e.surjective v
      rw [show e j∈_ ↔ j∈K.filter (H.Adj i) from mem_map' ..,mem_filter,mem_filter]
      change j∈K ∧ G.Adj (e i) (e j) ↔ e.toEmbedding j∈K.map e.toEmbedding ∧ _
      rw [mem_map']
    rw [←ee,card_map]
  have res := good i ik
  rw [cnt] at res
  by_cases z : e i∈Z
  · rw [if_pos ((tag i).mp z)] at res
    simpa [z] using res
  · rw [if_neg (fun h => z ((tag i).mpr h))] at res
    simpa [z] using res

#print axioms exact_four_on_ordered_graph
#print axioms exact_four_selector
end Graffiti384b.DiversityEleven
