import SparseFrontier
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph
open private Squares29.pair_at from SquareTriple29
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At eight exterior contacts, the two triangles of the selected anchor
consist of its triangular ear and an edge joining its two private neighbors. -/
theorem eight_triangles (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (eight : (((high G)\(G.neighborFinset e∪G.neighborFinset f)).filter
      (fun i => 0<nbr G i (G.neighborFinset e∪G.neighborFinset f))).card=8) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    ∃ w∈A,∃ u∈({e,f}:Finset V),∃ b∈A,∃ i∈X,∃ j∈X,
      i≠j ∧ G.neighborFinset u={w,b} ∧ G.Adj w b ∧ X.filter (G.Adj w)={i,j} ∧
      G.Adj i j ∧ trianglesAt G w=2 ∧ nbr G i A=1 ∧ nbr G j A=1 := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let R := fun w => X.filter (G.Adj w)
  let E : Finset V := {e,f}
  obtain ⟨_,w,wa,privateRow,_,_,_,_,noTriangle,atEight⟩ := sparse_frontier G t q bad ef de df
  obtain ⟨ks,sc⟩ := atEight eight
  change nbr G w X=2 at ks
  have no := (noTriangle (by change nbr G w X≤3; omega) (by rw [eight]; change 8<nbr G w X+10; omega)).1
  change ¬∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j at no
  have one : ∃ u∈E,G.Adj w u := (mem_union.mp wa).elim
    (fun m => ⟨e,mem_insert_self ..,((G.mem_neighborFinset ..).mp m).symm⟩)
    (fun m => ⟨f,mem_insert_of_mem (mem_singleton_self _),((G.mem_neighborFinset ..).mp m).symm⟩)
  obtain ⟨u,um,wu⟩ := one
  have two (a : V) (am : a∈E) : G.degree a=2 := (mem_insert.mp am).elim (fun h => h ▸ de) (fun h => mem_singleton.mp h ▸ df)
  have all (a : V) (am : a∈E) : G.neighborFinset a⊆A :=
    (mem_insert.mp am).elim (fun h => h ▸ subset_union_left) (fun h => mem_singleton.mp h ▸ subset_union_right)
  obtain ⟨b,wb,pair⟩ := Squares29.pair_at ((card_neighborFinset_eq_degree ..).trans (two u um)) ((G.mem_neighborFinset ..).mpr wu.symm)
  have ba := all u um (show b∈G.neighborFinset u from pair ▸ mem_insert_of_mem (mem_singleton_self _))
  have rcard : (R w).card=2 := ks
  obtain ⟨i,j,ij,row⟩ := card_eq_two.mp rcard
  have ir : i∈R w := row ▸ mem_insert_self ..
  have jr : j∈R w := row ▸ mem_insert_of_mem (mem_singleton_self _)
  have ix := (mem_filter.mp ir).1
  have jx := (mem_filter.mp jr).1
  have low {a z : V} (wa' : G.Adj w a) (wz : G.Adj w z) (az : G.Adj a z) (off : a∉high G) : a=u ∧ z=b := by
    have inc : {w,z}⊆G.neighborFinset a := insert_subset ((G.mem_neighborFinset ..).mpr wa'.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr az))
    have ct := card_le_card inc
    rw [card_pair wz.ne,card_neighborFinset_eq_degree] at ct
    have da : G.degree a=2 := le_antisymm (Nat.le_of_not_gt (fun h => off (mem_filter.mpr ⟨mem_univ _,h⟩))) ct
    have au : a=u := by
      apply Classical.byContradiction; intro ne
      have dj := AnchorPairs.disjoint_anchors G t q bad ne da (two u um)
      exact disjoint_left.mp dj ((G.mem_neighborFinset ..).mpr wa'.symm) ((G.mem_neighborFinset ..).mpr wu.symm)
    refine ⟨au,?_⟩
    have zm := (G.mem_neighborFinset ..).mpr az
    rw [au,pair,mem_insert,mem_singleton] at zm; exact zm.resolve_left wz.ne.symm
  have outer {a z : V} (aw : G.Adj w a) (zw : G.Adj w z) (az : G.Adj a z) (ha : a∈high G) (hz : z∈high G) : a∈R w := by
    apply mem_filter.mpr; refine ⟨mem_sdiff.mpr ⟨ha,?_⟩,aw⟩
    intro aa
    by_cases za : z∈A
    · exact no ⟨a,aa,z,za,aw,zw,az⟩
    · have sp := privateRow z (mem_sdiff.mpr ⟨hz,za⟩) zw
      have ct := PinnedColor34.two G aw.ne zw.symm az.symm wa aa
      change nbr G z A=1 at sp; change 2≤nbr G z A at ct; omega
  let L := Repair.linkEdges G w
  have cover : L⊆{{i,j},{u,b}} := by
    intro h hm; obtain ⟨sub,sz,cl⟩ := Repair.edge_info G hm
    obtain ⟨a,z,az,rfl⟩ := card_eq_two.mp sz
    have am : a∈({a,z}:Finset V) := mem_insert_self ..
    have zm : z∈({a,z}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have aw := (G.mem_neighborFinset ..).mp (sub am); have zw := (G.mem_neighborFinset ..).mp (sub zm)
    have edge := cl _ am _ zm az
    by_cases ha : a∈high G
    · by_cases hz : z∈high G
      · have inc := insert_subset (outer aw zw edge ha hz) (singleton_subset_iff.mpr (outer zw aw edge.symm hz ha))
        exact mem_insert.mpr (Or.inl ((eq_of_subset_of_card_le inc (rcard.trans sz.symm).le).trans row))
      · obtain ⟨eq1,eq2⟩ := low zw aw edge.symm hz
        rw [eq1,eq2,pair_comm b u]; exact mem_insert_of_mem (mem_singleton_self _)
    · obtain ⟨eq1,eq2⟩ := low aw zw edge ha
      rw [eq1,eq2]; exact mem_insert_of_mem (mem_singleton_self _)
  have eq : L={{i,j},{u,b}} := eq_of_subset_of_card_le cover ((card_insert_le ..).trans
    (by rw [card_singleton]; exact sc.ge))
  have insideI : ({i,j}:Finset V)∈L := eq ▸ mem_insert_self ..
  have insideU : ({u,b}:Finset V)∈L := eq ▸ mem_insert_of_mem (mem_singleton_self _)
  have wij := (Repair.edge_info G insideI).2.2 _ (mem_insert_self ..) _ (mem_insert_of_mem (mem_singleton_self _)) ij
  have wb' := (G.mem_neighborFinset ..).mp ((Repair.edge_info G insideU).1 (mem_insert_of_mem (mem_singleton_self _)))
  exact ⟨w,wa,u,um,b,ba,i,ix,j,jx,ij,pair,wb',row,wij,sc,privateRow i ix (mem_filter.mp ir).2,privateRow j jx (mem_filter.mp jr).2⟩
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.eight_triangles
