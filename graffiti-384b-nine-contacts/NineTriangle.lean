import NineRanks
namespace Graffiti384b.NinePins
open Finset SimpleGraph SparsePairs
open private SparsePairs.inner SparsePairs.inner_match from SparseGeometry
open private Squares29.pair_at from SquareTriple29
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With one isolated neighbor and a matching on the remaining neighbors,
a degree-four root cannot have three vertices in that matching row and two
triangles. This applies to arbitrary finite simple graphs. -/
theorem short_matching_row {w u : V} (R : Finset V) (wu : G.Adj w u) (off : u∉R)
    (row : R⊆G.neighborFinset w) (alone : ∀a∈R,¬G.Adj u a)
    (matching : ∀a∈R,nbr G a R≤1) (small : G.degree w≤4)
    (score : 2≤trianglesAt G w) : R.card≤2 := by
  classical
  by_contra! many
  have inc := insert_subset ((G.mem_neighborFinset ..).mpr wu) row
  have bound := card_le_card inc
  rw [card_insert_of_not_mem off,card_neighborFinset_eq_degree] at bound
  have exactN : G.neighborFinset w=insert u R := (eq_of_subset_of_card_le inc
    (by rw [card_neighborFinset_eq_degree,card_insert_of_not_mem off]; omega)).symm
  have sub : Repair.linkEdges G w⊆SparsePairs.inner G R := by
    intro p pm; obtain ⟨adj,sz,cl⟩ := Repair.edge_info G pm
    obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp sz
    have am : a∈({a,b}:Finset V) := mem_insert_self ..
    have bm : b∈({a,b}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have aa := adj am; have bb := adj bm
    rw [exactN,mem_insert] at aa bb
    have edge := cl _ am _ bm ab
    have use {x y : V} (xm : x=u ∨ x∈R) (ym : y=u ∨ y∈R) (xy : G.Adj x y) : x∈R := by
      rcases xm with rfl|h
      · exact False.elim (ym.elim (fun eq => xy.ne eq.symm) (fun h => alone _ h xy))
      · exact h
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset (use aa bb edge)
      (singleton_subset_iff.mpr (use bb aa edge.symm)),sz⟩,cl⟩
  have links := card_le_card sub
  change trianglesAt G w≤(SparsePairs.inner G R).card at links
  have matchSize := SparsePairs.inner_match G R matching
  omega

/-- At nine exterior contacts, the two triangles of the selected anchor
consist of its triangular ear and an edge joining its two private neighbors. -/
theorem nine_triangles (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (nine : (((high G)\(G.neighborFinset e∪G.neighborFinset f)).filter
      (fun i => 0<nbr G i (G.neighborFinset e∪G.neighborFinset f))).card=9) :
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
  obtain ⟨_,w,wa,privateRow,matchingRow,five,ten,_,noTriangle,_⟩ := sparse_frontier G t q bad ef de df
  let x := nbr G w X
  let H := X.filter (fun z => 0<nbr G z A)
  change H.card=9 at nine
  change x+5≤H.card at five
  change (x≤1 → x+10≤H.card) at ten
  have lower : 2≤x := by by_contra! hi; have h := ten (by omega); omega
  have sm : x≤3 := by
    by_contra! large
    have six := six_beyond_matching G t q bad ef de df wa privateRow matchingRow (by change 4≤x; omega) (by change x≤7; omega)
    change x+6≤H.card at six; omega
  obtain ⟨no,upper⟩ := noTriangle sm (by change H.card<x+10; omega)
  obtain ⟨_,ah,_,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  obtain ⟨hs,_⟩ := TwoEars.profile G t q bad
  obtain ⟨_,floor,_,_⟩ := Repair.maximal_diversity G (by rw [hs,t])
  have lo := floor w (ah wa)
  change trianglesAt G w≤1+x/2 at upper
  have sc : trianglesAt G w=2 := by omega
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
  have uh : u∉high G := by intro m; have h := (mem_filter.mp m).2; rw [two u um] at h; omega
  have off : u∉R w := fun h => uh (mem_sdiff.mp (mem_filter.mp h).1).1
  have alone (z : V) (zm : z∈R w) : ¬G.Adj u z :=
    fun uz => (mem_sdiff.mp (mem_filter.mp zm).1).2 (all u um ((G.mem_neighborFinset ..).mpr uz))
  have short := short_matching_row G (R w) wu off (fun z zm => (G.mem_neighborFinset ..).mpr (mem_filter.mp zm).2) alone matchingRow
    (SparsePairs.score_two_degree_le_four G t q bad ef de df wa sc) lo
  have ks : nbr G w X=2 := le_antisymm short lower
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
end Graffiti384b.NinePins
#print axioms Graffiti384b.NinePins.short_matching_row
#print axioms Graffiti384b.NinePins.nine_triangles
