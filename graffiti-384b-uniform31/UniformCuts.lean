import ExteriorCut
import OppositeFan
namespace Graffiti384b.TenPins
open Finset SimpleGraph ForkGuard34
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With at most one adjacent ear, two triangles at v guarantee a triangle
whose two other vertices both have degree at least three. -/
theorem high_triangle (v : V) (lowCount : nbr G v (LowSample.twos G)≤1) (sc : 2≤trianglesAt G v) :
    ∃i∈high G,∃j∈high G,G.Adj v i ∧ G.Adj v j ∧ G.Adj i j := by
  classical
  apply Classical.byContradiction; intro none
  let code (w : V) := insert w ((G.neighborFinset w).erase v)
  have low {i j : V} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) (ih : i∉high G) :
      i∈LowSample.twos G ∧ code i={i,j} := by
    have sub : {v,j}⊆G.neighborFinset i := insert_subset ((G.mem_neighborFinset ..).mpr vi.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ij))
    have lower := card_le_card sub
    rw [card_pair vj.ne,card_neighborFinset_eq_degree] at lower
    have upper : G.degree i≤2 := Nat.le_of_not_gt (fun h => ih (mem_filter.mpr ⟨mem_univ _,h⟩))
    have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,card_pair vj.ne]; exact upper)
    exact ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,lower⟩,ih⟩,by simp [code,←eq,vj.ne,vj.ne.symm]⟩
  have cover : Repair.linkEdges G v⊆((LowSample.twos G).filter (G.Adj v)).image code := by
    intro p pm
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G pm
    obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
    have im : i∈({i,j}:Finset V) := mem_insert_self ..
    have jm : j∈({i,j}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have vi := (G.mem_neighborFinset ..).mp (sub im)
    have vj := (G.mem_neighborFinset ..).mp (sub jm)
    have edge_ := cl _ im _ jm ij
    by_cases ih : i∈high G
    · by_cases jh : j∈high G
      · exact False.elim (none ⟨i,ih,j,jh,vi,vj,edge_⟩)
      · obtain ⟨m,eq⟩ := low vj vi edge_.symm jh
        exact mem_image.mpr ⟨j,mem_filter.mpr ⟨m,vj⟩,eq.trans (pair_comm ..)⟩
    · obtain ⟨m,eq⟩ := low vi vj edge_ ih
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨m,vi⟩,eq⟩
  have count := (card_le_card cover).trans card_image_le
  change trianglesAt G v≤nbr G v (LowSample.twos G) at count; omega

/-- The catalogue inequality for exactly 31 triangle counts and 31 nonleaves,
at every order and for disconnected as well as connected graphs. -/
theorem thirty_one_nonleaves (t : (types G).card=31) (q : (nonleaves G).card=31) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨hs,count⟩ := TwoEars.profile G t q bad
  obtain ⟨e,f,ef,pair⟩ := card_eq_two.mp count
  have two (z : V) (m : z∈LowSample.twos G) : G.degree z=2 := by
    obtain ⟨vm,off⟩ := mem_sdiff.mp m
    have lo := (mem_filter.mp vm).2
    have hi : G.degree z≤2 := Nat.le_of_not_gt (fun h => off (mem_filter.mpr ⟨mem_univ _,h⟩))
    omega
  have de := two e (pair ▸ mem_insert_self ..)
  have df := two f (pair ▸ mem_insert_of_mem (mem_singleton_self _))
  let A := G.neighborFinset e∪G.neighborFinset f
  have data : AnchorData G A := anchor_data G t q bad ef de df
  obtain ⟨w,wa,blind,matching⟩ := ForkGuard34.matching G data.highPins data.ears data.owns (by omega) bad
  have priv (z : V) (zm : z∈row G A w) : nbr G z A=1 := by
    obtain ⟨zx,wz⟩ := mem_filter.mp zm
    have nonzero : 0<nbr G z A := card_pos.mpr ⟨w,mem_filter.mpr ⟨wa,wz.symm⟩⟩
    by_contra h
    exact blind z (mem_filter.mpr ⟨zx,by omega⟩) wz
  have gap := secondary_gap G t q bad ef de df wa (fun z zm wz => priv z (mem_filter.mpr ⟨zm,wz⟩)) matching
  obtain ⟨_,floor,_,_⟩ := Repair.maximal_diversity G (by rw [t,hs])
  obtain ⟨i,ih,j,jh,wi,wj,ij⟩ := high_triangle G w (data.singleEar w wa) (floor w (data.highPins wa))
  have same {a z : V} (ag : a∈high G) (wz : G.Adj w z) (aw : G.Adj w a) (az : G.Adj a z) (za : z∈A) : a∈A := by
    by_contra off
    have one := priv a (mem_filter.mpr ⟨mem_sdiff.mpr ⟨ag,off⟩,aw⟩)
    have both := PinnedColor34.two G wz.ne aw.symm az wa za; omega
  by_cases ia : i∈A
  · have ja := same jh wi wj ij.symm ia
    let K : Finset V := {w,i,j}
    have sub : K⊆A := insert_subset wa (insert_subset ia (singleton_subset_iff.mpr ja))
    have ks : K.card=3 := by simp [K,wi.ne,wj.ne,ij.ne]
    have rest : (A\K).card=1 := by rw [card_sdiff sub,data.four,ks]
    obtain ⟨b,bm⟩ := card_pos.mp (show 0<(A\K).card by omega)
    obtain ⟨ba,bk⟩ := mem_sdiff.mp bm
    have ex : A.erase b=K := (eq_of_subset_of_card_le (show K⊆A.erase b from
      fun y ym => mem_erase.mpr ⟨fun eq => bk (eq ▸ ym),sub ym⟩) (by rw [card_erase_of_mem ba,data.four,ks])).symm
    have cl : ∀x∈A.erase b,∀y∈A.erase b,x≠y → G.Adj x y := by
      rw [ex]; intro x xm y ym xy
      simp only [K,mem_insert,mem_singleton] at xm ym
      rcases xm with rfl|rfl|rfl <;> rcases ym with rfl|rfl|rfl <;>
        first | exact False.elim (xy rfl) | assumption | exact wi.symm | exact wj.symm | exact ij.symm
    have score := gap b ba (fun eq => bk (eq ▸ mem_insert_self ..))
    have dis := AnchorPairs.disjoint_anchors G t q bad ef de df
    rcases mem_union.mp ba with be|bf
    · exact missing_pin G ef de df bad A rfl data dis be score cl
    · exact missing_pin G ef.symm df de bad A (union_comm ..) data dis.symm bf score cl
  · have ja : j∉A := fun h => ia (same ih wj wi ij h)
    have ir : i∈row G A w := mem_filter.mpr ⟨mem_sdiff.mpr ⟨ih,ia⟩,wi⟩
    have jr : j∈row G A w := mem_filter.mpr ⟨mem_sdiff.mpr ⟨jh,ja⟩,wj⟩
    exact exterior_cut G t q bad ef de df wa priv matching gap i ir j jr ij

/-- At diversity 31 the recorded natural-number bound is n minus sixteen. -/
theorem omit_sixteen (t : (types G).card=31) (q : (nonleaves G).card=31) :
    gamma G≤Fintype.card V-16 := by
  simpa only [bound,t] using thirty_one_nonleaves G t q

end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.high_triangle
#print axioms Graffiti384b.TenPins.thirty_one_nonleaves
#print axioms Graffiti384b.TenPins.omit_sixteen
