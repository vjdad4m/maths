import DiversityElevenPendantGeometry384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Repair.edge_info Repair.linkEdges from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The high anchor has a triangle other than the pendant triangle, so
at least two vertices of the eight-high board see it and are adjacent. -/
theorem pendant_anchor_triangle (sup : Supported G)
    {e f a : V} (ah : a∈high G) (am : 2≤trianglesAt G a)
    (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a}) :
    ∃ x∈(high G).erase a, ∃ y∈(high G).erase a,
      G.Adj a x ∧ G.Adj a y ∧ G.Adj x y := by
  classical
  let L := Repair.linkEdges G a
  have count : 1<L.card := am
  obtain ⟨s,sm,ne⟩ := exists_ne_of_one_lt_card count ({e,f}:Finset V)
  obtain ⟨sn,sz,cl⟩ := Repair.edge_info G sm
  obtain ⟨x,y,xy,sxy⟩ := card_eq_two.mp sz
  have xs : x∈s := sxy ▸ mem_insert_self _ _
  have ys : y∈s := sxy ▸ mem_insert_of_mem (mem_singleton_self _)
  have ax : G.Adj a x := (G.mem_neighborFinset ..).mp (sn xs)
  have ay : G.Adj a y := (G.mem_neighborFinset ..).mp (sn ys)
  have edge : G.Adj x y := cl x xs y ys xy
  have within {v w : V} (av : G.Adj a v) (aw : G.Adj a w) (vw : G.Adj v w)
      (vwset : s={v,w}) : v∈(high G).erase a := by
    refine mem_erase.mpr ⟨av.ne.symm,?_⟩
    obtain ⟨z,vz,wz⟩ := sup av
    have sub : ({a,z}:Finset V)⊆ G.neighborFinset v := by
      intro u um
      simp only [mem_insert,mem_singleton] at um
      rcases um with rfl|rfl
      · exact (G.mem_neighborFinset ..).mpr av.symm
      · exact (G.mem_neighborFinset ..).mpr wz
    have card := card_le_card sub
    rw [card_pair vz.ne,card_neighborFinset_eq_degree] at card
    by_cases vh : v∈high G
    · exact vh
    exfalso
    have vl : v∈nonleaves G \ high G := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,card⟩,vh⟩
    rw [low,mem_insert,mem_singleton] at vl
    rcases vl with rfl|rfl
    · have h := (G.mem_neighborFinset ..).mpr vw
      rw [en,mem_insert,mem_singleton] at h
      rcases h with rfl|rfl
      · exact ne vwset
      · exact aw.ne rfl
    · have h := (G.mem_neighborFinset ..).mpr vw
      rw [fn,mem_insert,mem_singleton] at h
      rcases h with rfl|rfl
      · exact ne (vwset.trans (pair_comm ..))
      · exact aw.ne rfl
  exact ⟨x,within ax ay edge sxy,y,within ay ax edge.symm (sxy.trans (pair_comm ..)),ax,ay,edge⟩

theorem pendant_zero_tags_le_six (sup : Supported G)
    (nine : (high G).card=9) {e f a : V} (ah : a∈high G) (am : 2≤trianglesAt G a)
    (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a}) :
    (((high G).erase a).filter (fun v => ¬G.Adj v a)).card≤6 := by
  obtain ⟨x,xh,y,yh,ax,ay,xy⟩ := pendant_anchor_triangle G sup ah am low en fn
  let B := (high G).erase a
  let Z := B.filter (fun v => ¬G.Adj v a)
  have two : 2≤(B.filter (G.Adj · a)).card := by
    have sub : ({x,y}:Finset V)⊆B.filter (G.Adj · a) := by
      intro v vm
      simp only [mem_insert,mem_singleton] at vm
      rcases vm with rfl|rfl
      · exact mem_filter.mpr ⟨xh,ax.symm⟩
      · exact mem_filter.mpr ⟨yh,ay.symm⟩
    have h := card_le_card sub
    rwa [card_pair xy.ne] at h
  have sz : B.card=8 := by dsimp [B]; rw [card_erase_of_mem ah,nine]
  have c := filter_card_add_filter_neg_card_eq_card (s:=B) (G.Adj · a)
  change _+Z.card=B.card at c
  change Z.card≤6
  omega

#print axioms pendant_anchor_triangle
#print axioms pendant_zero_tags_le_six
end Graffiti384b.DiversityEleven
