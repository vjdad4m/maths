import Coupled35_384b

namespace Graffiti384b.Diversity35
open Finset SimpleGraph
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deleting every edge outside triangles leaves all triangle incidences
unchanged. Disconnectedness of the retained graph is allowed. -/
theorem exact_distinct (n : Fintype.card V=35) (t : (types G).card=35) {l : V} (zero : trianglesAt G l=0) :
    gamma G≤bound G := by
  classical
  by_contra! fail
  let J := TrianglePrune.skeleton G l ∅
  have eq (z : V) : trianglesAt J z=trianglesAt G z := TrianglePrune.scores G l ∅ z
  have typesEq : types J=types G := image_congr (fun z _ => eq z)
  have tj : (types J).card=35 := typesEq ▸ t
  have mono : gamma G≤gamma J := by
    have available : {k : ℕ | ∃ d, TwoDominates J d ∧ d.card=k}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
    obtain ⟨D,ok,sz⟩ := Nat.sInf_mem available
    have good : TwoDominates G D := fun v hv => (ok v hv).trans (card_le_card
      (show D.filter (J.Adj v) ⊆ D.filter (G.Adj v) from fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩))
    exact Nat.sInf_le (s:={k | ∃ d,TwoDominates G d ∧ d.card=k}) ⟨D,good,sz⟩
  have jf : bound J<gamma J := by
    have same : bound J=bound G := by simp only [bound,typesEq]
    rw [same]; exact fail.trans_le mono
  have inj : Function.Injective (trianglesAt J) := by
    have sz : (univ.image (trianglesAt J)).card=(univ : Finset V).card := by change (types J).card=_; rw [card_univ,tj,n]
    exact fun a b e => card_image_iff.mp sz (mem_univ a) (mem_univ b) e
  have triangle {a b : V} (edge : J.Adj a b) : ∃ c,J.Adj a c ∧ J.Adj b c := by
    change G.Adj a b ∧ ((∃ w,G.Adj a w ∧ G.Adj b w) ∨ _ ∨ _) at edge
    obtain ⟨ab,h⟩ := edge
    obtain ⟨c,ac,bc⟩ : ∃ c,G.Adj a c ∧ G.Adj b c := by simpa using h
    exact ⟨c,⟨ac,Or.inl ⟨b,ab,bc.symm⟩⟩,⟨bc,Or.inl ⟨a,ab.symm,ac.symm⟩⟩⟩
  have positive {a b : V} (ab : J.Adj a b) : 0<trianglesAt J a := by
    obtain ⟨c,ac,bc⟩ := triangle ab
    exact (TrianglePrune.triangle_iff J a).mpr ⟨b,c,ab,ac,bc⟩
  have lzero := (eq l).trans zero
  have noLeaf (w : V) : ¬J.Adj l w := fun e => by have := positive e; omega
  have dl : J.degree l=0 := by
    rw [←card_neighborFinset_eq_degree,card_eq_zero]
    exact eq_empty_iff_forall_not_mem.mpr (fun w m => noLeaf w ((J.mem_neighborFinset _ _).mp m))
  have normal : TrianglePrune.Normal J := ⟨fun _ _ z w => inj (z.trans w.symm),
    fun z sc _ _ edge _ => False.elim (by have := positive edge; omega),fun _ _ edge _ _ => triangle edge⟩
  have highTwo (z : V) (nz : z≠l) : 2≤J.degree z := by
    have pos := Nat.pos_of_ne_zero (fun sc => nz (inj (sc.trans lzero.symm)))
    obtain ⟨a,b,za,zb,ab⟩ := (TrianglePrune.triangle_iff J z).mp pos
    have sub : ({a,b} : Finset V) ⊆ J.neighborFinset z := insert_subset ((J.mem_neighborFinset _ _).mpr za)
      (singleton_subset_iff.mpr ((J.mem_neighborFinset _ _).mpr zb))
    simpa only [card_pair ab.ne,card_neighborFinset_eq_degree] using card_le_card sub
  have nonleaf : nonleaves J=({l} : Finset V)ᶜ := by
    ext z
    simp only [nonleaves,mem_filter,mem_univ,true_and,mem_compl,mem_singleton]
    exact ⟨fun d e => by subst z; omega,highTwo z⟩
  have q : (nonleaves J).card=34 := by rw [nonleaf,card_compl,card_singleton,n]
  have small : 2≤SmallScores35.top (high J).card := by unfold SmallScores35.top; split_ifs <;> decide
  obtain ⟨y,_,score1⟩ := SmallScores35.realized J tj q.ge jf 1 (by omega)
  obtain ⟨x,_,score2⟩ := SmallScores35.realized J tj q.ge jf 2 small
  have yl : y≠l := fun e => by subst y; omega
  have dy : J.degree y=2 := by
    have bd := (Minimal.degree_score J normal y (by omega)).1
    have empty : (J.neighborFinset y).filter (fun w => trianglesAt J w=0)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro w wm sc
      have := positive ((J.mem_neighborFinset _ _).mp wm).symm
      omega
    rw [empty,card_empty] at bd
    have := highTwo y yl
    omega
  have subH : high J⊆({l,y} : Finset V)ᶜ := by
    intro z zh
    have d := (mem_filter.mp zh).2
    apply mem_compl.mpr
    intro zm
    rcases mem_insert.mp zm with e|e
    · subst z; omega
    · obtain rfl := mem_singleton.mp e; omega
  have hc : (high J).card=33 := by
    have up := card_le_card subH
    rw [card_compl,card_pair yl.symm,n] at up
    have low := type_bound J
    omega
  have highEq := eq_of_subset_of_card_le subH (by rw [card_compl,card_pair yl.symm,n,hc])
  obtain ⟨u,v,yu,yv,uv⟩ := (TrianglePrune.triangle_iff J y).mp (by omega)
  have highN {z : V} (yz : J.Adj y z) : z∈high J := by
    rw [highEq,mem_compl,mem_insert,mem_singleton]
    exact fun h => h.elim (fun e => noLeaf y (e ▸ yz.symm)) yz.ne.symm
  have ny : J.neighborFinset y={u,v} := (eq_of_subset_of_card_le (insert_subset ((J.mem_neighborFinset _ _).mpr yu)
    (singleton_subset_iff.mpr ((J.mem_neighborFinset _ _).mpr yv))) (by rw [card_pair uv.ne,card_neighborFinset_eq_degree,dy])).symm
  obtain ⟨e,f,_,pairs,ec,fc,links,deg⟩ := TwoLinks35.shape J normal lzero score2
  have no : ¬J.Adj x l := fun adj => noLeaf x adj.symm
  rw [erase_eq_of_not_mem (fun m => no ((J.mem_neighborFinset _ _).mp m))] at links
  rw [if_neg no,Nat.add_zero] at deg
  exact Coupled35.core J n tj q hc inj jf dl score1 ny uv (highN yu) (highN yv) score2 pairs ec fc links deg

theorem exact_of_at_least_35_types (hc : G.Connected) (hn : 2<Fintype.card V) (big : 35≤(types G).card) :
    gamma G≤bound G := by
  by_contra! bad
  obtain ⟨r,_,_,same,fail,small|large⟩ := Least35.induced_alternative G hc hn bad
  · have size : (types (G.induce (r : Set V))).card≤r.card := by
      simpa only [types,card_univ,Fintype.card_coe] using
        (card_image_le (s:=(univ : Finset r)) (f:=trianglesAt (G.induce (r : Set V))))
    rw [same] at size; omega
  · obtain ⟨sz,t,_,_,types3⟩ := large
    have zero : 0∈types (G.induce (r : Set V)) := same ▸ types3 (by decide : 0∈range 3)
    obtain ⟨l,_,lz⟩ := mem_image.mp zero
    exact (not_lt_of_ge (exact_distinct (G.induce (r : Set V)) ((Fintype.card_coe r).trans sz) (same ▸ t) lz)) fail

theorem exact_of_at_least_34_types (hc : G.Connected) (hn : 2<Fintype.card V) (big : 34≤(types G).card) :
    gamma G≤bound G := by
  by_cases top : 35≤(types G).card
  · exact exact_of_at_least_35_types G hc hn top
  · exact Below35.exact34 G hc hn (by omega)

theorem induced_bound (hc : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G) :
    ∃ r : Finset V, 2<r.card ∧ r.card≤34 ∧ (G.induce (r : Set V)).Connected ∧
      types (G.induce (r : Set V))=types G ∧ bound (G.induce (r : Set V))<gamma (G.induce (r : Set V)) := by
  apply Below35.bounded_failure G _ hc hn bad
  exact Nat.lt_of_not_ge (fun big => (not_lt_of_ge (exact_of_at_least_35_types G hc hn big)) bad)

end Graffiti384b.Diversity35
#print axioms Graffiti384b.Diversity35.exact_distinct
#print axioms Graffiti384b.Diversity35.exact_of_at_least_35_types
#print axioms Graffiti384b.Diversity35.induced_bound

#print axioms Graffiti384b.Diversity35.exact_of_at_least_34_types
