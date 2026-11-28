import DisjointEarFork
import PaletteException
namespace Graffiti384b.TriangleFrame
open Finset SimpleGraph LowSample Four29 FiveChoice
open private LowSample.two_degree from LowSample384b
open private Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem pair_anchors {e f : V} (ears : twos G={e,f}) : anchors G=roots G e f := by
  simp [anchors,ears,roots]

/-- If a cross-fork is present, orient the two pairs oppositely and close the only remaining gap. -/
private theorem cross {e f : V} (ears : twos G={e,f}) (ef : e≠f)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (indep : Disjoint (twos G) (anchors G)) (rich : ∀a∈anchors G,2≤trianglesAt G a)
    (quota : (types G).card≤(nonleaves G).card) (bad : bound G<gamma G)
    {a : V} (am : a∈G.neighborFinset e) : nbr G a (G.neighborFinset f)≤1 := by
  classical
  have rootEq := pair_anchors G ears
  have de := LowSample.two_degree G (ears ▸ mem_insert_self e {f})
  have df := LowSample.two_degree G (ears ▸ mem_insert_of_mem (mem_singleton_self f))
  obtain ⟨a',b',ab',en⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G e).trans de)
  obtain ⟨b,ne,first⟩ : ∃b,b≠a ∧ G.neighborFinset e={b,a} := by
    rw [en,mem_insert,mem_singleton] at am
    rcases am with rfl|rfl
    · exact ⟨_,ab'.symm,en.trans (pair_comm ..)⟩
    · exact ⟨_,ab',en⟩
  obtain ⟨c,d,cd,second⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G f).trans df)
  let l : Fin 6→V := ![b,a,c,d,e,f]
  let W := roots G e f
  let E : Finset V := {e,f}
  have we : Disjoint W E := by simpa only [W,E,rootEq,ears] using indep.symm
  have rootSize : W.card=4 := by
    change (G.neighborFinset e∪G.neighborFinset f).card=4
    rw [card_union_of_disjoint sep,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de,df]
  have size : (W∪E).card=6 := by rw [card_union_of_disjoint we,rootSize,show E.card=2 from card_pair ef]
  have inside : W∪E ⊆ univ.image l := by
    intro v vm
    change v∈(G.neighborFinset e∪G.neighborFinset f)∪{e,f} at vm
    rw [first,second] at vm
    simp only [mem_union,mem_insert,mem_singleton] at vm
    rcases vm with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl)
    all_goals first | exact mem_image.mpr ⟨0,mem_univ _,rfl⟩ | exact mem_image.mpr ⟨1,mem_univ _,rfl⟩ |
      exact mem_image.mpr ⟨2,mem_univ _,rfl⟩ | exact mem_image.mpr ⟨3,mem_univ _,rfl⟩ |
      exact mem_image.mpr ⟨4,mem_univ _,rfl⟩ | exact mem_image.mpr ⟨5,mem_univ _,rfl⟩
  have inj := (card_image_iff (s:=univ) (f:=l)).mp (Nat.le_antisymm card_image_le (by
    have cmp := card_le_card inside; rw [size] at cmp; simpa using cmp))
  let emb : Fin 6 ↪ V := ⟨l,fun _ _ eq => inj (mem_univ _) (mem_univ _) eq⟩
  apply Nat.le_of_not_gt
  intro no
  have all : (G.neighborFinset f).filter (G.Adj a)=G.neighborFinset f :=
    eq_of_subset_of_card_le (filter_subset ..) (by rw [card_neighborFinset_eq_degree,df]; exact no)
  have ad {z : V} (zm : z∈G.neighborFinset f) : G.Adj a z := (mem_filter.mp (all.symm ▸ zm)).2
  have rb : b∈anchors G := rootEq ▸ mem_union_left _ (first ▸ mem_insert_self ..)
  exact (not_lt_of_ge (fork_bound G quota emb ears first second (ad (second ▸ mem_insert_self ..))
    (ad (second ▸ mem_insert_of_mem (mem_singleton_self _))) (no_thin_of_failure G bad) (rich b rb))) bad

/-- Two independent ears with disjoint neighborhoods suffice at every diversity if each of
their four anchors has at least two triangles. No hypothesis is imposed on the other scores. -/
theorem two_disjoint_ears {e f : V} (ears : twos G={e,f}) (ef : e≠f)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (indep : Disjoint (twos G) (anchors G)) (rich : ∀a∈anchors G,2≤trianglesAt G a)
    (quota : (types G).card≤(nonleaves G).card) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  obtain ⟨a,aw,_,_,cap⟩ := failed_graph_has_trapped_anchor G quota indep bad
  have pos : (internalTriangles G a).Nonempty := card_pos.mp (by have low := rich a aw; omega)
  obtain ⟨p,pm⟩ := pos
  obtain ⟨hit,inside⟩ := mem_filter.mp pm
  obtain ⟨sub,size,cl⟩ := Repair.edge_info G hit
  obtain ⟨x,y,ne,pair⟩ := card_eq_two.mp size
  have xp : x∈p := pair ▸ mem_insert_self ..
  have yp : y∈p := pair ▸ mem_insert_of_mem (mem_singleton_self _)
  have ax := (G.mem_neighborFinset ..).mp (sub xp)
  have ay := (G.mem_neighborFinset ..).mp (sub yp)
  have xy := cl x xp y yp ne
  have xw := inside xp; have yw := inside yp
  rw [pair_anchors G ears] at aw xw yw
  have de := LowSample.two_degree G (ears ▸ mem_insert_self e {f})
  have df := LowSample.two_degree G (ears ▸ mem_insert_of_mem (mem_singleton_self f))
  have ab := fun {v} (m : v∈G.neighborFinset e) => cross G ears ef sep indep rich quota bad m
  have ba := fun {v} (m : v∈G.neighborFinset f) => cross G (ears.trans (pair_comm ..)) ef.symm sep.symm indep rich quota bad m
  have own (s : Finset V) (k : s.card=2) (v : V) (m : v∈s) : nbr G v s≤1 := by
    have sub : s.filter (G.Adj v)⊆s.erase v := fun x xm => mem_erase.mpr ⟨(mem_filter.mp xm).2.ne.symm,(mem_filter.mp xm).1⟩
    have cmp := card_le_card sub
    rwa [card_erase_of_mem m,k] at cmp
  have contradict {S : Finset V} {v i j : V} (cap : nbr G v S≤1) (im : i∈S) (jm : j∈S)
      (vi : G.Adj v i) (vj : G.Adj v j) (ne : i≠j) : False :=
    (by have := PinnedColor34.two G ne vi vj im jm; omega)
  have ee := own _ ((card_neighborFinset_eq_degree G e).trans de)
  have ff := own _ ((card_neighborFinset_eq_degree G f).trans df)
  rcases mem_union.mp aw with a1|a2 <;> rcases mem_union.mp xw with x1|x2 <;> rcases mem_union.mp yw with y1|y2
  all_goals first | exact contradict (ee _ a1) x1 y1 ax ay xy.ne | exact contradict (ff _ a2) x2 y2 ax ay xy.ne |
    exact contradict (ab a1) x2 y2 ax ay xy.ne | exact contradict (ba a2) x1 y1 ax ay xy.ne |
    exact contradict (ab x1) a2 y2 ax.symm xy ay.ne | exact contradict (ba x2) a1 y1 ax.symm xy ay.ne |
    exact contradict (ab y1) a2 x2 ay.symm xy.symm ax.ne | exact contradict (ba y2) a1 x1 ay.symm xy.symm ax.ne

/-- The disjoint four-high-anchor, two-ear profile is closed at every diversity t=q. -/
theorem two_ears_equal_quota {e f : V} (ears : twos G={e,f}) (ef : e≠f)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (hi : anchors G⊆high G) (quota : (types G).card=(nonleaves G).card) : gamma G≤bound G := by
  have sub : high G⊆nonleaves G := by
    intro z zm; exact mem_filter.mpr ⟨mem_univ _, by have d := (mem_filter.mp zm).2; omega⟩
  have count := card_sdiff_add_card_eq_card sub
  change (twos G).card+(high G).card=(nonleaves G).card at count
  rw [ears,card_pair ef] at count
  have maximal : (types G).card=(high G).card+2 := by omega
  exact two_disjoint_ears G ears ef sep (disjoint_left.mpr (fun z zt za => (mem_sdiff.mp zt).2 (hi za)))
    (fun a aw => (Repair.maximal_diversity G maximal).2.1 a (hi aw)) quota.le

end Graffiti384b.TriangleFrame
#print axioms Graffiti384b.TriangleFrame.two_disjoint_ears
#print axioms Graffiti384b.TriangleFrame.two_ears_equal_quota
