import RankRepair29
namespace Graffiti384b.Adjacent15
open Finset SimpleGraph
open private Repair.nbr_mono Repair.full_nbr Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two parts may each be omitted, independently. -/
def Split (S : Finset V) : Prop := ∃ L R : Finset V,Disjoint L R ∧ L∪R=S ∧
    (∀ i∈L,2≤nbr G i Lᶜ) ∧ (∀ i∈R,2≤nbr G i Rᶜ)

theorem split_high (S : Finset V) (sub : S⊆high G) : Split G S := by
  classical
  obtain ⟨A,_,_,la,rb⟩ := PinnedColor34.cut G ∅ ∅ (by simp)
  refine ⟨S∩A,S\A,disjoint_left.mpr (fun _ m h => (mem_sdiff.mp h).2 (mem_inter.mp m).2),
    ?_,?_,?_⟩
  · ext i; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  · intro i m
    obtain ⟨im,ia⟩ := mem_inter.mp m
    have dg : 3≤G.degree i := (mem_filter.mp (sub im)).2
    have := la i ia (not_mem_empty _)
    have := Repair.full_nbr G i A
    exact (show 2≤nbr G i Aᶜ by omega).trans (Repair.nbr_mono G _ (compl_subset_compl.mpr inter_subset_right))
  · intro i m
    obtain ⟨im,ia⟩ := mem_sdiff.mp m
    have dg : 3≤G.degree i := (mem_filter.mp (sub im)).2
    have := rb i (mem_compl.mpr ia) (not_mem_empty _)
    have := Repair.full_nbr G i A
    exact (show 2≤nbr G i A by omega).trans (Repair.nbr_mono G _ (fun _ h => mem_compl.mpr (fun p => (mem_sdiff.mp p).2 h)))

theorem Split.exact {S : Finset V} (split : Split G S) (size : (types G).card≤S.card) : gamma G≤bound G := by
  obtain ⟨L,R,sep,eq,l,r⟩ := split
  have left := Repair.omit_set G L l
  have right := Repair.omit_set G R r
  have count := card_union_of_disjoint sep
  rw [eq] at count; unfold bound; omega

/-- A degree-two vertex can be added to one of the two omission sets whenever
one of its neighbors is still outside their union. -/
theorem Split.adjoin {S : Finset V} (split : Split G S) {u v : V} (du : G.degree u=2)
    (uv : G.Adj u v) (vo : v∉S) : Split G (insert u S) := by
  classical
  by_cases us : u∈S
  · simpa [insert_eq_of_mem us] using split
  obtain ⟨L,R,dis,rfl,l,r⟩ := split
  obtain ⟨y,ym,yv⟩ := exists_mem_ne (s:=G.neighborFinset u) (by rw [card_neighborFinset_eq_degree,du]; decide) v
  have pair : {v,y}⊆G.neighborFinset u := insert_subset ((G.mem_neighborFinset ..).mpr uv) (singleton_subset_iff.mpr ym)
  have eq := (eq_of_subset_of_card_le pair (by rw [card_pair yv.symm,card_neighborFinset_eq_degree,du])).symm
  have keep (D : Finset V) (sub : D⊆L∪R) (yd : y∉D) (safe : ∀ i∈D,2≤nbr G i Dᶜ) :
      ∀ i∈insert u D,2≤nbr G i (insert u D)ᶜ := by
    have no (i : V) (id : i∈D) (ui : G.Adj u i) : False := by
      have m := (G.mem_neighborFinset ..).mpr ui
      rw [eq] at m
      exact (mem_insert.mp m).elim (fun p => vo (p ▸ sub id)) (fun p => yd (mem_singleton.mp p ▸ id))
    intro i im
    rcases mem_insert.mp im with rfl|id
    · have ss : G.neighborFinset i ⊆ (insert i D)ᶜ.filter (G.Adj i) := by
        intro j jm
        have ij := (G.mem_neighborFinset ..).mp jm
        exact mem_filter.mpr ⟨mem_compl.mpr (fun m => (mem_insert.mp m).elim ij.ne.symm (fun md => no j md ij)),ij⟩
      simpa only [nbr,card_neighborFinset_eq_degree,du] using card_le_card ss
    · apply (safe i id).trans (card_le_card ?_)
      intro j jm
      obtain ⟨jc,ij⟩ := mem_filter.mp jm
      refine mem_filter.mpr ⟨mem_compl.mpr (fun m => ?_),ij⟩
      rcases mem_insert.mp m with rfl|jd
      · exact no i id ij.symm
      · exact mem_compl.mp jc jd
  by_cases yl : y∈L
  · have ur : u∉L := fun m => us (mem_union_left _ m)
    exact ⟨L,insert u R,by simpa [ur] using dis,by ext; simp,l,
      keep R subset_union_right (fun m => disjoint_left.mp dis yl m) r⟩
  · have ur : u∉R := fun m => us (mem_union_right _ m)
    exact ⟨insert u L,R,by simpa [ur] using dis,by simp,keep L subset_union_left yl l,r⟩

omit [DecidableEq V] in
private theorem off_high {u : V} (du : G.degree u≤2) : u∉high G := by
  intro m; have := (mem_filter.mp m).2; omega

/-- Two degree-two vertices can be processed in sequence when their indicated
low neighbors remain available at their respective steps. -/
theorem two_steps {f u w v : V} (fu : f≠u) (df : G.degree f=2) (du : G.degree u=2)
    (fw : G.Adj f w) (dw : G.degree w≤2) (uv : G.Adj u v) (dv : G.degree v≤2)
    (vf : v≠f) : gamma G≤bound G := by
  have s := (split_high G _ Subset.rfl).adjoin G df fw (off_high G dw)
  have next := s.adjoin G du uv (show v∉insert f (high G) by simp [vf,off_high G dv])
  apply next.exact
  have := type_bound G
  simp [card_insert_of_not_mem,fu.symm,off_high G du.le,off_high G df.le]
  omega

/-- Any two edges between degree-two vertices in a failure are the same
unordered edge, at all orders and triangle diversities. -/
theorem unique_edge {u v x y : V} (uv : G.Adj u v) (xy : G.Adj x y)
    (du : G.degree u=2) (dv : G.degree v=2) (dx : G.degree x=2) (dy : G.degree y=2)
    (bad : bound G<gamma G) : ({u,v}:Finset V)={x,y} := by
  by_cases xu : x=u
  · subst x
    by_cases yv : y=v
    · rw [yv]
    · exact False.elim ((not_lt_of_ge (two_steps G yv dy dv xy.symm du.le uv.symm du.le xy.ne)) bad)
  by_cases yu : y=u
  · subst y
    by_cases xv : x=v
    · rw [xv,pair_comm]
    · exact False.elim ((not_lt_of_ge (two_steps G xv dx dv xy du.le uv.symm du.le xy.ne.symm)) bad)
  by_cases xv : x=v
  · subst x
    exact False.elim ((not_lt_of_ge (two_steps G yu dy du xy.symm dv.le uv dv.le xy.ne)) bad)
  · exact False.elim ((not_lt_of_ge (two_steps G xu dx du xy dy.le uv dv.le (Ne.symm xv))) bad)

/-- If the third degree-two vertex shares an anchor with the adjacent pair,
set that anchor aside and adjoin all three low vertices. -/
theorem shared_anchor {u v f a : V} (uv : G.Adj u v) (va : G.Adj v a) (fa : G.Adj f a)
    (uf : u≠f) (vf : v≠f) (du : G.degree u=2) (dv : G.degree v=2)
    (df : G.degree f=2) : gamma G≤bound G := by
  by_cases au : a=u
  · subst a
    exact two_steps G vf dv df uv.symm du.le fa du.le uv.ne
  let H := (high G).erase a
  have s := split_high G H (erase_subset ..)
  have al : a∉H := not_mem_erase _ _
  have vl : v∉H := fun m => off_high G dv.le (mem_erase.mp m).2
  have fl : f∉H := fun m => off_high G df.le (mem_erase.mp m).2
  have ul : u∉H := fun m => off_high G du.le (mem_erase.mp m).2
  have p := s.adjoin G du uv vl
  have p' := p.adjoin G dv va (by simp [au,al])
  have p'' := p'.adjoin G df fa (by simp [au,va.ne.symm,al])
  apply p''.exact
  have := type_bound G
  have card := card_le_card (show high G⊆insert a H by
    intro i im; by_cases ia : i=a
    · exact mem_insert.mpr (Or.inl ia)
    · exact mem_insert_of_mem (mem_erase.mpr ⟨ia,im⟩))
  have inc := card_insert_le a H
  simp [card_insert_of_not_mem,fl,vl,ul,vf.symm,uf.symm,uv.ne.symm]
  omega

end Graffiti384b.Adjacent15
#print axioms Graffiti384b.Adjacent15.split_high
#print axioms Graffiti384b.Adjacent15.Split.adjoin
#print axioms Graffiti384b.Adjacent15.Split.exact
#print axioms Graffiti384b.Adjacent15.two_steps
#print axioms Graffiti384b.Adjacent15.unique_edge
#print axioms Graffiti384b.Adjacent15.shared_anchor
