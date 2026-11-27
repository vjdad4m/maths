import FrontierPivot31
namespace Graffiti384b.Frontier31
open Finset SimpleGraph CliquePivot33
open private Repair.nbr_add Repair.isolate from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every original vertex outside the positive core is retained. This
allows all its neighbors to receive a credit at the same time. -/
theorem rooted_tight (t : (types G).card=31) (q : (nonleaves G).card=30) (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    Tight H (univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)) := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
  change Tight H R
  intro D good
  let emb : P ↪ V := Function.Embedding.subtype _
  let K := D.map emb
  have dis : Disjoint K Pᶜ := disjoint_left.mpr (by
    intro w wm outside; obtain ⟨v,_,rfl⟩ := mem_map.mp wm; exact mem_compl.mp outside v.property)
  have counts (v : P) : nbr G v.val K=nbr H v D := by
    have eq : K.filter (G.Adj v.val)=(D.filter (H.Adj v)).map emb := by
      ext w; constructor
      · intro h
        obtain ⟨u,um,rfl⟩ := mem_map.mp (mem_filter.mp h).1
        exact mem_map.mpr ⟨u,mem_filter.mpr ⟨um,(mem_filter.mp h).2⟩,rfl⟩
      · intro h
        obtain ⟨u,um,rfl⟩ := mem_map.mp h
        exact mem_filter.mpr ⟨mem_map.mpr ⟨u,(mem_filter.mp um).1,rfl⟩,(mem_filter.mp um).2⟩
    exact (congrArg card eq).trans (card_map ..)
  have dom : TwoDominates G (K∪Pᶜ) := by
    intro v out
    have vm : v∈P := Classical.byContradiction (fun vm => out (mem_union_right _ (mem_compl.mpr vm)))
    let w : P := ⟨v,vm⟩
    have low := good w (fun m => out (mem_union_left _ (mem_map.mpr ⟨w,m,rfl⟩)))
    change 2≤nbr H w D+(if w∈R then 1 else 0) at low
    rw [←counts w] at low; rw [Repair.nbr_add G v dis]
    have credit : (if w∈R then 1 else 0)≤nbr G v Pᶜ := by
      split_ifs with yes
      · obtain ⟨z,outside,edge⟩ := (mem_filter.mp yes).2
        exact card_pos.mpr ⟨z,mem_filter.mpr ⟨mem_compl.mpr outside,edge⟩⟩
      · exact Nat.zero_le _
    exact low.trans (Nat.add_le_add_left credit _)
  have cap : gamma G≤(K∪Pᶜ).card := Nat.sInf_le ⟨_,dom,rfl⟩
  rw [card_union_of_disjoint dis,show K.card=D.card from card_map ..,card_compl] at cap
  have sz : P.card=30 := q
  have n : P.card≤Fintype.card V := card_le_univ P
  unfold bound at bad; rw [t] at bad
  change Fintype.card P≤2*D.card; rw [Fintype.card_coe]; omega

/-- If the unique degree-two vertex is credited by a retained leaf, the
two protected pairs can omit their center without any other protected pins. -/
theorem ear_uncredited {R : Finset V} (tight : Tight G R) {e x : V}
    (de : G.degree e=2) (rest : ∀ v,v≠e → 3≤G.degree v) (dx : G.degree x=4) (sx : trianglesAt G x=5) : e∉R := by
  classical
  intro credit
  obtain ⟨P,Q,un,_,_,frame,px,qx⟩ := pivot_frame G dx sx
  have xn := G.not_mem_neighborFinset_self x
  apply (shared G R frame.1 (fun m => xn (un ▸ mem_union_left Q m)) (fun m => xn (un ▸ mem_union_right P m))
    px qx frame.2.1 frame.2.2 ?_) tight
  intro v vx vp vq
  have no : x∉G.neighborFinset v := by
    intro m; have vn := (G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp m).symm
    rw [←un] at vn; exact (mem_union.mp vn).elim vp vq
  rw [CliquePivot33.isolated_degree G vx,erase_eq_of_not_mem no,card_neighborFinset_eq_degree]
  by_cases eq : v=e
  · subst v; simp [credit,de]
  · have := rest v eq; omega

/-- The ear is a genuine degree-two vertex of the original graph. -/
theorem original_ear (hc : G.Connected) (t : (types G).card=31)
    (cap : ∀ v,G.degree v≤9 → trianglesAt G v≤RankTable.cap (G.degree v) 3) (bad : bound G<gamma G) :
    ∃ e,G.degree e=2 ∧ trianglesAt G e=1 ∧ G.neighborFinset e⊆nonleaves G := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
  obtain ⟨sz,_,sc,fi,pos,g,_,x,dx,sx⟩ := core G hc t cap bad
  have h : Fintype.card P≤2*gamma H := by rw [sz,show gamma H=15 from g]
  obtain ⟨e,de,se,lo,_⟩ := ear_barrier H dx sx h pos fi
  have q := (profile G t cap bad).1
  have tight : Tight H R := rooted_tight G t q bad
  have off := ear_uncredited H tight de lo dx sx
  have all : G.neighborFinset e.val⊆P := by
    intro z zm; apply Classical.byContradiction; intro outside
    exact off (mem_filter.mpr ⟨mem_univ _,z,outside,(G.mem_neighborFinset ..).mp zm⟩)
  have eq : P.filter (G.Adj e.val)=G.neighborFinset e.val := by
    ext z; simp only [mem_filter,G.mem_neighborFinset]; exact ⟨And.right,fun adj => ⟨all ((G.mem_neighborFinset ..).mpr adj),adj⟩⟩
  have d := EarAnchor.induced_degree G (W:=P) e
  change H.degree e=(P.filter _).card at d
  rw [eq,card_neighborFinset_eq_degree] at d
  exact ⟨e.val,d.symm.trans de,(sc e).symm.trans se,all⟩

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.rooted_tight
#print axioms Graffiti384b.Frontier31.ear_uncredited
#print axioms Graffiti384b.Frontier31.original_ear
