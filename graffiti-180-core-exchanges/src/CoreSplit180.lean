import FirstForm180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem score_iff_core (G : SimpleGraph V) (hc : G.Connected) (hn : 2<Fintype.card V)
    (W : Finset V) (m : ℕ) :
    m≤weightedLeaves G W ↔ ∃ C⊆W, m≤C.card ∧ Con G (univ\C) ∧ ∀ z∈C, Dominates G (univ\C) z := by
  constructor
  · intro score
    obtain ⟨T,sub,tr,opt⟩ := tree_opt G hc W
    exact ⟨W∩leaves T,inter_subset_left,opt ▸ score,leaf_core G T sub tr hn _ inter_subset_right⟩
  · rintro ⟨C,cw,count,conn,cover⟩
    have bound := weightedCore G (univ\C) W conn (by intro x h; exact cover x (by simpa using h))
    exact count.trans ((card_le_card (show C⊆W\(univ\C) from fun z hz => mem_sdiff.mpr ⟨cw hz,by simp [hz]⟩)).trans bound)

/-- Starting from a specified second form, compare to the entire lower optimum. -/
theorem second_split_iff (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) :
    FirstForm J U x y w ↔ ∃ B⊆C.erase x, ∃ Z⊆(U\C).erase y, B.card<Z.card ∧
      let L := ((C.erase x)\B)∪Z
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ q∈L, Dominates (J⊔SimpleGraph.edge x y) (univ\L) q := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let W := U\{x,y}
  let C0 := C.erase x
  have xc := tip.1
  have yn : y∉C := (mem_sdiff.mp tip.2.1).2
  have sz : C0.card=weightedLeaves J U := by have := card_erase_add_one xc; change (C.erase x).card=_; omega
  have co : C0⊆W := by
    intro q h
    obtain ⟨qx,qc⟩ := mem_erase.mp h
    exact mem_sdiff.mpr ⟨cu qc,by simp [qx,show q≠y from fun e => yn (e ▸ qc)]⟩
  rw [first_iff_erased_gain J hc hn x y w xy old xw wy]
  change weightedLeaves J U<weightedLeaves G W ↔ _
  constructor
  · intro gain
    obtain ⟨L,lw,num,conn,dom⟩ := (score_iff_core G (hc.mono le_sup_left) hn W (weightedLeaves J U+1)).mp gain
    let B := C0\L
    let Z := L\C0
    have zs : Z⊆(U\C).erase y := by
      intro q h; obtain ⟨ql,nc⟩ := mem_sdiff.mp h
      obtain ⟨qu,ne⟩ := mem_sdiff.mp (lw ql)
      simp only [mem_insert,mem_singleton,not_or] at ne
      exact mem_erase.mpr ⟨ne.2,mem_sdiff.mpr ⟨qu,fun qc => nc (mem_erase.mpr ⟨ne.1,qc⟩)⟩⟩
    have sizeB := card_sdiff_add_card_inter C0 L
    have sizeZ := card_sdiff_add_card_inter L C0
    rw [inter_comm L C0] at sizeZ
    have eq : (C0\B)∪Z=L := by ext q; simp only [B,Z,mem_sdiff,mem_union]; tauto
    refine ⟨B,sdiff_subset,Z,zs,?_,?_⟩
    · change (C0\L).card<(L\C0).card; omega
    · change Con G (univ\((C0\B)∪Z)) ∧ _
      rw [eq]; exact ⟨conn,dom⟩
  · rintro ⟨B,bc,Z,zs,win,conn,dom⟩
    let L := (C0\B)∪Z
    have zw : Z⊆W := by
      intro q h; obtain ⟨qy,k⟩ := mem_erase.mp (zs h)
      obtain ⟨qu,qc⟩ := mem_sdiff.mp k
      exact mem_sdiff.mpr ⟨qu,by simp [qy,show q≠x from fun e => qc (e ▸ xc)]⟩
    have dis : Disjoint (C0\B) Z := disjoint_left.mpr (fun q h z => (mem_sdiff.mp (mem_of_mem_erase (zs z))).2
      (mem_of_mem_erase (mem_sdiff.mp h).1))
    have len : L.card=(C0\B).card+Z.card := card_union_of_disjoint dis
    have diff := card_sdiff_add_card_eq_card (show B⊆C0 from bc)
    apply (score_iff_core G (hc.mono le_sup_left) hn W (weightedLeaves J U+1)).mpr
    exact ⟨L,union_subset (sdiff_subset.trans co) zw,by omega,conn,dom⟩

theorem first_of_local_split (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C B Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (bc : B⊆C.erase x) (zs : Z⊆(U\C).erase y)
    (win : B.card<Z.card) (patch : Con J (insert x B))
    (touch : let S := (univ\C)\Z
      ∀ a∈S, ∃ t∈S, (within J S).Reachable a t ∧ (t=y ∨ Dominates J (insert x B) t))
    (survive : let S := (univ\C)\Z
      ∀ q∈((C.erase x\B)∪Z), Dominates J S q ∨ Dominates J (insert x B) q) :
    FirstForm J U x y w := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let S := (univ\C)\Z
  let K := insert x B
  let L := (C.erase x\B)∪Z
  have xc := tip.1
  have yn := (mem_sdiff.mp tip.2.1).2
  have yz : y∉Z := fun h => (mem_erase.mp (zs h)).1 rfl
  have ys : y∈S := by simp [S,yn,yz]
  have xk : x∈K := mem_insert_self _ _
  have xz : x∉Z := fun h => (mem_sdiff.mp (mem_of_mem_erase (zs h))).2 xc
  have eq : univ\L=S∪K := by
    ext a
    by_cases ax : a=x
    · subst a; simp [L,S,K,xz]
    have bz (b:a∈B) := mem_of_mem_erase (bc b)
    have zc (z:a∈Z) := (mem_sdiff.mp (mem_of_mem_erase (zs z))).2
    simp only [L,S,K,mem_sdiff,mem_univ,true_and,mem_union,mem_erase,mem_insert,ax,not_false_eq_true,false_or] 
    tauto
  apply (second_split_iff J hc hn x y w xy old xw wy U C cu count tip).mpr
  refine ⟨B,bc,Z,zs,win,?_⟩
  change Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q
  rw [eq]
  have add : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  constructor
  · apply (connected_cuts G (S∪K)).mpr
    refine ⟨⟨y,mem_union_left _ ys⟩,?_⟩
    intro f good
    have sameK := (connected_cuts J K).mp patch |>.2 f
      (fun a ha b hb e => good a (mem_union_right _ ha) b (mem_union_right _ hb) (Or.inl e))
    have anchor := good x (mem_union_right _ xk) y (mem_union_left _ ys) add
    have route {a t} (p:(within J S).Walk a t) : f a=f t := by
      induction p with
      | nil => rfl
      | cons e _ ih => exact (good _ (mem_union_left _ e.2.1) _ (mem_union_left _ e.2.2) (Or.inl e.1)).trans ih
    have all (a:V) (ha:a∈S∪K) : f a=f y := by
      rcases mem_union.mp ha with hs|hk
      · obtain ⟨t,ts,⟨p⟩,rfl|⟨b,bk,e⟩⟩ := touch a hs
        · exact route p
        · exact (route p).trans ((good t (mem_union_left _ ts) b (mem_union_right _ bk) (Or.inl e)).trans ((sameK b bk x xk).trans anchor))
      · exact (sameK a hk x xk).trans anchor
    exact fun a ha b hb => (all a ha).trans (all b hb).symm
  · intro q h
    rcases survive q h with ⟨t,ts,e⟩|⟨t,tk,e⟩
    · exact ⟨t,mem_union_left _ ts,Or.inl e⟩
    · exact ⟨t,mem_union_right _ tk,Or.inl e⟩

#print axioms score_iff_core
#print axioms second_split_iff
#print axioms first_of_local_split
end Minimal180
