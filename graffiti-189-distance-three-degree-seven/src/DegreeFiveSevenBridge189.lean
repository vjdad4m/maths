import DegreeFiveEightBridgeRoutes189
import DegreeFiveAlternatingBlock189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem bridge_route_at_three_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (localThree : S.localA.card=3)
    (foreignFour : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (bridge : portBridge S) :
    ∃ p,∃ q,G.Adj a p ∧ G.Adj b q ∧ RouteOn G S.L p q := by
  classical
  let A := S.localA
  let E := S.L\A
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have xA : x∈A := mem_filter.mpr ⟨xl,ax⟩
  have yA : y∉A := fun h=>not_common far (mem_filter.mp h).2 by'
  have yE : y∈E := mem_sdiff.mpr ⟨yl,yA⟩
  have aSub : A⊆S.L := filter_subset _ _
  have sep : Disjoint A E := disjoint_left.mpr (fun z za ze=>(mem_sdiff.mp ze).2 za)
  have univ := bridge_four_forces_universal S hc far even foreignFour xl ax xy by'
  have adj (p : V) (pA : p∈A) (z : V) (zl : z∈S.L) (pz : p≠z) (zy : z≠y) :
      G.Adj p z := by
    have pL := aSub pA
    have ap := (mem_filter.mp pA).2
    by_cases px : p=x
    · subst p
      exact (univ z zl).resolve_left (fun e=>pz e.symm)
    have xp := (univ p pL).resolve_left px
    by_cases hit : ∃ w∈S.L,G.Adj b w ∧ G.Adj p w
    · obtain ⟨w,_,bw,pw⟩ := hit
      exact (bridge_four_forces_universal S hc far even foreignFour pL ap pw bw z zl).resolve_left
        (fun e=>pz e.symm)
    have py : p≠y := fun h=>yA (h ▸ pA)
    have pyn : ¬G.Adj p y := fun h=>hit ⟨y,yl,by',h⟩
    have y2 := d2 hc py pyn xp.symm xy
    apply Classical.byContradiction
    intro pzn
    have zx : z≠x := fun e=>pzn (e.symm ▸ xp.symm)
    have xz := (univ z zl).resolve_left zx
    have z2 := d2 hc pz pzn xp.symm xz
    exact zy (singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zl yl z2 y2)
  have cl : CompleteOn G A := by
    intro p pA z zA ne
    exact adj p pA z (aSub zA) ne (fun e=>yA (e ▸ zA))
  have cap : E.card≤4 := by
    have h := bound_bridge_side_of_opposite_four S hc far even rightConnected rightA rightB
      foreignFour ⟨x,xl,y,yl,ax,xy,by'⟩
    have q : E.card+A.card=S.L.card := card_sdiff_add_card_eq_card aSub
    change A.card=3 at localThree
    change S.L.card≤A.card+4 at h
    omega
  have cross (p : V) (pA : p∈A) (z : V) (ze : z∈E) (zy : z≠y) : G.Adj p z :=
    adj p pA z (mem_sdiff.mp ze).1 (fun e=>(mem_sdiff.mp ze).2 (e ▸ pA)) zy
  have key : A∪E=S.L := union_sdiff_of_subset aSub
  by_cases easy : E.card≤3
  · have h : E.card≤A.card := by
      change A.card=3 at localThree
      omega
    obtain ⟨p,pp,route⟩ := route_clique_join_end_leaf sep cl
      (fun p pp z zz=>cross p pp z (mem_erase.mp zz).2 (mem_erase.mp zz).1) h xA yE xy
    exact ⟨p,y,(mem_filter.mp pp).2,by',key ▸ route⟩
  have e4 : E.card=4 := by omega
  have some : ∃ s∈E,∃ t∈E,G.Adj s t := by
    apply Classical.byContradiction
    intro no
    have low (z : V) (ze : z∈E) : ¬5≤G.degree z := by
      obtain ⟨zL,za⟩ := mem_sdiff.mp ze
      have az : ¬G.Adj a z := fun az=>za (mem_filter.mpr ⟨zL,az⟩)
      have sub : G.neighborFinset z⊆insert b A := by
        intro v vm
        have zv := (mem_neighborFinset G z v).mp vm
        rcases left_boundary S z zL v zv with va|vb|vL
        · exact (az (va ▸ zv.symm)).elim
        · exact mem_insert.mpr (.inl vb)
        by_cases vA : v∈A
        · exact mem_insert_of_mem vA
        exact (no ⟨z,ze,v,mem_sdiff.mpr ⟨vL,vA⟩,zv⟩).elim
      have m := (card_le_card sub).trans (card_insert_le b A)
      rw [card_neighborFinset_eq_degree] at m
      change A.card=3 at localThree
      omega
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (show 1<E.card by omega)
    exact (degree u v uv).elim (low u ue) (low v ve)
  obtain ⟨s,se,t,te,st⟩ := some
  have block (s t : V) (se : s∈E) (te : t∈E) (st : G.Adj s t) :
      ∃ p∈A,RouteOn G (A∪E) p y := by
    let B := ({s,t} : Finset V)
    let L := E\B
    have sub : B⊆E := insert_subset_iff.mpr ⟨se,singleton_subset_iff.mpr te⟩
    have lsub : L⊆E := sdiff_subset
    have b2 : B.card=2 := by simp [B,st.ne]
    have l2 : L.card=2 := by
      change (E\B).card=2
      rw [card_sdiff sub,e4,b2]
    have ca : A.card=3 := localThree
    have sOff : s∉A∪L := by
      intro h
      exact (mem_union.mp h).elim (fun a=>(mem_sdiff.mp se).2 a)
        (fun l=>(mem_sdiff.mp l).2 (by simp [B]))
    have tOff : t∉A∪L := by
      intro h
      exact (mem_union.mp h).elim (fun a=>(mem_sdiff.mp te).2 a)
        (fun l=>(mem_sdiff.mp l).2 (by simp [B]))
    have cover : (A∪L)∪B=A∪E := by
      have e : L∪B=E := sdiff_union_of_subset sub
      rw [union_assoc,e]
    by_cases ty : t=y
    · subst t
      have no (h : V) (hh : h∈A) (l : V) (ll : l∈L) : G.Adj h l :=
        cross h hh l (lsub ll) (fun e=>(mem_sdiff.mp ll).2 (e.symm ▸ (show y∈B by simp [B])))
      obtain ⟨p,pp,route⟩ := route_clique_join_end_block (sep.mono (Subset.refl _) lsub)
        cl no sOff tOff (by omega) xA (cross x xA s se st.ne) st
      exact ⟨p,pp,cover ▸ route⟩
    by_cases sy : s=y
    · subst s
      have no (h : V) (hh : h∈A) (l : V) (ll : l∈L) : G.Adj h l :=
        cross h hh l (lsub ll) (fun e=>(mem_sdiff.mp ll).2 (e.symm ▸ (show y∈B by simp [B])))
      obtain ⟨p,pp,route⟩ := route_clique_join_end_block (sep.mono (Subset.refl _) lsub)
        cl no tOff sOff (by omega) xA (cross x xA t te ty) st.symm
      have eq : (A∪L)∪({t,y} : Finset V)=(A∪L)∪B := by ext w; simp [B,or_comm,or_left_comm,or_assoc]
      exact ⟨p,pp,eq.trans cover ▸ route⟩
    have yy : y∈L := mem_sdiff.mpr ⟨yE,by simp [B,show y≠s from fun e=>sy e.symm,show y≠t from fun e=>ty e.symm]⟩
    obtain ⟨p,pp,route⟩ := route_clique_join_block_before_leaf
      (sep.mono (Subset.refl _) lsub) cl
      (fun h hh u uu=>cross h hh u (lsub (mem_erase.mp uu).2) (mem_erase.mp uu).1)
      (fun h hh=>cross h hh s se sy) (fun h hh=>(cross h hh t te ty).symm)
      sOff tOff st (by omega) xA yy xy
    exact ⟨p,pp,cover ▸ route⟩
  obtain ⟨p,pp,route⟩ := block s t se te st
  exact ⟨p,y,(mem_filter.mp pp).2,by',key ▸ route⟩

#print axioms bridge_route_at_three_four
end Graffiti189LongestPath.CrossSaturation.Split.Five
