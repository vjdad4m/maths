import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem six_port_two_inner_route
    (A B I : Finset V) (a3 : A.card=3) (b3 : B.card=3) (i2 : I.card=2)
    (ac : CompleteOn G A) (bc : CompleteOn G B)
    (ab : Disjoint A B) (ai : Disjoint A I) (bi : Disjoint B I)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (aN : ∀ x∈A,5≤G.degree x → ∀ z∈I,G.Adj x z)
    (bN : ∀ x∈B,5≤G.degree x → ∀ z∈I,G.Adj x z) :
    ∃ l∈A,∃ r∈B,RouteOn G ((A∪I)∪B) l r := by
  classical
  obtain ⟨x,xA,y,yA,xy,xh,yh⟩ := two_high_points a3 degree
  obtain ⟨u,v,uv,eq⟩ := card_eq_two.mp i2
  have um : u∈I := by simp [eq]
  have vm : v∈I := by simp [eq]
  obtain ⟨z,zB,w,wB,zw,zh,wh⟩ := two_high_points b3 degree
  let A' := A.erase y
  have xA' : x∈A' := mem_erase.mpr ⟨xy,xA⟩
  have acl : CompleteOn G A' := fun u ua v va ne=>ac u (mem_of_mem_erase ua) v (mem_of_mem_erase va) ne
  obtain ⟨l,p,pp,ps⟩ := rooted_path_in_clique A' acl xA'
  let J : Finset V := {u,y,v}
  have jy : RouteOn G J u v := RouteOn.three (aN y yA yh u um).symm (aN y yA yh v vm) uv
  have aJ : Disjoint A' J := by
    apply disjoint_left.mpr
    intro t ta tj
    simp only [J,mem_insert,mem_singleton] at tj
    rcases tj with e|e|e
    · exact disjoint_left.mp ai (mem_of_mem_erase ta) (e.symm ▸ um)
    · exact (mem_erase.mp ta).1 e
    exact disjoint_left.mp ai (mem_of_mem_erase ta) (e.symm ▸ vm)
  have jB : Disjoint J B := by
    apply disjoint_left.mpr
    intro t tj tb
    simp only [J,mem_insert,mem_singleton] at tj
    rcases tj with e|e|e
    · exact disjoint_left.mp bi tb (e.symm ▸ um)
    · exact disjoint_left.mp ab (e.symm ▸ yA) tb
    exact disjoint_left.mp bi tb (e.symm ▸ vm)
  have r1 : RouteOn G A' l x := (show RouteOn G A' x l from ⟨p,pp,ps⟩).reverse
  have r2 := r1.join jy aJ (aN x xA xh u um)
  obtain ⟨r,q,qp,qs⟩ := rooted_path_in_clique B bc zB
  have q' : RouteOn G B z r := ⟨q,qp,qs⟩
  have r3 := r2.join q' (disjoint_union_left.mpr ⟨ab.mono_left (erase_subset _ _),jB⟩)
    (bN z zB zh v vm).symm
  have e : A'∪J=A∪I := by
    ext t
    by_cases ty : t=y
    · simp [A',J,ty,yA]
    simp [A',J,eq,ty,or_assoc]
  rw [e] at r3
  exact ⟨l,mem_of_mem_erase ((ps l).mp p.end_mem_support),r,(qs r).mp q.end_mem_support,r3⟩

private theorem all_nonport_neighbors_inside {A I : Finset V} {x : V}
    (a3 : A.card=3) (i3 : I.card=3) (xi : x∈I)
    (hi : 5≤G.degree x) (sub : G.neighborFinset x⊆A∪I.erase x) :
    I.erase x ⊆ G.neighborFinset x := by
  have c := card_union_le A (I.erase x)
  rw [card_erase_of_mem xi,a3,i3] at c
  have e := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; omega)
  rw [e]
  exact subset_union_right

/-- The three nonporters are routable between the two port cliques. When
the two shells coincide, the sole deep vertex has only two possible
neighbors. Otherwise one exclusive-shell vertex is high and sees both
other nonporters. -/
theorem six_port_three_inner_route
    (A B I E F : Finset V) (a3 : A.card=3) (b3 : B.card=3) (i3 : I.card=3)
    (e2 : E.card=2) (f2 : F.card=2) (ei : E⊆I) (fi : F⊆I)
    (ac : CompleteOn G A) (bc : CompleteOn G B)
    (ab : Disjoint A B) (ai : Disjoint A I) (bi : Disjoint B I)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (minTwo : ∀ z∈I,2≤G.degree z)
    (aN : ∀ x∈A,5≤G.degree x → ∀ z∈E,G.Adj x z)
    (bN : ∀ x∈B,5≤G.degree x → ∀ z∈F,G.Adj x z)
    (dep : ∀ z∈I,z∉E → z∉F → G.neighborFinset z⊆I.erase z)
    (eN : ∀ z∈E,z∉F → G.neighborFinset z⊆A∪I.erase z)
    (fN : ∀ z∈F,z∉E → G.neighborFinset z⊆B∪I.erase z) :
    ∃ l∈A,∃ r∈B,RouteOn G ((A∪I)∪B) l r := by
  classical
  obtain ⟨x,xA,_,_,_,xh,_⟩ := two_high_points a3 degree
  obtain ⟨y,yB,_,_,_,yh,_⟩ := two_high_points b3 degree
  have finish {u v : V} (ue : u∈E) (vf : v∈F) (p : RouteOn G I u v) :
      ∃ l∈A,∃ r∈B,RouteOn G ((A∪I)∪B) l r :=
    route_join_cliques ac bc ab ai bi xA yB (aN x xA xh u ue) (bN y yB yh v vf).symm p
  by_cases eq : E=F
  · obtain ⟨u,v,uv,he⟩ := card_eq_two.mp e2
    have ue : u∈E := by simp [he]
    have ve : v∈E := by simp [he]
    have cnt := card_inter_add_card_sdiff I E
    rw [inter_eq_right.mpr ei,i3,e2] at cnt
    obtain ⟨w,wm⟩ := card_pos.mp (by omega : 0<(I\E).card)
    obtain ⟨wi,we⟩ := mem_sdiff.mp wm
    have wu : w≠u := fun e=>we (e.symm ▸ ue)
    have wv : w≠v := fun e=>we (e.symm ▸ ve)
    have sub := dep w wi we (by simpa [←eq] using we)
    have all := eq_of_subset_of_card_le sub (by
      rw [card_neighborFinset_eq_degree,card_erase_of_mem wi,i3]
      exact minTwo _ wi)
    have uw : G.Adj u w := ((mem_neighborFinset _ _ _).mp (all.symm ▸ mem_erase.mpr ⟨wu.symm,ei ue⟩)).symm
    have wv' : G.Adj w v := (mem_neighborFinset _ _ _).mp (all.symm ▸ mem_erase.mpr ⟨wv.symm,ei ve⟩)
    have s : ({u,w,v}:Finset V)⊆I := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl
      · exact ei ue
      · exact wi
      · exact ei ve
    have ident := eq_of_subset_of_card_le s (by rw [i3]; simp [uv,wu.symm,wv])
    exact finish ue (eq ▸ ve) (ident ▸ RouteOn.three uw wv' uv)
  have c : (E∪F).card≤3 := (card_le_card (union_subset ei fi)).trans_eq i3
  have h := card_union_add_card_inter E F
  have both : (E∩F).card=1 := by
    have limit : (E∩F).card≤2 := (card_le_card inter_subset_left).trans_eq e2
    apply Classical.byContradiction
    intro no
    have ht : (E∩F).card=2 := by omega
    have e1 : E∩F=E := eq_of_subset_of_card_le inter_subset_left (by omega)
    have f1 : E∩F=F := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact eq (e1.symm.trans f1)
  obtain ⟨w,hW⟩ := card_eq_one.mp both
  have wm : w∈E∩F := by simp [hW]
  have ew := (mem_inter.mp wm).1
  have fw := (mem_inter.mp wm).2
  have es : (E\F).card=1 := by
    have k := card_inter_add_card_sdiff E F
    omega
  have fs : (F\E).card=1 := by
    have k := card_inter_add_card_sdiff F E
    rw [inter_comm] at k
    omega
  obtain ⟨u,um⟩ := card_pos.mp (by omega : 0<(E\F).card)
  obtain ⟨v,vm⟩ := card_pos.mp (by omega : 0<(F\E).card)
  obtain ⟨ue,uf⟩ := mem_sdiff.mp um
  obtain ⟨vf,ve⟩ := mem_sdiff.mp vm
  have uvi : u≠v := fun e=>uf (e.symm ▸ vf)
  have uwi : u≠w := fun e=>uf (e.symm ▸ fw)
  have vwi : v≠w := fun e=>ve (e.symm ▸ ew)
  have ui := ei ue
  have vi := fi vf
  have wi := ei ew
  rcases degree u v uvi with uh|vh
  · have nb := all_nonport_neighbors_inside a3 i3 ui uh (eN u ue uf)
    have uw : G.Adj u w := (mem_neighborFinset _ _ _).mp (nb (mem_erase.mpr ⟨uwi.symm,wi⟩))
    have uv : G.Adj u v := (mem_neighborFinset _ _ _).mp (nb (mem_erase.mpr ⟨uvi.symm,vi⟩))
    have s : ({w,u,v}:Finset V)⊆I := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl
      · exact wi
      · exact ui
      · exact vi
    have ident := eq_of_subset_of_card_le s (by rw [i3]; simp [uwi.symm,vwi.symm,uvi])
    exact finish ew vf (ident ▸ RouteOn.three uw.symm uv vwi.symm)
  have nb := all_nonport_neighbors_inside b3 i3 vi vh (fN v vf ve)
  have vu : G.Adj v u := (mem_neighborFinset _ _ _).mp (nb (mem_erase.mpr ⟨uvi,ui⟩))
  have vw : G.Adj v w := (mem_neighborFinset _ _ _).mp (nb (mem_erase.mpr ⟨vwi.symm,wi⟩))
  have s : ({u,v,w}:Finset V)⊆I := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact ui
    · exact vi
    · exact wi
  have ident := eq_of_subset_of_card_le s (by rw [i3]; simp [uvi,uwi,vwi])
  exact finish ue fw (ident ▸ RouteOn.three vu.symm vw uwi)

#print axioms six_port_two_inner_route
#print axioms six_port_three_inner_route
end Graffiti189LongestPath.CrossSaturation
