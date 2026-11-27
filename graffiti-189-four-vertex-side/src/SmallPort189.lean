import PortRotation189
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.TwoCut.PortRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

def HighAt (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (x : V) : Prop :=
  (if x∈P then 3 else 4) ≤ G.degree x

private theorem high_ge_three {P : Finset V} {x : V} (hi : HighAt G P x) :
    3≤G.degree x := by unfold HighAt at hi; split at hi <;> omega

private theorem high_nonport_ge_four {P : Finset V} {x : V} (np : x∉P) (hi : HighAt G P x) :
    4≤G.degree x := by simpa [HighAt,np] using hi

private theorem cover_from_high_terminal (P : Finset V) (pnon : P.Nonempty)
    (atmostone : ∀ x y : V, x≠y → HighAt G P x ∨ HighAt G P y)
    (pos : ∀ x, 1≤G.degree x)
    (nonport : ∀ x∉P, 2≤G.degree x) :
    ∃ s t : V, ∃ p : G.Walk s t, MaxFrom P p ∧ HighAt G P t := by
  obtain ⟨s,t,p,hp⟩ := exists_max (G:=G) P pnon
  by_cases high : HighAt G P t
  · exact ⟨s,t,p,hp,high⟩
  by_cases tp : t∈P
  · have st : s≠t := by
      intro eq
      subst t
      have pi := (isPath_iff_eq_nil p).mp hp.2.1
      have ge := (pos s)
      have pc : 0<(G.neighborFinset s).card := by rw [card_neighborFinset_eq_degree]; omega
      obtain ⟨x,xn⟩ := card_pos.mp pc
      have xt := terminal_closed hp ((mem_neighborFinset G s x).mp xn)
      rw [pi,mem_support_nil_iff] at xt
      exact ((mem_neighborFinset G s x).mp xn).ne xt.symm
    refine ⟨t,s,p.reverse,⟨tp,hp.2.1.reverse,?_⟩,(atmostone s t st).resolve_right high⟩
    intro u hu v q hq
    simpa only [length_reverse] using hp.2.2 u hu v q hq
  · obtain ⟨R,_,_,rc,rot⟩ := rotated_set hp
    have c := nonport t tp
    obtain ⟨x,xr,y,yr,xy⟩ := one_lt_card.mp (show 1<R.card by omega)
    rcases atmostone x y xy with high|high
    · obtain ⟨q,hq,_⟩ := rot x xr
      exact ⟨s,x,q,hq,high⟩
    · obtain ⟨q,hq,_⟩ := rot y yr
      exact ⟨s,y,q,hq,high⟩

private theorem neighbor_bound {x : V} (C : Finset V) (off : x∉C)
    (not_adj : ∀ z∈C, ¬G.Adj x z) :
    G.degree x + C.card + 1 ≤ Fintype.card V := by
  let D := insert x C
  have dis : Disjoint (G.neighborFinset x) D := disjoint_left.mpr (by
    intro z hz zd
    have xz := (mem_neighborFinset G x z).mp hz
    rcases mem_insert.mp zd with rfl|zc
    · exact xz.ne rfl
    · exact not_adj z zc xz)
  have cb := card_le_univ (G.neighborFinset x ∪ D)
  rw [card_union_of_disjoint dis,card_neighborFinset_eq_degree,
    show D=insert x C from rfl,card_insert_of_not_mem off] at cb
  omega

/-- A graph of order at most six, under the internal degree bounds arising
at a distance-three cut, has a spanning path starting at a porter. -/
theorem spanning_path_from_port_of_six (P : Finset V) (ports : 2≤P.card)
    (small : Fintype.card V≤6)
    (atmostone : ∀ x y : V, x≠y → HighAt G P x ∨ HighAt G P y)
    (pos : ∀ x, 1≤G.degree x)
    (nonport : ∀ x∉P, 2≤G.degree x) :
    ∃ s∈P, ∃ t : V, ∃ p : G.Walk s t, p.IsPath ∧ ∀ x,x∈p.support := by
  classical
  let Goal := ∃ s∈P, ∃ t : V, ∃ p : G.Walk s t, p.IsPath ∧ ∀ x,x∈p.support
  change Goal
  by_cases yes : Goal
  · exact yes
  exfalso
  have Pne : P.Nonempty := card_pos.mp (by omega)
  obtain ⟨s,t,p,hp,tHigh⟩ := cover_from_high_terminal P Pne atmostone pos nonport
  obtain ⟨R,Rsub,sR,rc,rot⟩ := rotated_set hp
  have rg : 3≤R.card := by rw [rc]; exact high_ge_three tHigh
  obtain ⟨y,yo⟩ : ∃ x,x∉p.support := not_forall.mp (fun all => yes ⟨s,hp.1,t,p,hp.2.1,all⟩)
  have omitted_low {x : V} (xo : x∉p.support) : ¬HighAt G P x := by
    intro hi
    have no : x∉R := fun e => xo (List.mem_toFinset.mp (Rsub e))
    have b := neighbor_bound R no (fun z zr => omitted_avoids_rotated rot xo zr)
    have a := high_ge_three hi
    omega
  have sole {x : V} (xo : x∉p.support) : x=y :=
    Classical.byContradiction (fun e => (atmostone x y e).elim (omitted_low xo) (omitted_low yo))
  have ylow := omitted_low yo
  have highin {x : V} (hx : x∈p.support) : HighAt G P x :=
    (atmostone y x (fun e => yo (e.symm ▸ hx))).resolve_left ylow
  have noR (z : V) (zr : z∈R) : ¬G.Adj y z := omitted_avoids_rotated rot yo zr
  have yR : y∉R := fun e => yo (List.mem_toFinset.mp (Rsub e))
  have ys : y≠s := fun e => yo (e.symm ▸ p.start_mem_support)
  have plen : p.length≤4 := by
    have cp := card_le_univ (insert y p.support.toFinset)
    rw [card_insert_of_not_mem (fun h => yo (List.mem_toFinset.mp h)),
      List.toFinset_card_of_nodup hp.2.1.support_nodup,length_support] at cp
    omega
  have four_sub_full {R' : Finset V} (sub : R'⊆p.support.toFinset) (off : s∉R')
      (four : 4≤R'.card) :
      ∀ z∈p.support, z=s ∨ z∈R' := by
    intro z zp
    have sub' : insert s R'⊆p.support.toFinset := by
      intro x e
      rcases mem_insert.mp e with rfl|e
      · exact List.mem_toFinset.mpr p.start_mem_support
      · exact sub e
    have eq : insert s R'=p.support.toFinset := eq_of_subset_of_card_le sub' (by
      rw [card_insert_of_not_mem off,List.toFinset_card_of_nodup hp.2.1.support_nodup,length_support]
      omega)
    exact mem_insert.mp (eq ▸ List.mem_toFinset.mpr zp)
  have rotates_to_four {x : V} (xr : x∈R) (nport : x∉P) :
      ∃ R' : Finset V, R'⊆p.support.toFinset ∧ s∉R' ∧ 4≤R'.card ∧
        ∀ z∈R', ∃ q : G.Walk s z, MaxFrom P q ∧ (∀ u,u∈q.support ↔ u∈p.support) := by
    obtain ⟨q,hq,same⟩ := rot x xr
    obtain ⟨R',sub,off,c,rot'⟩ := rotated_set hq
    have ge := high_nonport_ge_four nport (highin (List.mem_toFinset.mp (Rsub xr)))
    refine ⟨R',fun z hz => List.mem_toFinset.mpr ((same _).mp (List.mem_toFinset.mp (sub hz))),
      off,by omega,?_⟩
    intro z hz
    obtain ⟨r,hr,hs⟩ := rot' z hz
    exact ⟨r,hr,fun u => (hs u).trans (same u)⟩
  have spanning_append {q : V} {w : G.Walk s q} (hw : w.IsPath)
      (same : ∀ u,u∈w.support ↔ u∈p.support) (adj : G.Adj y s) :
      (Walk.cons adj w).IsPath ∧ ∀ x,x∈(Walk.cons adj w).support := by
    refine ⟨hw.cons (fun h => yo ((same _).mp h)),?_⟩
    intro x
    by_cases xin : x∈p.support
    · simp [support_cons,(same _).mpr xin]
    · simp [sole xin]
  by_cases ed : G.Adj y s
  · by_cases yp : y∈P
    · obtain ⟨hw,hs⟩ := spanning_append hp.2.1 (fun _ => Iff.rfl) ed
      exact yes ⟨y,yp,t,Walk.cons ed p,hw,hs⟩
    have some_port : ∃ z∈P, ∃ q : G.Walk s z, MaxFrom P q ∧ (∀ u,u∈q.support↔u∈p.support) := by
      by_cases bad : ∃ x∈R,x∉P
      · obtain ⟨x,xr,np⟩ := bad
        obtain ⟨R',sub,off,four,rot'⟩ := rotates_to_four xr np
        have ex : ∃ z∈P,z≠s := by
          have ca := card_erase_of_mem hp.1
          obtain ⟨z,e⟩ := card_pos.mp (show 0<(P.erase s).card by omega)
          exact ⟨z,(mem_erase.mp e).2,(mem_erase.mp e).1⟩
        obtain ⟨z,zp,zs⟩ := ex
        have zin : z∈p.support := Classical.byContradiction (fun h => yp (sole h ▸ zp))
        have zr := (four_sub_full sub off four z zin).resolve_left zs
        exact ⟨z,zp,rot' z zr⟩
      · obtain ⟨z,zr⟩ := card_pos.mp (show 0<R.card by omega)
        exact ⟨z,Classical.byContradiction (fun h => bad ⟨z,zr,h⟩),rot z zr⟩
    obtain ⟨z,zp,q,hq,same⟩ := some_port
    obtain ⟨hw,hs⟩ := spanning_append hq.2.1 same ed
    exact yes ⟨z,zp,y,(Walk.cons ed q).reverse,hw.reverse,fun x => by rw [support_reverse]; exact List.mem_reverse.mpr (hs x)⟩
  have dp : G.degree y≤1 := by
    have hc := neighbor_bound (x:=y) (insert s R) (by simp [ys,yR]) (by
      intro z h
      rcases mem_insert.mp h with rfl|hr
      · exact ed
      · exact noR _ hr)
    rw [card_insert_of_not_mem sR] at hc
    omega
  have yp : y∈P := Classical.byContradiction (fun np => by have q := nonport y np; omega)
  obtain ⟨z,zy⟩ := card_pos.mp (show 0<(G.neighborFinset y).card by
    rw [card_neighborFinset_eq_degree]
    have h := pos y
    omega)
  have yz := (mem_neighborFinset G y z).mp zy
  have zin : z∈p.support := Classical.byContradiction (fun h => yz.ne (sole h).symm)
  have sh : 3≤G.degree s := high_ge_three (highin p.start_mem_support)
  have th : 3≤G.degree t := high_ge_three tHigh
  have sinside (u : V) (su : G.Adj s u) : u∈p.support :=
    Classical.byContradiction (fun off => ed (sole off ▸ su.symm))
  obtain ⟨v,q,hq,close,qs⟩ := close_path_from_degrees hp.2.1 sinside
    (fun _ e => terminal_closed hp e) (by omega)
  obtain ⟨u,r,hr,_,rs⟩ := reroot_closed_path hq close ((qs _).mpr zin)
  have rno : y∉r.support := fun e => yo ((qs _).mp ((rs _).mp e))
  refine yes ⟨y,yp,u,.cons yz r,hr.cons rno,?_⟩
  intro x
  by_cases xin : x∈p.support
  · simp [support_cons,(rs _).mpr ((qs _).mpr xin)]
  · simp [sole xin]

#print axioms spanning_path_from_port_of_six
end Graffiti189LongestPath.TwoCut
