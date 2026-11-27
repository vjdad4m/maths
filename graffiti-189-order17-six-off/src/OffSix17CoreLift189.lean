import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin reverse_long from SmallOrderFour189
open private length_ten_two_pin_shape omitted_degree_component_bound two_pin_flanks_path_only
    two_pin_universal_in_omitted_component from FourOffGraphSupport189
open private two_pins_choose_ordered from FourOffGraphCore189

private theorem offSix_walk_of_chain (a : V) (L : List V)
    (cl : List.Chain' G.Adj (a::L)) : ∃ b,∃ q : G.Walk a b,q.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,q,eq⟩ := ih b cl.tail
    exact ⟨c,.cons cl.rel_head q,by simp [eq]⟩

private theorem range_path_chain {a b : V} (p : G.Walk a b)
    (s t : ℕ) (bound : s+t≤p.length+1) :
    List.Chain' G.Adj ((List.range' s t).map p.getVert) := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    cases t with
    | zero => simp
    | succ t =>
      rw [List.range'_succ, List.range'_succ]
      simp only [List.map_cons,List.chain'_cons]
      exact ⟨p.adj_getVert_succ (by omega), ih (s+1) (by omega)⟩

private theorem range_path_head {a b : V} (p : G.Walk a b) (s t : ℕ) (pos : 0<t) :
    ((List.range' s t).map p.getVert).head?=some (p.getVert s) := by
  cases t with
  | zero => omega
  | succ n => simp [List.range'_succ]

/-- A path through omitted vertices connecting two sites extends the spine
if its edge count is at least the smaller site index. -/
theorem no_longest_with_long_omitted_path_between_sites
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (q : G.Walk x y) (qp : q.IsPath)
    (off : ∀ z∈q.support,z∉p.support)
    {i j : ℕ} (lo : i<j) (hi : j≤p.length) (enough : i≤q.length)
    (left : G.Adj x (p.getVert i)) (right : G.Adj y (p.getVert j)) : False := by
  classical
  let I := List.range' i (j-i)
  let J := List.range' j (p.length+1-j)
  let A := (I.map p.getVert).reverse
  let B := J.map p.getVert
  have ir (k : ℕ) (im : k∈I) : i≤k ∧ k<j := by
    have q := List.mem_range'_1.mp im
    omega
  have jr (i : ℕ) (im : i∈J) : j≤i ∧ i≤p.length := by
    have q := List.mem_range'_1.mp im
    omega
  have ndA : A.Nodup := List.nodup_reverse.mpr (List.Nodup.map_on
    (fun u um v vm e => hp.1.getVert_injOn (show u≤p.length by have q := ir u um; omega)
      (show v≤p.length by have q := ir v vm; omega) e)
    (List.nodup_range' (s:=i) (n:=j-i)))
  have ndB : B.Nodup := List.Nodup.map_on
    (fun u um v vm e => hp.1.getVert_injOn (jr u um).2 (jr v vm).2 e)
    (List.nodup_range' (s:=j) (n:=p.length+1-j))
  have ima (z : V) (zm : z∈A) : ∃ i∈I,p.getVert i=z := List.mem_map.mp (List.mem_reverse.mp zm)
  have imb (z : V) (zm : z∈B) : ∃ i∈J,p.getVert i=z := List.mem_map.mp zm
  have onA {z : V} (zm : z∈A) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := ima z zm
    exact p.getVert_mem_support i
  have onB {z : V} (zm : z∈B) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := imb z zm
    exact p.getVert_mem_support i
  have ab : A.Disjoint B := by
    intro z zm zn
    obtain ⟨i,im,ie⟩ := ima _ zm
    obtain ⟨k,km,ke⟩ := imb _ zn
    have il := ir i im
    have kl := jr k km
    have e := hp.1.getVert_injOn (show i≤p.length by omega) kl.2 (ie.trans ke.symm)
    omega
  have da : A.Disjoint q.support := fun _ h r=>off _ r (onA h)
  have db : q.support.Disjoint B := fun _ h r=>off _ h (onB r)
  have nd : ((A++q.support)++B).Nodup := by
    refine (ndA.append qp.support_nodup da).append ndB ?_
    intro z zm zn
    exact (List.mem_append.mp zm).elim (fun h=>ab h zn) (fun h=>db h zn)
  have ca : List.Chain' G.Adj A := List.chain'_reverse.mpr
    ((range_path_chain p i (j-i) (by omega)).imp (fun u v h=>h.symm))
  have cb : List.Chain' G.Adj B := range_path_chain p j (p.length+1-j) (by omega)
  have headA : A.getLast?=some (p.getVert i) := by
    simp only [A,List.getLast?_reverse]
    exact range_path_head p i (j-i) (by omega)
  have headB : B.head?=some (p.getVert j) := range_path_head p j (p.length+1-j) (by omega)
  have ca' : List.Chain' G.Adj (A++q.support) := ca.append q.chain'_adj_support (by
    intro u um v vm
    have u1 : p.getVert i=u := by simpa [headA] using um
    have first : q.support.head?=some x := by cases q <;> rfl
    have r : x=v := by simpa [first] using vm
    subst u
    subst v
    exact left.symm)
  have last : (A++q.support).getLast?=some y := by
    rw [List.getLast?_append, List.getLast?_eq_getLast q.support_ne_nil]
    simp [q.getLast_support]
  have cl : List.Chain' G.Adj ((A++q.support)++B) := ca'.append cb (by
    intro u um v vm
    have q : y=u := by simpa [last] using um
    have r : p.getVert j=v := by simpa [headB] using vm
    subst u
    subst v
    exact right)
  let L := (A++q.support)++B
  have ln : L.length+i=p.length+q.length+2 := by simp [L,A,B,I,J,length_support]; omega
  change List.Chain' G.Adj L at cl
  cases e : L with
  | nil => simp [e] at ln; omega
  | cons r R =>
    obtain ⟨s,qqq,su⟩ := offSix_walk_of_chain r R (e ▸ cl)
    have qq : qqq.IsPath := IsPath.mk' (su.symm ▸ (e ▸ nd))
    have c := hp.2 _ _ qqq qq
    have d := congrArg List.length su
    rw [length_support,←e] at d
    omega


theorem no_longest_with_omitted_path_at_left_boundary
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (q : G.Walk x y) (qp : q.IsPath) (qpos : 0<q.length)
    (off : ∀ z∈q.support,z∉p.support)
    {j : ℕ} (lo : 2≤j) (hi : j≤p.length)
    (left : G.Adj x (p.getVert 1)) (right : G.Adj y (p.getVert j)) : False :=
  no_longest_with_long_omitted_path_between_sites hp q qp off (by omega) hi (by omega) left right

theorem no_longest_with_shared_left_boundary_pair
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yo : y∉p.support) (xy : G.Adj x y)
    {j : ℕ} (lo : 2≤j) (hi : j≤p.length)
    (left : G.Adj x (p.getVert 1)) (right : G.Adj y (p.getVert j)) : False := by
  let q : G.Walk x y := .cons xy .nil
  have qp : q.IsPath := by
    apply IsPath.mk'
    simp [q,xy.ne]
  have qpos : 0<q.length := by simp [q]
  have safe (z : V) (zs : z∈q.support) : z∉p.support := by
    have ze : z=x ∨ z=y := by simpa [q] using zs
    rcases ze with rfl|rfl
    · exact xo
    · exact yo
  exact no_longest_with_omitted_path_at_left_boundary hp q qp qpos safe lo hi left right

#print axioms no_longest_with_long_omitted_path_between_sites
#print axioms no_longest_with_omitted_path_at_left_boundary
#print axioms no_longest_with_shared_left_boundary_pair

/-- A nontrivial omitted component cannot contain a double-pin vertex
on a high-ended edge-optimal length-ten path. -/
theorem single_pins_in_nontrivial_length_ten_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (H : OmittedComponent p) (large : 2≤H.vertices.card)
    {x : V} (xh : x∈H.vertices) : (Pins p x).card≤1 := by
  classical
  apply Nat.le_of_not_gt
  intro x2
  have xo := H.off _ xh
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered x2
  obtain ⟨path_only,sub⟩ := two_pin_flanks_path_only hc even conn degree hp ah bh xo xi xj ij
  have share {y : V} (yh : y∈H.vertices) (yx : y≠x) {k : ℕ} (yk : k∈Pins p y) : False := by
    have yo := H.off _ yh
    have adj := two_pin_universal_in_omitted_component hc H xh path_only y yh yx
    have kp := sub y yo adj yk
    have eq : k=i ∨ k=j := by simpa using kp
    have jlen := (pin_data xj).1
    rcases (length_ten_two_pin_shape hc even conn degree hp ah bh len xo xi xj ij).1 with rfl|hj
    · rcases eq with rfl|rfl
      · exact no_longest_with_shared_left_boundary_pair hp.1 yo xo adj.symm (by omega) jlen.le
          (pin_data yk).2 (pin_data xj).2
      · exact no_longest_with_shared_left_boundary_pair hp.1 xo yo adj (by omega) jlen.le
          (pin_data xi).2 (pin_data yk).2
    · have i1 := pin_pos hp.1 xo xi
      have xr : 1∈Pins p.reverse x := by
        simpa only [show p.length-j=1 by omega] using reverse_pin hp.1 xo xj
      have xf : p.length-i∈Pins p.reverse x := reverse_pin hp.1 xo xi
      have hl := (pin_data xf).1
      rw [length_reverse] at hl
      rcases eq with ki|kj
      · subst k
        have yf : p.length-i∈Pins p.reverse y := reverse_pin hp.1 yo yk
        exact no_longest_with_shared_left_boundary_pair (reverse_long hp.1)
          (by simpa using xo) (by simpa using yo) adj (by omega) (by rw [length_reverse]; exact hl.le)
          (pin_data xr).2 (pin_data yf).2
      · subst k
        have yr : 1∈Pins p.reverse y := by
          simpa only [show p.length-j=1 by omega] using reverse_pin hp.1 yo yk
        exact no_longest_with_shared_left_boundary_pair (reverse_long hp.1)
          (by simpa using yo) (by simpa using xo) adj.symm (by omega) (by rw [length_reverse]; exact hl.le)
          (pin_data yr).2 (pin_data xf).2
  let S : Finset V := {x}
  let U := ((↑S : Set V)ᶜ)
  have cut := conn S (by simp [S])
  have ec := card_erase_of_mem xh
  obtain ⟨y,yr⟩ := card_pos.mp (show 0<(H.vertices.erase x).card by omega)
  obtain ⟨yx,yh⟩ := mem_erase.mp yr
  have ax : a≠x := fun e=>xo (e ▸ p.start_mem_support)
  let ys : U := ⟨y,by simp [U,S,yx]⟩
  let as : U := ⟨a,by simp [U,S,ax]⟩
  obtain ⟨q⟩ := cut.preconnected ys as
  have localStep {u v : U} (hu : u.val∈H.vertices) (e : (G.induce U).Adj u v) :
      v.val∈H.vertices := by
    by_cases vy : v.val∈H.vertices
    · exact vy
    exfalso
    have vs := H.closed _ hu _ vy (show G.Adj u.val v.val from e)
    obtain ⟨k,kp,_⟩ := pin_of_neighbor_mem hp.1 (H.off _ hu) vs e
    exact share hu (by simpa [U,S] using u.property) kp
  have prop {u v : U} (q : (G.induce U).Walk u v) : u.val∈H.vertices → v.val∈H.vertices := by
    induction q with
    | nil => exact id
    | cons e q ih => exact fun h=>ih (localStep h e)
  exact H.off _ (prop q yh) p.start_mem_support

/-- Three omitted vertices in one component would force two double-pin
vertices. Thus such a component cannot occur for a length-ten optimum. -/
theorem no_length_ten_with_three_vertex_omitted_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (H : OmittedComponent p) (h3 : H.vertices.card=3) : False := by
  classical
  obtain ⟨u,uh,v,vh,uv⟩ := one_lt_card.mp (show 1<H.vertices.card by omega)
  obtain ⟨x,xh,xd⟩ : ∃ x∈H.vertices,4≤G.degree x := (degree u v uv).elim
    (fun h=>⟨u,uh,h⟩) (fun h=>⟨v,vh,h⟩)
  have xbd := omitted_degree_component_bound hp.1 H xh
  have xone := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H
    (by omega) xh
  omega

/-- A disconnected omitted graph on six vertices has one five-vertex
component and a single isolated omitted vertex. -/
theorem disconnected_six_omissions_at_length_ten
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (off : ((univ : Finset V)\p.support.toFinset).card=6)
    (disc : ¬∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices) :
    ∃ (H : OmittedComponent p) (x : V), H.vertices.card=5 ∧
      x∉p.support ∧ x∉H.vertices ∧
      (∀ z∉p.support,z=x ∨ z∈H.vertices) ∧
      (∀ z∉p.support,¬G.Adj x z) ∧ (∀ z∈H.vertices,4≤G.degree z) := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have oc : O.card=6 := off
  have few (z : V) (zo : z∉p.support) :=
    (at_most_two_pins_one_slack hc 2 (by decide) (fun v=>distanceTwo_le_of_even 4 v (even v))
      conn degree hp zo).1
  obtain ⟨u,uo,v,vo,uv⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨w,wo,wd⟩ : ∃ w∈O,4≤G.degree w := (degree u v uv).elim
    (fun h=>⟨u,uo,h⟩) (fun h=>⟨v,vo,h⟩)
  obtain ⟨S,wh,sne,soff,sclosed,sjoined⟩ := exists_omitted_component (out.mp wo)
  let H : OmittedComponent p := ⟨S,sne,soff,sclosed,sjoined⟩
  have Hsub : H.vertices⊆O := fun z hz=>out.mpr (H.off z hz)
  have large : 4≤H.vertices.card := by
    have d := omitted_degree_component_bound hp.1 H wh
    have f := few w (out.mp wo)
    have n : H.vertices.card≠3 :=
      no_length_ten_with_three_vertex_omitted_component hc even conn degree hp ah bh len H
    omega
  let R := O\H.vertices
  have rCard : R.card+H.vertices.card=O.card := card_sdiff_add_card_eq_card Hsub
  have low (z : V) (zr : z∈R) : ¬4≤G.degree z := by
    have zo := out.mp (mem_sdiff.mp zr).1
    have zh := (mem_sdiff.mp zr).2
    obtain ⟨T,zT,tne,toff,tclosed,tjoined⟩ := exists_omitted_component zo
    let J : OmittedComponent p := ⟨T,tne,toff,tclosed,tjoined⟩
    have Jsub : J.vertices⊆R := by
      intro y ym
      refine mem_sdiff.mpr ⟨out.mpr (J.off y ym),?_⟩
      intro yh
      obtain ⟨q,_,stay⟩ := J.joined y ym z zT
      have propagate {u v : V} (r : G.Walk u v) (onJ : ∀ t∈r.support,t∈J.vertices) :
          u∈H.vertices → v∈H.vertices := by
        induction r with
        | nil => exact id
        | @cons a b c ab r ih =>
          intro ah
          have bh : b∈H.vertices := Classical.byContradiction (fun no=>
            J.off b (onJ b (by simp [r.start_mem_support])) (H.closed a ah b no ab))
          exact ih (fun t tm=>onJ t (by simp [tm])) bh
      exact zh (propagate q stay yh)
    have bd := omitted_degree_component_bound hp.1 J zT
    have f := few z zo
    have k := card_le_card Jsub
    omega
  have singleton : R.card≤1 := by
    apply Nat.le_of_not_gt
    intro more
    obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp more
    exact (degree u v uv).elim (low u ur) (low v vr)
  obtain ⟨x,xo,xh⟩ : ∃ x∉p.support,x∉H.vertices := by
    by_cases q : ∃ x∉p.support,x∉H.vertices
    · exact q
    exact False.elim (disc ⟨H,fun z zo=>Classical.byContradiction (fun zh=>q ⟨z,zo,zh⟩)⟩)
  have xr : x∈R := mem_sdiff.mpr ⟨out.mpr xo,xh⟩
  have rpos := card_pos.mpr ⟨x,xr⟩
  have only {v : V} (vr : v∈R) : v=x := by
    exact Classical.byContradiction (fun ne=> (Nat.not_lt_of_ge singleton) (one_lt_card.mpr ⟨v,vr,x,xr,ne⟩))
  refine ⟨H,x,by omega,xo,xh,?_,?_,?_⟩
  · intro v vo
    by_cases vh : v∈H.vertices
    · exact .inr vh
    · exact .inl (only (mem_sdiff.mpr ⟨out.mpr vo,vh⟩))
  · intro v vo e
    by_cases vh : v∈H.vertices
    · exact xo (H.closed v vh x xh e.symm)
    · exact e.ne (only (mem_sdiff.mpr ⟨out.mpr vo,vh⟩)).symm
  · intro v vh
    exact (degree v x (fun e=>xh (e ▸ vh))).resolve_right (low x xr)

#print axioms single_pins_in_nontrivial_length_ten_component
#print axioms no_length_ten_with_three_vertex_omitted_component
#print axioms disconnected_six_omissions_at_length_ten


/-- Nontrivial omitted components at length ten attach only at interior
sites 2 through 8. A boundary carrier and any carrier of a different
site would permit the omitted-component splice. -/
theorem no_boundary_pin_in_nontrivial_length_ten_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (H : OmittedComponent p) (large : 2≤H.vertices.card)
    {x : V} (xh : x∈H.vertices) {i : ℕ} (xi : i∈Pins p x) : 2≤i ∧ i≤8 := by
  classical
  have nl := (pin_data xi).1
  have xo := H.off _ xh
  have ip := pin_pos hp.1 xo xi
  by_contra! alt
  have eq : i=1 ∨ i=9 := by omega
  have pc := componentPins_card hp.1 H 2 conn
  have pi : p.getVert i∈componentPins H := mem_filter.mpr
    ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),x,xh,(pin_data xi).2⟩
  have pe := card_erase_of_mem pi
  obtain ⟨v,ve⟩ := card_pos.mp (show 0<((componentPins H).erase (p.getVert i)).card by omega)
  obtain ⟨vne,vm⟩ := mem_erase.mp ve
  obtain ⟨vp,y,yh,yv⟩ := mem_filter.mp vm
  have yo := H.off _ yh
  obtain ⟨j,yj,jv⟩ := pin_of_neighbor_mem hp.1 yo (List.mem_toFinset.mp vp) yv
  have jn := (pin_data yj).1
  have jp := pin_pos hp.1 yo yj
  have ij : i≠j := fun e=>vne (jv.symm.trans (congrArg p.getVert e.symm))
  have xy : x≠y := by
    intro e
    subst y
    have one := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H large xh
    exact (Nat.not_lt_of_ge one) (one_lt_card.mpr ⟨i,xi,j,yj,ij⟩)
  obtain ⟨q,_,stay⟩ := H.joined x xh y yh
  let Q : G.Walk x y := q.toPath
  have qpath : Q.IsPath := q.toPath.property
  have qpos : 0<Q.length := Nat.pos_of_ne_zero (fun e=>xy (Q.eq_of_length_eq_zero e))
  have safe (v : V) (vv : v∈Q.support) : v∉p.support := H.off _ (stay _ (q.support_toPath_subset vv))
  rcases eq with rfl|i9
  · exact no_longest_with_omitted_path_at_left_boundary hp.1 Q qpath qpos safe (by omega) jn.le
      (pin_data xi).2 (pin_data yj).2
  · have xr : 1∈Pins p.reverse x := by
      simpa only [show p.length-i=1 by omega] using reverse_pin hp.1 xo xi
    have yr : p.length-j∈Pins p.reverse y := reverse_pin hp.1 yo yj
    have bound := (pin_data yr).1
    rw [length_reverse] at bound
    exact no_longest_with_omitted_path_at_left_boundary (reverse_long hp.1) Q qpath qpos
      (fun v vv=>by simpa [support_reverse] using safe v vv)
      (by omega) (by rw [length_reverse]; exact bound.le) (pin_data xr).2 (pin_data yr).2

#print axioms no_boundary_pin_in_nontrivial_length_ten_component


open private omittedDegree_eq omittedNeighbors from FourOffGraphCore189
open private dist_two mem_distanceTwo from SmallOrderFour189

private theorem omitted_neighbors_eq_component_neighbors
    {a b x : V} {p : G.Walk a b} (H : OmittedComponent p) (hx : x∈H.vertices) :
    omittedNeighbors p x=G.neighborFinset x∩H.vertices := by
  classical
  ext z
  simp only [omittedNeighbors,mem_filter,mem_inter,mem_neighborFinset]
  exact ⟨fun ⟨e,off⟩=>⟨e,Classical.byContradiction (fun hz=>off (H.closed x hx z hz e))⟩,
    fun ⟨e,mem⟩=>⟨e,H.off z mem⟩⟩

/-- At length ten a single-pin carrier cannot be a leaf of the omitted
component with a neighbor carrying another pin. -/
theorem no_foreign_pin_at_omitted_leaf_neighbor
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (H : OmittedComponent p)
    {x y : V} (xh : x∈H.vertices) (yh : y∈H.vertices)
    {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (ij : i≠j)
    (leaf : G.neighborFinset x∩H.vertices={y}) : False := by
  classical
  have xy : G.Adj x y := by
    have m : y∈G.neighborFinset x∩H.vertices := by rw [leaf]; simp
    exact (mem_neighborFinset G _ _).mp (mem_inter.mp m).1
  have large : 2≤H.vertices.card := one_lt_card.mpr ⟨x,xh,y,yh,xy.ne⟩
  have xs := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H large xh
  have ys := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H large yh
  have xd := omittedDegree_eq hp.1 (H.off _ xh)
  rw [omitted_neighbors_eq_component_neighbors H xh,leaf,card_singleton] at xd
  have yd : 4≤G.degree y := (degree x y xy.ne).resolve_left (by omega)
  have ydeg := omittedDegree_eq hp.1 (H.off _ yh)
  rw [omitted_neighbors_eq_component_neighbors H yh] at ydeg
  let T := G.neighborFinset y∩H.vertices
  have xT : x∈T := mem_inter.mpr ⟨(mem_neighborFinset G _ _).mpr xy.symm,xh⟩
  have t3 : 3≤T.card := by change 3≤(G.neighborFinset y∩H.vertices).card; omega
  have c := card_erase_of_mem xT
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<(T.erase x).card by omega)
  let P : Finset ℕ := {i-1,i+1,j}
  have ib := (pin_data xi).1
  have jb := (pin_data yj).1
  have il := pin_pos hp.1 (H.off _ xh) xi
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ij with h|h
    · exact .inl (component_pins_spaced_four hc even conn degree hp ah bh H xh yh xi yj h)
    · exact .inr (component_pins_spaced_four hc even conn degree hp ah bh H yh xh yj xi h)
  have pr {k : ℕ} (m : k∈P) : k≤p.length := by
    have a : k=i-1 ∨ k=i+1 ∨ k=j := by simpa [P] using m
    rcases a with rfl|rfl|rfl <;> omega
  have pc : P.card=3 := by
    have a : i-1∉({i+1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have b : i+1∉({j}:Finset ℕ) := by simp only [mem_singleton]; omega
    rw [show P={i-1,i+1,j} from rfl,card_insert_of_not_mem a,card_insert_of_not_mem b,card_singleton]
  have ic : (P.image p.getVert).card=3 := by
    rw [card_image_iff.mpr (fun _ u _ v e=>hp.1.1.getVert_injOn (pr u) (pr v) e),pc]
  have dos {w : V} (wm : w∈T.erase x) : w∈DistanceTwo G x := by
    obtain ⟨wx,wt⟩ := mem_erase.mp wm
    obtain ⟨wn,wh⟩ := mem_inter.mp wt
    have yw := (mem_neighborFinset G _ _).mp wn
    have na : ¬G.Adj x w := by
      intro adj
      have qm := mem_inter.mpr ⟨(mem_neighborFinset G _ _).mpr adj,wh⟩
      rw [leaf] at qm
      exact yw.ne (mem_singleton.mp qm).symm
    exact mem_distanceTwo.mpr (dist_two hc wx.symm na xy yw)
  have dp : P.image p.getVert⊆DistanceTwo G x := by
    intro z zm
    obtain ⟨k,km,rfl⟩ := mem_image.mp zm
    have ne : k=i-1 ∨ k=i+1 ∨ k=j := by simpa [P] using km
    rcases ne with km|kp|kJ
    · subst k
      exact (mem_sdiff.mp (flanks_outside_boundary hc hp.1 (H.off _ xh)
        (mem_image.mpr ⟨i-1,mem_union.mpr (.inl (mem_image.mpr ⟨i,xi,rfl⟩)),rfl⟩))).1
    · subst k
      exact (mem_sdiff.mp (flanks_outside_boundary hc hp.1 (H.off _ xh)
        (mem_image.mpr ⟨i+1,mem_union.mpr (.inr (mem_image.mpr ⟨i,xi,rfl⟩)),rfl⟩))).1
    · subst k
      have na : ¬G.Adj x (p.getVert j) := by
        intro e
        have jx : j∈Pins p x := mem_filter.mpr ⟨mem_range.mpr jb,e⟩
        exact (Nat.not_lt_of_ge xs) (one_lt_card.mpr ⟨i,xi,j,jx,ij⟩)
      exact mem_distanceTwo.mpr (dist_two hc (fun e=>(H.off _ xh) (e ▸ p.getVert_mem_support j))
        na xy (pin_data yj).2)
  have pair : ({u,v}:Finset V)⊆DistanceTwo G x := insert_subset (dos um) (singleton_subset_iff.mpr (dos vm))
  have dj : Disjoint (P.image p.getVert) ({u,v}:Finset V) := disjoint_left.mpr (by
    intro w wp ws
    obtain ⟨k,_,rfl⟩ := mem_image.mp wp
    have all : ({u,v}:Finset V)⊆H.vertices := insert_subset
      (mem_inter.mp (mem_erase.mp um).2).2 (singleton_subset_iff.mpr (mem_inter.mp (mem_erase.mp vm).2).2)
    exact (H.off _ (all ws)) (p.getVert_mem_support k))
  have D := card_le_card (union_subset dp pair)
  rw [card_union_of_disjoint dj,ic,show ({u,v}:Finset V).card=2 by simp [uv]] at D
  have cap := distanceTwo_le_of_even 4 x (even x)
  omega

#print axioms no_foreign_pin_at_omitted_leaf_neighbor


/-- The six-vertex marked-path lemma, supplied abstractly, lifts to any
connected omitted component of size six. No mark or endpoint table is used. -/
theorem no_length_ten_with_large_omitted_component_of_core_paths
    (core : ∀ {W : Type u} (D : SimpleGraph W) [Fintype W] [DecidableEq W]
      [DecidableRel D.Adj], Fintype.card W=6 → (∀ w,1≤D.degree w) →
      (∀ s t,s≠t → 3≤D.degree s ∨ 3≤D.degree t) →
      ∀ {s t},s≠t →
      (∃ q : D.Walk s t,q.IsPath ∧ 3≤q.length) ∨
        D.neighborFinset s={t} ∨ D.neighborFinset t={s})
    (core5 : ∀ {W : Type u} (D : SimpleGraph W) [Fintype W] [DecidableEq W]
      [DecidableRel D.Adj], Fintype.card W=5 → (∀ w,3≤D.degree w) →
      ∀ {s t},s≠t → ∃ q : D.Walk s t,q.IsPath ∧ 3≤q.length)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (H : OmittedComponent p)
    (hsize : H.vertices.card=5 ∨ H.vertices.card=6)
    (high5 : H.vertices.card=5 → ∀ z∈H.vertices,4≤G.degree z) : False := by
  classical
  let S : Set V := H.vertices
  let D := G.induce S
  let f : D →g G := ⟨Subtype.val, fun h=>h⟩
  have neigh (z : S) : (D.neighborFinset z).image Subtype.val=G.neighborFinset z.val∩H.vertices := by
    ext w
    simp only [mem_image,mem_neighborFinset,mem_inter]
    constructor
    · rintro ⟨r,e,rfl⟩
      exact ⟨show G.Adj z.val r.val from e,r.property⟩
    · rintro ⟨adj,hm⟩
      exact ⟨⟨w,hm⟩,adj,rfl⟩
  have dc (z : S) : D.degree z=(G.neighborFinset z.val∩H.vertices).card := by
    have e := congrArg Finset.card (neigh z)
    rwa [card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at e
  have bound (z : S) : 4≤G.degree z.val → 3≤D.degree z := by
    have d := omittedDegree_eq hp.1 (H.off _ z.property)
    rw [omitted_neighbors_eq_component_neighbors H z.property,←dc z] at d
    have one := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H
      (by omega) z.property
    omega
  have d3 (s t : S) (ne : s≠t) : 3≤D.degree s ∨ 3≤D.degree t :=
    (degree s.val t.val (fun e=>ne (Subtype.ext e))).imp (bound s) (bound t)
  have d1 (z : S) : 1≤D.degree z := by
    have n := card_erase_of_mem (show z.val∈H.vertices from z.property)
    obtain ⟨w,wm⟩ := card_pos.mp (show 0<(H.vertices.erase z.val).card by omega)
    obtain ⟨wz,wh⟩ := mem_erase.mp wm
    obtain ⟨q,_,stay⟩ := H.joined z.val z.property w wh
    obtain ⟨v,e,r,rfl⟩ := Walk.exists_eq_cons_of_ne wz.symm q
    have vh := stay v (by simp [r.start_mem_support])
    have vm : v∈G.neighborFinset z.val ∩ H.vertices :=
      mem_inter.mpr ⟨(mem_neighborFinset G _ _).mpr e,vh⟩
    rw [dc z]
    exact card_pos.mpr ⟨v,vm⟩
  have cardS : Fintype.card S=H.vertices.card := Fintype.card_coe H.vertices
  have np := componentPins_card hp.1 H 2 conn
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<(componentPins H).card by omega)
  obtain ⟨up,x,xh,xu⟩ := mem_filter.mp um
  obtain ⟨vp,y,yh,yv⟩ := mem_filter.mp vm
  have xo := H.off _ xh
  have yo := H.off _ yh
  obtain ⟨i,xi,iu⟩ := pin_of_neighbor_mem hp.1 xo (List.mem_toFinset.mp up) xu
  obtain ⟨j,yj,jv⟩ := pin_of_neighbor_mem hp.1 yo (List.mem_toFinset.mp vp) yv
  have ij : i≠j := fun e=>uv (iu.symm.trans ((congrArg p.getVert e).trans jv))
  have xy : x≠y := by
    intro e
    subst y
    have two := one_lt_card.mpr ⟨i,xi,j,yj,ij⟩
    have one := single_pins_in_nontrivial_length_ten_component hc even conn degree hp ah bh len H
      (by omega) xh
    omega
  let sx : S := ⟨x,xh⟩
  let sy : S := ⟨y,yh⟩
  have distinct : sx≠sy := fun e=>xy (congrArg Subtype.val e)
  have marked : (∃ q : D.Walk sx sy,q.IsPath ∧ 3≤q.length) ∨
      D.neighborFinset sx={sy} ∨ D.neighborFinset sy={sx} := by
    rcases hsize with c5|c6
    · exact .inl (core5 D (cardS.trans c5) (fun z=>bound z (high5 c5 _ z.property)) distinct)
    · exact core D (cardS.trans c6) d1 d3 distinct
  rcases marked with ⟨q,qp,ql⟩|lx|ly
  · let Q : G.Walk x y := q.map f
    have qp' : Q.IsPath := (q.map_isPath_iff_of_injective Subtype.val_injective).mpr qp
    have ql' : 3≤Q.length := by simpa [Q] using ql
    have safe (z : V) (m : z∈Q.support) : z∉p.support := by
      rw [show Q=q.map f from rfl,support_map] at m
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp m
      exact H.off _ w.property
    have extend {x y : V} (Q : G.Walk x y) (qp : Q.IsPath)
        (ql : 3≤Q.length) (xs : x∉p.support) (ys : y∉p.support)
        (safe : ∀ z∈Q.support,z∉p.support)
        {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (gap : i+3≤j) : False := by
      have ir := (pin_data xi).1
      have jr := (pin_data yj).1
      by_cases mode : i+j≤10
      · exact no_longest_with_long_omitted_path_between_sites hp.1 Q qp safe
          (by omega) jr.le (by omega) (pin_data xi).2 (pin_data yj).2
      have j' : p.length-j∈Pins p.reverse y := reverse_pin hp.1 ys yj
      have i' : p.length-i∈Pins p.reverse x := reverse_pin hp.1 xs xi
      have lenQ : 3≤Q.reverse.length := by simpa using ql
      exact no_longest_with_long_omitted_path_between_sites (reverse_long hp.1)
        Q.reverse qp.reverse (fun z zn=>by simpa [support_reverse] using safe z (by simpa using zn))
        (by omega) (pin_data i').1.le (by omega) (pin_data j').2 (pin_data i').2
    rcases lt_or_gt_of_ne ij with lt|gt
    · exact extend Q qp' ql' xo yo safe xi yj
        (component_pins_spaced_four hc even conn degree hp ah bh H xh yh xi yj lt)
    · exact extend Q.reverse qp'.reverse (by simpa using ql') yo xo
        (fun z m=>safe z (by simpa using m)) yj xi
        (component_pins_spaced_four hc even conn degree hp ah bh H yh xh yj xi gt)
  · have hn := neigh sx
    rw [lx,Finset.image_singleton] at hn
    exact no_foreign_pin_at_omitted_leaf_neighbor hc even conn degree hp ah bh len H
      xh yh xi yj ij hn.symm
  · have hn := neigh sy
    rw [ly,Finset.image_singleton] at hn
    exact no_foreign_pin_at_omitted_leaf_neighbor hc even conn degree hp ah bh len H
      yh xh yj xi ij.symm hn.symm

#print axioms no_length_ten_with_large_omitted_component_of_core_paths


/-- A length-ten optimum cannot omit six vertices, once the two marked
path lemmas on orders five and six are supplied. -/
theorem no_length_ten_with_six_omissions_of_core_paths
    (core6 : ∀ {W : Type u} (D : SimpleGraph W) [Fintype W] [DecidableEq W]
      [DecidableRel D.Adj], Fintype.card W=6 → (∀ w,1≤D.degree w) →
      (∀ s t,s≠t → 3≤D.degree s ∨ 3≤D.degree t) →
      ∀ {s t},s≠t →
      (∃ q : D.Walk s t,q.IsPath ∧ 3≤q.length) ∨
        D.neighborFinset s={t} ∨ D.neighborFinset t={s})
    (core5 : ∀ {W : Type u} (D : SimpleGraph W) [Fintype W] [DecidableEq W]
      [DecidableRel D.Adj], Fintype.card W=5 → (∀ w,3≤D.degree w) →
      ∀ {s t},s≠t → ∃ q : D.Walk s t,q.IsPath ∧ 3≤q.length)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (off : ((univ : Finset V)\p.support.toFinset).card=6) : False := by
  classical
  by_cases c : ∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices
  · obtain ⟨H,whole⟩ := c
    have e : H.vertices=(univ : Finset V)\p.support.toFinset := by
      ext z
      simp only [mem_sdiff,mem_univ,List.mem_toFinset,true_and]
      exact ⟨H.off _,whole _⟩
    have h6 : H.vertices.card=6 := by rwa [e]
    exact no_length_ten_with_large_omitted_component_of_core_paths core6 core5
      hc even conn degree hp ah bh len H (.inr h6) (fun h=> (by omega : False).elim)
  · obtain ⟨H,x,h5,_,_,_,_,high⟩ := disconnected_six_omissions_at_length_ten
      hc even conn degree hp ah bh len off c
    exact no_length_ten_with_large_omitted_component_of_core_paths core6 core5
      hc even conn degree hp ah bh len H (.inl h5) (fun _=>high)

#print axioms no_length_ten_with_six_omissions_of_core_paths

end Graffiti189LongestPath.TwoCut
