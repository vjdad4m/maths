import OffFour17GraphLift189
import OffFour17Structure189
import OffFour17Forward189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack OffFour17
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1700000
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin reverse_long same_support_optimal
  LeftMarks RightMarks dist_two mem_distanceTwo from SmallOrderFour189
open private omitted_degree_component_bound off_four_component_carries_all_high
  pins_gap_at_four two_pin_flanks_path_only two_pin_universal_in_omitted_component from FourOffGraphSupport189
open private two_pins_choose_ordered omittedDegree_eq omittedNeighbors from FourOffGraphCore189
open private min_two_from_cut from OrderSixteenFoundation189
open private omitted_neighbors_eq_component_neighbors from OffSix17CoreLift189

private structure FourLabels17 (S : Finset V) (x y : V) where
  fn : Fin 4→V
  inject : Function.Injective fn
  mem : ∀ i,fn i∈S
  lx : fn 2=x
  ly : fn 3=y

private theorem choose_four_labels_17 {S : Finset V} (four : S.card=4) {x y : V}
    (xh : x∈S) (yh : y∈S) (xy : x≠y) : Nonempty (FourLabels17 S x y) := by
  classical
  have b : y∈S.erase x := mem_erase.mpr ⟨xy.symm,yh⟩
  have c := card_erase_of_mem xh
  have d := card_erase_of_mem b
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<((S.erase x).erase y).card by omega)
  obtain ⟨uy,ue⟩ := mem_erase.mp um
  obtain ⟨ux,uS⟩ := mem_erase.mp ue
  obtain ⟨vy,ve⟩ := mem_erase.mp vm
  obtain ⟨vx,vS⟩ := mem_erase.mp ve
  let f (i : Fin 4) : V := if i=0 then u else if i=1 then v else if i=2 then x else y
  have lift : Function.Injective f := by
    intro i j e
    fin_cases i <;> fin_cases j <;> simp [f] at e ⊢
    all_goals first
      | exact False.elim (uv e) | exact False.elim (uv e.symm)
      | exact False.elim (ux e) | exact False.elim (ux e.symm)
      | exact False.elim (uy e) | exact False.elim (uy e.symm)
      | exact False.elim (vx e) | exact False.elim (vx e.symm)
      | exact False.elim (vy e) | exact False.elim (vy e.symm)
      | exact False.elim (xy e) | exact False.elim (xy e.symm)
  have mem (i : Fin 4) : f i∈S := by fin_cases i <;> simp [f,uS,vS,xh,yh]
  exact ⟨⟨f,lift,mem,by simp [f],by simp [f]⟩⟩

private theorem mapped_four_path
    {x y : V} (S : Finset V) (four : S.card=4)
    (members : x∈S ∧ y∈S) (xy : x≠y)
    (full : ∀ s∈S,∀ t∈S,s≠t → G.Adj s t) :
    ∃ q : G.Walk x y,q.IsPath ∧ q.length=3 ∧ ∀ z∈q.support,z∈S := by
  obtain ⟨f⟩ := choose_four_labels_17 four members.1 members.2 xy
  have adj (i j : Fin 4) (ij : i≠j) : G.Adj (f.fn i) (f.fn j) :=
    full _ (f.mem _) _ (f.mem _) (fun e=>ij (f.inject e))
  let q : G.Walk (f.fn 2) (f.fn 3) :=
    .cons (adj 2 0 (by decide)) (.cons (adj 0 1 (by decide)) (.cons (adj 1 3 (by decide)) .nil))
  have qp : q.IsPath := by
    apply IsPath.mk'
    exact (by decide : ([2,0,1,3]:List (Fin 4)).Nodup).map f.inject
  have l : q.length=3 := by simp [q]
  have stay (z : V) (zm : z∈q.support) : z∈S := by
    have e : z∈([2,0,1,3] : List (Fin 4)).map f.fn := zm
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp e
    exact f.mem k
  have ex : ∃ r : G.Walk (f.fn 2) (f.fn 3),r.IsPath ∧ r.length=3 ∧ ∀ z∈r.support,z∈S :=
    ⟨q,qp,l,stay⟩
  exact (congrArg₂ (fun a b=> ∃ r : G.Walk a b,r.IsPath ∧ r.length=3 ∧ ∀ z∈r.support,z∈S) f.lx f.ly) ▸ ex

private theorem four_component_clique_of_single
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (H : OmittedComponent p)
    (h4 : H.vertices.card=4) (one : ∀ z∈H.vertices,(Pins p z).card ≤ 1) :
    ∀ z∈H.vertices,∀ w∈H.vertices,z≠w → G.Adj z w := by
  classical
  have high (z : V) (zh : z∈H.vertices) (zd : 4 ≤ G.degree z) :
      G.neighborFinset z∩H.vertices=H.vertices.erase z := by
    have de := omittedDegree_eq hp (H.off _ zh)
    rw [omitted_neighbors_eq_component_neighbors H zh] at de
    have one := one z zh
    have cl : 3 ≤ (G.neighborFinset z∩H.vertices).card := by omega
    have sub : G.neighborFinset z∩H.vertices⊆H.vertices.erase z := by
      intro w wm
      obtain ⟨wn,wh⟩ := mem_inter.mp wm
      exact mem_erase.mpr ⟨((mem_neighborFinset _ _ _).mp wn).ne.symm,wh⟩
    apply eq_of_subset_of_card_le sub
    rw [card_erase_of_mem zh,h4]
    exact cl
  intro z zh w wh zw
  rcases degree z w zw with zl|wl
  · have h : w∈G.neighborFinset z∩H.vertices := by
      rw [high z zh zl]
      exact mem_erase.mpr ⟨zw.symm,wh⟩
    exact (mem_neighborFinset _ _ _).mp (mem_inter.mp h).1
  · have h : z∈G.neighborFinset w∩H.vertices := by
      rw [high w wh wl]
      exact mem_erase.mpr ⟨zw,zh⟩
    exact ((mem_neighborFinset _ _ _).mp (mem_inter.mp h).1).symm

private theorem four_clique_pins_central
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (H : OmittedComponent p) (h4 : H.vertices.card=4)
    (cl : ∀ z∈H.vertices,∀ w∈H.vertices,z≠w → G.Adj z w)
    (xh : x∈H.vertices) (yh : y∈H.vertices) (xy : x≠y)
    {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (ij : i<j) :
    4 ≤ i ∧ j ≤ 8 ∧ i+3 ≤ j := by
  have gap := component_pins_spaced_four hc even conn degree hp ah bh H xh yh xi yj ij
  obtain ⟨q,qp,ql,stay⟩ := mapped_four_path H.vertices h4 ⟨xh,yh⟩ xy cl
  have off (z : V) (zm : z∈q.support) := H.off _ (stay z zm)
  have left : 4 ≤ i := by
    apply Nat.le_of_not_gt
    intro small
    exact no_longest_with_long_omitted_path_between_sites hp.1 q qp off ij (pin_data yj).1.le
      (by omega) (pin_data xi).2 (pin_data yj).2
  have right : j ≤ 8 := by
    apply Nat.le_of_not_gt
    intro big
    have yi : p.length-j∈Pins p.reverse y := reverse_pin hp.1 (H.off _ yh) yj
    have xj : p.length-i∈Pins p.reverse x := reverse_pin hp.1 (H.off _ xh) xi
    have ql' : q.reverse.length=3 := by simpa using ql
    have jl := (pin_data yj).1
    exact no_longest_with_long_omitted_path_between_sites (reverse_long hp.1)
      q.reverse qp.reverse (fun z hz=>by simpa using off z (by simpa using hz))
      (by omega) (pin_data xj).1.le (by omega) (pin_data yi).2 (pin_data xj).2
  exact ⟨left,right,gap⟩

theorem no_length_twelve_four_clique_single
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (H : OmittedComponent p) (h4 : H.vertices.card=4)
    (one : ∀ z∈H.vertices,(Pins p z).card ≤ 1) : False := by
  classical
  have cl := four_component_clique_of_single degree hp.1 H h4 one
  have two := componentPins_card hp.1 H 2 conn
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<(componentPins H).card by omega)
  obtain ⟨up,x,xh,xu⟩ := mem_filter.mp um
  obtain ⟨vp,y,yh,yv⟩ := mem_filter.mp vm
  obtain ⟨i,xi,iu⟩ := pin_of_neighbor_mem hp.1 (H.off _ xh) (List.mem_toFinset.mp up) xu
  obtain ⟨j,yj,jv⟩ := pin_of_neighbor_mem hp.1 (H.off _ yh) (List.mem_toFinset.mp vp) yv
  have ij : i≠j := fun e=>uv (iu.symm.trans ((congrArg p.getVert e).trans jv))
  have xy : x≠y := by
    intro e
    subst y
    exact (Nat.not_lt_of_ge (one _ xh)) (one_lt_card.mpr ⟨i,xi,j,yj,ij⟩)
  have ordered {x y : V} (xh : x∈H.vertices) (yh : y∈H.vertices) (xy : x≠y)
      {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (ij : i<j) : False := by
    obtain ⟨il,jl,gap⟩ := four_clique_pins_central hc even conn degree hp ah bh len H h4 cl xh yh xy xi yj ij
    obtain ⟨q,qp,ql,stay⟩ := mapped_four_path H.vertices h4 ⟨xh,yh⟩ xy cl
    exact no_longest_with_forward_omitted_splice hp.1 q qp
      (fun z hz=>H.off _ (stay z hz)) ij (pin_data yj).1.le
      (by omega) (pin_data xi).2 (pin_data yj).2
  exact (lt_or_gt_of_ne ij).elim (ordered xh yh xy xi yj) (ordered yh xh xy.symm yj xi)

#print axioms no_length_twelve_four_clique_single


private theorem any_four_omitted_path_crossing_pins
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=12)
    (q : G.Walk x y) (qp : q.IsPath) (q3 : 3 ≤ q.length)
    (stay : ∀ z∈q.support,z∉p.support)
    {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (ij : i<j) : False := by
  have jl := (pin_data yj).1
  by_cases lo : i ≤ 3
  · exact no_longest_with_long_omitted_path_between_sites hp q qp stay ij jl.le
      (by omega) (pin_data xi).2 (pin_data yj).2
  by_cases hi : 9 ≤ j
  · have yr := reverse_pin hp (stay _ q.end_mem_support) yj
    have xr := reverse_pin hp (stay _ q.start_mem_support) xi
    have rlen : 3 ≤ q.reverse.length := by simpa using q3
    exact no_longest_with_long_omitted_path_between_sites (reverse_long hp) q.reverse qp.reverse
      (fun z hz=>by simpa using stay z (by simpa using hz)) (by omega) (pin_data xr).1.le
      (by omega) (pin_data yr).2 (pin_data xr).2
  exact no_longest_with_forward_omitted_splice hp q qp stay ij jl.le
    (by omega) (pin_data xi).2 (pin_data yj).2

theorem no_length_twelve_four_component_with_dual
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (H : OmittedComponent p) (h4 : H.vertices.card=4)
    {x : V} (xh : x∈H.vertices) (x2 : 2 ≤ (Pins p x).card) : False := by
  classical
  have xo := H.off _ xh
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered x2
  obtain ⟨pathD,sub⟩ := two_pin_flanks_path_only hc even conn degree hp ah bh xo xi xj ij
  have st := two_pin_universal_in_omitted_component hc H xh pathD
  have few (v : V) (vo : v∉p.support) := (at_most_two_pins_one_slack hc 2 (by decide)
    (fun z=>distanceTwo_le_of_even 4 z (even z)) conn degree hp vo).1
  have allPins (v : V) (vh : v∈H.vertices) (vx : v≠x) : Pins p v⊆({i,j}:Finset ℕ) :=
    sub v (H.off _ vh) (st v vh vx)
  obtain ⟨y,yh,yx,_,_⟩ := another_carrier_of_nontrivial_omitted_component conn hp.1 H (by omega) xh
  obtain ⟨f⟩ := choose_four_labels_17 h4 yh xh yx
  have sur (v : V) (vh : v∈H.vertices) : ∃ n : Fin 4, f.fn n=v := by
    have sub : (univ : Finset (Fin 4)).image f.fn⊆H.vertices := by
      intro v vm
      obtain ⟨k,_,rfl⟩ := mem_image.mp vm
      exact f.mem _
    have e := eq_of_subset_of_card_le sub (by rw [card_image_of_injective _ f.inject,card_univ,Fintype.card_fin,h4])
    obtain ⟨k,_,kv⟩ := mem_image.mp (e.symm ▸ vh)
    exact ⟨k,kv⟩
  have ed (k : Fin 4) (ne : k≠3) : G.Adj (f.fn 3) (f.fn k) := by
    rw [f.ly]
    exact st _ (f.mem _) (fun e=>ne (f.inject (e.trans f.ly.symm)))
  have neV {s t : Fin 4} (h : s≠t) : f.fn s≠f.fn t := fun e=>h (f.inject e)
  have bd (s : Fin 4) (T : Finset (Fin 4))
      (ff : ∀ q, G.Adj (f.fn s) (f.fn q) → q∈T) :
      G.degree (f.fn s) ≤ (Pins p (f.fn s)).card+T.card := by
    have d := omittedDegree_eq hp.1 (H.off _ (f.mem s))
    rw [omitted_neighbors_eq_component_neighbors H (f.mem s)] at d
    have sub : G.neighborFinset (f.fn s) ∩ H.vertices⊆T.image f.fn := by
      intro v vm
      obtain ⟨q,rfl⟩ := sur v (mem_inter.mp vm).2
      exact mem_image.mpr ⟨q,ff _ ((mem_neighborFinset _ _ _).mp (mem_inter.mp vm).1),rfl⟩
    have n := card_le_card sub
    rw [card_image_of_injective _ f.inject] at n
    omega
  have extra (s : Fin 4) (s3 : s≠3) (n : 2 ≤ (Pins p (f.fn s)).card) :
      i∈Pins p (f.fn s) ∧ j∈Pins p (f.fn s) := by
    have h := allPins _ (f.mem s) (fun e=>s3 (f.inject (e.trans f.ly.symm)))
    have c : ({i,j}:Finset ℕ).card=2 := by simp [ij.ne]
    have e := eq_of_subset_of_card_le h (by rw [c]; exact n)
    rw [e]
    simp
  have mk (r s u v : Fin 4) (nd : ([r,s,u,v]:List (Fin 4)).Nodup)
      (rs : G.Adj (f.fn r) (f.fn s)) (su : G.Adj (f.fn s) (f.fn u)) (uv : G.Adj (f.fn u) (f.fn v))
      (left : i∈Pins p (f.fn r)) (right : j∈Pins p (f.fn v)) : False := by
    let q : G.Walk (f.fn r) (f.fn v) := .cons rs (.cons su (.cons uv .nil))
    have qp : q.IsPath := IsPath.mk' (nd.map f.inject)
    have stay (z : V) (zm : z∈q.support) : z∉p.support := by
      change z∈([r,s,u,v]:List (Fin 4)).map f.fn at zm
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp zm
      exact H.off _ (f.mem k)
    exact any_four_omitted_path_crossing_pins hp.1 len q qp (by simp [q]) stay left right ij
  have xi' : i∈Pins p (f.fn 3) := f.ly.symm ▸ xi
  have xj' : j∈Pins p (f.fn 3) := f.ly.symm ▸ xj
  have mind (v : V) : 2 ≤ G.degree v := by
    apply min_two_from_cut conn
    have q := card_le_card (subset_univ p.support.toFinset)
    rw [card_univ,List.toFinset_card_of_nodup hp.1.1.support_nodup,length_support] at q
    omega
  have twoEdges (s t u : Fin 4)
      (ss : s≠3) (tt : t≠3) (uu : u≠3) (st' : s≠t) (su' : s≠u) (tu' : t≠u)
      (all : ∀ k : Fin 4,k=s ∨ k=t ∨ k=u ∨ k=3)
      (cs : G.Adj (f.fn u) (f.fn s)) (ct : G.Adj (f.fn u) (f.fn t))
      (bare : ¬G.Adj (f.fn s) (f.fn t)) : False := by
    have bs : G.degree (f.fn s) ≤ (Pins p (f.fn s)).card+2 := by
      have b := bd s {u,3} (by
        intro k hk
        rcases all k with rfl|rfl|rfl|rfl
        · exact (G.loopless _ hk).elim
        · exact (bare hk).elim
        · simp
        · simp)
      simpa [card_insert_of_not_mem,uu] using b
    have bt : G.degree (f.fn t) ≤ (Pins p (f.fn t)).card+2 := by
      have b := bd t {u,3} (by
        intro k hk
        rcases all k with rfl|rfl|rfl|rfl
        · exact (bare hk.symm).elim
        · exact (G.loopless _ hk).elim
        · simp
        · simp)
      simpa [card_insert_of_not_mem,uu] using b
    rcases degree _ _ (neV st') with sh|th
    · have pe := extra s ss (by omega)
      exact mk 3 t u s (by simp [ss,tt,uu,st'.symm,su'.symm,tu',Ne.symm ss,Ne.symm tt,Ne.symm uu])
        (ed t tt) ct.symm cs xi' pe.2
    · have pe := extra t tt (by omega)
      exact mk 3 s u t (by simp [ss,tt,uu,st',su',tu'.symm,Ne.symm ss,Ne.symm tt,Ne.symm uu])
        (ed s ss) cs.symm ct xi' pe.2
  have oneEdge (s t u : Fin 4)
      (ss : s≠3) (tt : t≠3) (uu : u≠3) (st' : s≠t) (su' : s≠u) (tu' : t≠u)
      (all : ∀ k : Fin 4,k=s ∨ k=t ∨ k=u ∨ k=3)
      (e : G.Adj (f.fn s) (f.fn t))
      (es : ¬G.Adj (f.fn s) (f.fn u)) (et : ¬G.Adj (f.fn t) (f.fn u)) : False := by
    have bu : G.degree (f.fn u) ≤ (Pins p (f.fn u)).card+1 := by
      have b := bd u {3} (by
        intro k hk
        rcases all k with rfl|rfl|rfl|rfl
        · exact (es hk.symm).elim
        · exact (et hk.symm).elim
        · exact (G.loopless _ hk).elim
        · simp)
      simpa using b
    have u2 := few _ (H.off _ (f.mem u))
    have bs : G.degree (f.fn s) ≤ (Pins p (f.fn s)).card+2 := by
      have b := bd s {t,3} (by
        intro k hk
        rcases all k with rfl|rfl|rfl|rfl
        · exact (G.loopless _ hk).elim
        · simp
        · exact (es hk).elim
        · simp)
      simpa [card_insert_of_not_mem,tt] using b
    have sh := (degree _ _ (neV su')).resolve_right (by omega)
    have pe := extra s ss (by omega)
    have ml := mind (f.fn u)
    obtain ⟨k,kp⟩ := card_pos.mp (show 0<(Pins p (f.fn u)).card by omega)
    have ps := allPins _ (f.mem u) (fun e=>uu (f.inject (e.trans f.ly.symm))) kp
    have ks : k=i ∨ k=j := by simpa using ps
    rcases ks with ki|kj
    · exact mk u 3 t s (by simp [ss,tt,uu,st'.symm,su'.symm,tu'.symm,Ne.symm ss,Ne.symm tt])
        (ed u uu).symm (ed t tt) e.symm (ki ▸ kp) pe.2
    · exact mk s t 3 u (by simp [ss,tt,uu,st',su',tu',Ne.symm uu])
        e (ed t tt).symm (ed u uu) pe.1 (kj ▸ kp)
  by_cases a : G.Adj (f.fn 0) (f.fn 1) <;>
    by_cases b : G.Adj (f.fn 0) (f.fn 2) <;>
    by_cases c : G.Adj (f.fn 1) (f.fn 2)
  · have full (s t : V) (sh : s∈H.vertices) (th : t∈H.vertices) (ne : s≠t) : G.Adj s t := by
      obtain ⟨r,rfl⟩ := sur s sh
      obtain ⟨q,rfl⟩ := sur t th
      have rq : r≠q := fun e=>ne (congrArg f.fn e)
      have e0 := ed 0 (by decide)
      have e1 := ed 1 (by decide)
      have e2 := ed 2 (by decide)
      have ae := a.symm
      have be := b.symm
      have ce := c.symm
      have e0' := e0.symm
      have e1' := e1.symm
      have e2' := e2.symm
      fin_cases r <;> fin_cases q <;>
        first | exact (rq rfl).elim | assumption
    obtain ⟨z,zh,zx,k,kp⟩ := another_carrier_of_nontrivial_omitted_component conn hp.1 H (by omega) xh
    obtain ⟨q,qp,ql,stay⟩ := mapped_four_path H.vertices h4 ⟨xh,zh⟩ zx.symm
      (fun u uh v vh e=>full u v uh vh e)
    have ks : k=i ∨ k=j := by simpa using allPins _ zh zx kp
    rcases ks with ki|kj
    · exact any_four_omitted_path_crossing_pins hp.1 len q.reverse qp.reverse
        (by simp [ql]) (fun v vz=>H.off _ (stay v (by simpa using vz))) (ki ▸ kp) xj ij
    · exact any_four_omitted_path_crossing_pins hp.1 len q qp
        (by omega) (fun v vz=>H.off _ (stay v vz)) xi (kj ▸ kp) ij
  · exact twoEdges 1 2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) a b c
  · exact twoEdges 0 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) a.symm c b
  · exact oneEdge 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) a b c
  · exact twoEdges 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) b.symm c.symm a
  · exact oneEdge 0 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) b a (fun e=>c e.symm)
  · exact oneEdge 1 2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro k; fin_cases k <;> decide) c (fun e=>a e.symm) (fun e=>b e.symm)
  · have z0 : G.degree (f.fn 0) ≤ (Pins p (f.fn 0)).card+1 := by
      have n := bd 0 {3} (by
        intro q qh
        fin_cases q
        · exact (G.loopless _ qh).elim
        · exact (a qh).elim
        · exact (b qh).elim
        · simp)
      simpa using n
    have z1 : G.degree (f.fn 1) ≤ (Pins p (f.fn 1)).card+1 := by
      have n := bd 1 {3} (by
        intro q qh
        fin_cases q
        · exact (a qh.symm).elim
        · exact (G.loopless _ qh).elim
        · exact (c qh).elim
        · simp)
      simpa using n
    have f0 := few _ (H.off _ (f.mem 0))
    have f1 := few _ (H.off _ (f.mem 1))
    rcases degree _ _ (neV (show (0:Fin 4)≠1 by decide)) with h|h <;> omega

#print axioms no_length_twelve_four_component_with_dual


private theorem double_triangle_pattern
    {a b x y : V} {p : G.Walk a b} (H : OmittedComponent p)
    (yh : y∈H.vertices) (xout : x∉H.vertices) (xo : x∉p.support)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
    {i j k l : ℕ}
    (all : ∀ z∈H.vertices,i∈Pins p z ∧ j∈Pins p z)
    (xk : k∈Pins p x) (xl : l∈Pins p x)
    (ir : i ≤ 11) (jr : j ≤ 11) (kr : k ≤ 11) (lr : l ≤ 11)
    (full : ∀ z∈H.vertices,∀ w∈H.vertices,z≠w → G.Adj z w)
    (holes : ∀ r,hole i j r → r∉LeftMarks p∪RightMarks p) :
    Nonempty (FourOmissionPattern17 p 3 i j k l) := by
  classical
  let S := (univ : Finset V)\p.support.toFinset
  have memS {z : V} : z∈S ↔ z∉p.support := by simp [S]
  have yo := H.off _ yh
  obtain ⟨f⟩ := choose_four_labels_17 off (memS.mpr yo) (memS.mpr xo) (fun e=>xout (e ▸ yh))
  have inside (u : Fin 4) (hu : u.val ≤ 2) : f.fn u∈H.vertices := by
    have q := whole _ (memS.mp (f.mem u))
    rcases q with e|h
    · have g := congrArg Fin.val (f.inject (e.trans f.ly.symm))
      change u.val=3 at g
      omega
    · exact h
  refine ⟨⟨f.fn,f.inject,fun s=>memS.mp (f.mem s),ir,jr,kr,lr,?_,?_,?_,?_⟩⟩
  · intro r hr
    rcases hr with rfl|rfl|⟨_,rfl|rfl⟩
    · exact ⟨y,yo,(all _ yh).1⟩
    · exact ⟨y,yo,(all _ yh).2⟩
    · exact ⟨x,xo,xk⟩
    · exact ⟨x,xo,xl⟩
  · intro u r h
    simp only [OffFour17.attach,show ¬(3:ℕ)=0 by decide,show ¬((3:ℕ)=1 ∨ 3=2) by decide,if_false] at h
    rcases h with ⟨rfl|rfl,_,b⟩|⟨rfl|rfl,b⟩
    · exact (all _ (inside u (by omega))).1
    · exact (all _ (inside u (by omega))).2
    · have e : u=3 := Fin.ext (by omega)
      rw [e,f.ly]
      exact xk
    · have e : u=3 := Fin.ext (by omega)
      rw [e,f.ly]
      exact xl
  · intro u v h
    have lt := h.2.1
    have b : 13+v.val ≤ 15 := by simpa [core] using h.2.2
    exact full _ (inside u (by omega)) _ (inside v (by omega)) (fun e=>by
      have g := congrArg Fin.val (f.inject e)
      omega)
  · intro _
    exact holes

private theorem triangle_port_central
    {a b x y z : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=12)
    (xo : x∉p.support) (yo : y∉p.support) (zo : z∉p.support)
    (xz : G.Adj x z) (zy : G.Adj z y) (xy : x≠y)
    {i j : ℕ} (ix : i∈Pins p x) (jy : j∈Pins p y) (ij : i<j) :
    3 ≤ i ∧ j ≤ 9 := by
  let q : G.Walk x y := .cons xz (.cons zy .nil)
  have qp : q.IsPath := by
    apply IsPath.mk'
    simp [q,xz.ne,zy.ne,xy]
  have n : q.length=2 := by simp [q]
  have safe (v : V) (vm : v∈q.support) : v∉p.support := by
    have e : v=x ∨ v=z ∨ v=y := by simpa [q] using vm
    rcases e with rfl|rfl|rfl <;> assumption
  have ir : 3 ≤ i := by
    apply Nat.le_of_not_gt
    intro f
    exact no_longest_with_long_omitted_path_between_sites hp q qp safe ij (pin_data jy).1.le
      (by omega) (pin_data ix).2 (pin_data jy).2
  have jl : j ≤ 9 := by
    apply Nat.le_of_not_gt
    intro f
    have jp := (pin_data jy).1
    have yi := reverse_pin hp yo jy
    have xj := reverse_pin hp xo ix
    have qr : q.reverse.length=2 := by simpa using n
    exact no_longest_with_long_omitted_path_between_sites (reverse_long hp)
      q.reverse qp.reverse (fun z hz=>by simpa using safe z (by simpa using hz))
      (by omega) (pin_data xj).1.le (by omega) (pin_data yi).2 (pin_data xj).2
  exact ⟨ir,jl⟩

theorem no_length_twelve_three_plus_one_of_rows
    (table : ∀ i j,3 ≤ i → j ≤ 9 → i+3 ≤ j → i+j ≤ 12 → row 3 i j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (H : OmittedComponent p) (h3 : H.vertices.card=3)
    (hHigh : ∀ z∈H.vertices,4 ≤ G.degree z) : False := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  let S := O\H.vertices
  have memO {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have sub : H.vertices⊆O := fun z zh=>memO.mpr (H.off _ zh)
  have div := card_sdiff_add_card_eq_card sub
  have oo : O.card=4 := off
  have s1 : S.card=1 := by change (O\H.vertices).card=1; omega
  obtain ⟨x,onlyx⟩ := card_eq_one.mp s1
  have xS : x∈S := by rw [onlyx]; simp
  have xo := memO.mp (mem_sdiff.mp xS).1
  have xout := (mem_sdiff.mp xS).2
  have whole (z : V) (zo : z∉p.support) : z=x ∨ z∈H.vertices := by
    by_cases zh : z∈H.vertices
    · exact .inr zh
    · have h : z∈S := mem_sdiff.mpr ⟨memO.mpr zo,zh⟩
      rw [onlyx] at h
      exact .inl (mem_singleton.mp h)
  have isol (z : V) (zo : z∉p.support) : ¬G.Adj x z := by
    intro e
    rcases whole z zo with rfl|zh
    · exact G.loopless _ e
    · exact xo (H.closed _ zh _ xout e.symm)
  have cap := fun v=>distanceTwo_le_of_even 4 v (even v)
  have few (z : V) (zo : z∉p.support) :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp zo).1
  have xd := omittedDegree_eq hp.1 xo
  have x0 : omittedNeighbors p x=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    have d := mem_filter.mp hw
    exact (isol _ d.2) ((mem_neighborFinset _ _ _).mp d.1)
  rw [x0,card_empty,Nat.add_zero] at xd
  have z3 : 3 ≤ Fintype.card V := by
    have b := card_le_card (subset_univ p.support.toFinset)
    rw [List.toFinset_card_of_nodup hp.1.1.support_nodup,length_support,card_univ] at b
    omega
  have min2 := min_two_from_cut conn z3 x
  obtain ⟨k,l,xk,xl,kl⟩ := two_pins_choose_ordered (show 2 ≤ (Pins p x).card by omega)
  have klg := pins_gap_at_four hc even conn degree hp ah bh xo xk xl kl
  obtain ⟨y,yh⟩ := H.nonempty
  have yo := H.off _ yh
  have two (z : V) (zh : z∈H.vertices) : 2 ≤ (Pins p z).card := by
    have d := omitted_degree_component_bound hp.1 H zh
    have hi := hHigh _ zh
    omega
  obtain ⟨i,j,yi,yj,ij⟩ := two_pins_choose_ordered (two _ yh)
  have iG := pins_gap_at_four hc even conn degree hp ah bh yo yi yj ij
  obtain ⟨onD,subP⟩ := two_pin_flanks_path_only hc even conn degree hp ah bh yo yi yj ij
  have uy := two_pin_universal_in_omitted_component hc H yh onD
  have same (z : V) (zh : z∈H.vertices) : i∈Pins p z ∧ j∈Pins p z := by
    by_cases e : z=y
    · exact e.symm ▸ ⟨yi,yj⟩
    have zp := subP z (H.off _ zh) (uy _ zh e)
    have p2 : ({i,j}:Finset ℕ).card=2 := by simp [ij.ne]
    have ep := eq_of_subset_of_card_le zp (by rw [p2]; exact two _ zh)
    rw [ep]
    simp
  have clique (z : V) (zh : z∈H.vertices) (w : V) (wh : w∈H.vertices) (zw : z≠w) : G.Adj z w := by
    have d := (two_pin_flanks_path_only hc even conn degree hp ah bh (H.off _ zh)
      (same _ zh).1 (same _ zh).2 ij).1
    exact two_pin_universal_in_omitted_component hc H zh d w wh zw.symm
  have noShare {r : ℕ} (xr : r∈Pins p x) (yr : r∈Pins p y) : False := by
    have xy : y≠x := fun e=>xout (e ▸ yh)
    have dy : x∈DistanceTwo G y := mem_distanceTwo.mpr (dist_two hc xy
      (fun e=>isol y yo e.symm) (pin_data yr).2 (pin_data xr).2.symm)
    exact xo (onD _ dy)
  have ki : k≠i := fun e=>noShare xk (e.symm ▸ yi)
  have kj : k≠j := fun e=>noShare xk (e.symm ▸ yj)
  have li : l≠i := fun e=>noShare xl (e.symm ▸ yi)
  have lj : l≠j := fun e=>noShare xl (e.symm ▸ yj)
  have yc := card_erase_of_mem yh
  obtain ⟨z,zm,w,wm,zw⟩ := one_lt_card.mp (show 1<(H.vertices.erase y).card by omega)
  obtain ⟨zy,zh⟩ := mem_erase.mp zm
  obtain ⟨wy,wh⟩ := mem_erase.mp wm
  obtain ⟨ic,jc⟩ := triangle_port_central hp.1 len yo (H.off _ zh) (H.off _ wh)
    (clique y yh w wh wy.symm) (clique w wh z zh zw.symm) zy.symm yi (same _ zh).2 ij
  have close {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
      (len : p.length=12)
      (H : OmittedComponent p) (yh : y∈H.vertices) (xout : x∉H.vertices)
      (xo : x∉p.support) (off : ((univ : Finset V)\p.support.toFinset).card=4)
      (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
      {i j k l : ℕ} (all : ∀ z∈H.vertices,i∈Pins p z ∧ j∈Pins p z)
      (xk : k∈Pins p x) (xl : l∈Pins p x) (ic : 3 ≤ i) (jc : j ≤ 9) (ig : i+3 ≤ j)
      (ori : i+j ≤ 12) (klg : k+3 ≤ l)
      (ki : k≠i) (kj : k≠j) (li : l≠i) (lj : l≠j)
      (clique : ∀ z∈H.vertices,∀ w∈H.vertices,z≠w → G.Adj z w) : False := by
    have ir := (pin_data (all _ yh).1).1
    have jr := (pin_data (all _ yh).2).1
    have kr := pin_pos hp.1 xo xk
    have lr := (pin_data xl).1
    have holes := four_holes_of_interior_dual_pair hc even conn degree hp ah bh (H.off _ yh)
      (all _ yh).1 (all _ yh).2 (by omega) (by omega) (by omega)
    obtain ⟨P⟩ := double_triangle_pattern H yh xout xo off whole all xk xl
      (by omega) (by omega) (by omega) (by omega) clique holes
    exact four_omissions_row_contradiction hc even hp ah bh len P
      (table i j ic jc ig ori) (extra_disc (by omega) klg (by omega) ki kj li lj)
  by_cases ori : i+j ≤ 12
  · exact close hp ah bh len H yh xout xo off whole same xk xl ic jc iG ori klg ki kj li lj clique
  let R : OmittedComponent p.reverse := ⟨H.vertices,H.nonempty,(by intro z h; simpa using H.off z h),
    (by intro z hz w hw zw; simpa using H.closed z hz w hw zw),H.joined⟩
  have hp' := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have rx : x∉p.reverse.support := by simpa using xo
  have rk := reverse_pin hp.1 xo xl
  have rl := reverse_pin hp.1 xo xk
  have kr := (pin_data xk).1
  have lr := (pin_data xl).1
  have allR (z : V) (zh : z∈R.vertices) :
      p.length-j∈Pins p.reverse z ∧ p.length-i∈Pins p.reverse z :=
    ⟨reverse_pin hp.1 (H.off _ zh) (same _ zh).2,reverse_pin hp.1 (H.off _ zh) (same _ zh).1⟩
  exact close hp' bh ah (by simpa using len) R yh xout rx
    (by simpa [support_reverse] using off) (fun z h=>whole z (by simpa using h)) allR rk rl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) clique

#print axioms no_length_twelve_three_plus_one_of_rows

/-- General partition for the last degree-four order-seventeen branch. -/
theorem no_length_twelve_with_four_omissions_of_rows
    (disc : ∀ i j,3 ≤ i → j ≤ 9 → i+3 ≤ j → i+j ≤ 12 → row 3 i j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (off : ((univ : Finset V)\p.support.toFinset).card=4) : False := by
  classical
  have few (z : V) (zo : z∉p.support) :=
    (at_most_two_pins_one_slack hc 2 (by decide) (fun v=>distanceTwo_le_of_even 4 v (even v))
      conn degree hp zo).1
  obtain ⟨H,lo,_,many⟩ := off_four_component_carries_all_high degree hp.1 off few
  have hi : H.vertices.card ≤ 4 := by
    rw [←off]
    exact card_le_card (fun z zh=>mem_sdiff.mpr ⟨mem_univ _,by simpa using H.off z zh⟩)
  by_cases h3 : H.vertices.card=3
  · have all : H.vertices.filter (fun z=>4 ≤ G.degree z)=H.vertices :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    have high (z : V) (zh : z∈H.vertices) : 4 ≤ G.degree z := by
      have p : z∈H.vertices.filter (fun z=>4 ≤ G.degree z) := all.symm ▸ zh
      exact (mem_filter.mp p).2
    exact no_length_twelve_three_plus_one_of_rows disc hc even conn degree hp ah bh len off H h3 high
  have h4 : H.vertices.card=4 := by omega
  by_cases dual : ∃ x∈H.vertices,2 ≤ (Pins p x).card
  · obtain ⟨x,xh,x2⟩ := dual
    exact no_length_twelve_four_component_with_dual hc even conn degree hp ah bh len H h4 xh x2
  have one (z : V) (zh : z∈H.vertices) : (Pins p z).card ≤ 1 :=
    Nat.le_of_not_gt (fun e=>dual ⟨z,zh,e⟩)
  exact no_length_twelve_four_clique_single hc even conn degree hp ah bh len H h4 one

#print axioms no_length_twelve_with_four_omissions_of_rows
end Graffiti189LongestPath.TwoCut
