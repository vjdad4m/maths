import NoPairs189
import ActualDistThree189
namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

private theorem no_endpoints {x a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) :
    ¬G.Adj x a ∧ ¬G.Adj x b := by
  constructor
  · intro h
    have hle := hp.2 x b (.cons h p) (hp.1.cons hx)
    simp at hle
  · intro h
    have hq : (Walk.cons h p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hx)).reverse
    have hle := hp.2 a x _ hq
    simp at hle

private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega




variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
omit [Fintype V] [DecidableEq V] in
private theorem pin_data {a b : V} {p : G.Walk a b} {x : V} {i : ℕ}
    (hi : i ∈ Pins p x) : i < p.length ∧ G.Adj x (p.getVert i) :=
  ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

omit [Fintype V] [DecidableEq V] in
private theorem pin_of_neighbor_mem {a b x y : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) (hy : y ∈ p.support) (e : G.Adj x y) :
    ∃ i ∈ Pins p x, p.getVert i = y := by
  obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hy
  have hi : i < p.length := by
    by_contra! h
    have ee : i = p.length := by omega
    rw [ee,getVert_length] at he
    exact (no_endpoints hp hx).2 (he.symm ▸ e)
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ e⟩,he⟩


private lemma pin_pos {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : 0 < i := by
  by_contra h
  have e : i=0 := Nat.eq_zero_of_not_pos h
  exact (no_endpoints hp hx).1 (by simpa only [e,getVert_zero] using (pin_data hi).2)



variable {a b : V} {p : G.Walk a b} {x : V}
private lemma mem_distanceTwo {x y : V} : y∈DistanceTwo G x ↔ G.dist x y=2 := by
  classical
  simp [DistanceTwo]

private theorem card_pinVertices (hp : IsLongest p) :
    (PinVertices p x).card = (Pins p x).card := by
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e

private theorem cardinal_flankVertices (hp : IsLongest p) :
    (FlankVertices p x).card = (FlankIndices p x).card := by
  have upper (i : ℕ) (hi : i∈FlankIndices p x) : i≤p.length := by
    rcases mem_union.mp hi with hi|hi
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j-1≤p.length
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j+1≤p.length
      omega
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (upper i hi) (upper j hj) e

private def LeftMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj a (p.getVert (i+1))

private def RightMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj b (p.getVert i)

private theorem card_leftMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (LeftMarks p).card = G.degree a := by
  classical
  have eq : (LeftMarks p).image (fun i => p.getVert (i+1)) = G.neighborFinset a := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).1 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : 0 < i := by
        by_contra h
        have he : i=0 := by omega
        rw [he,getVert_zero] at ei
        exact e.ne ei
      have iq : i-1+1=i := by omega
      exact ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [iq,ei]⟩,by rwa [iq]⟩
  have inj : ((LeftMarks p).image (fun i => p.getVert (i+1))).card = (LeftMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    have h := hp.1.getVert_injOn (show i+1≤p.length by omega) (show j+1≤p.length by omega) e
    omega
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

private theorem card_rightMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (RightMarks p).card = G.degree b := by
  classical
  have eq : (RightMarks p).image p.getVert = G.neighborFinset b := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).2 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : i < p.length := by
        by_contra h
        have he : i=p.length := by omega
        rw [he,getVert_length] at ei
        exact e.ne ei
      exact ⟨i,mem_filter.mpr ⟨mem_range.mpr ip,by rwa [ei]⟩,ei⟩
  have inj : ((RightMarks p).image p.getVert).card = (RightMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    exact hp.1.getVert_injOn il.le jl.le e
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm


private theorem same_support_optimal {a b s t : V} {p : G.Walk a b} {q : G.Walk s t}
    (hp : EdgeOptimal p) (hq : IsLongest q) (same : ∀ z,z∈p.support↔z∈q.support) :
    EdgeOptimal q := by
  have e : OmittedEdges p=OmittedEdges q := by
    ext yz
    simp only [OmittedEdges,mem_filter,mem_univ,true_and,same yz.1,same yz.2]
  exact ⟨hq,fun _ _ _ hr => e ▸ hp.2 _ _ _ hr⟩

private theorem reverse_long {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    IsLongest p.reverse := ⟨hp.1.reverse,fun _ _ _ h => by simpa using hp.2 _ _ _ h⟩

private theorem reverse_pin {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) : p.length-i∈Pins p.reverse x := by
  have ip := pin_pos hp hx hi
  have il := (pin_data hi).1
  refine mem_filter.mpr ⟨mem_range.mpr (by rw [length_reverse]; omega),?_⟩
  rw [getVert_reverse]
  have q : p.length-(p.length-i)=i := by omega
  rw [q]
  exact (pin_data hi).2

private theorem mark_length {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (xo : x∉p.support) (yp : y∈p.support) (xy : G.Adj x y)
    (Holes : Finset ℕ) (hr : Holes⊆range p.length)
    (hm : Disjoint (LeftMarks p∪RightMarks p) Holes) :
    G.degree a+G.degree b+Holes.card≤p.length := by
  have d : Disjoint (LeftMarks p) (RightMarks p) := disjoint_left.mpr (by
    intro j jl jr
    have jlt := mem_range.mp (mem_filter.mp jl).1
    exact not_adj_both_end_marks hp xo yp xy jlt (mem_filter.mp jl).2 (mem_filter.mp jr).2)
  have sub : LeftMarks p∪RightMarks p⊆range p.length :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have c := card_le_card (union_subset sub hr)
  rwa [card_union_of_disjoint hm,card_union_of_disjoint d,
    card_leftMarks hp,card_rightMarks hp,card_range] at c

private theorem degree_off_bound {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) :
    G.degree x≤(Pins p x).card + ((univ : Finset V)\p.support.toFinset).card-1 := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have xO : x∈O := mem_sdiff.mpr ⟨mem_univ _,fun e => xo (List.mem_toFinset.mp e)⟩
  have sub : G.neighborFinset x ⊆ PinVertices p x∪O.erase x := by
    intro y yn
    have xy := (mem_neighborFinset G x y).mp yn
    by_cases yp : y∈p.support
    · obtain ⟨i,hi,e⟩ := pin_of_neighbor_mem hp xo yp xy
      exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,e⟩))
    · exact mem_union.mpr (Or.inr (mem_erase.mpr
        ⟨xy.ne.symm,mem_sdiff.mpr ⟨mem_univ _,fun e => yp (List.mem_toFinset.mp e)⟩⟩))
  have c := card_le_card sub
  have c' := card_union_le (PinVertices p x) (O.erase x)
  rw [card_erase_of_mem xO,card_pinVertices hp] at c'
  rw [card_neighborFinset_eq_degree] at c
  have pos := card_pos.mpr (show O.Nonempty from ⟨x,xO⟩)
  change G.degree x≤(Pins p x).card+O.card-1
  omega

private theorem two_flanks_full {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hc : G.Connected) (xo : x∉p.support) (F2 : (Pins p x).card≤2)
    (cap : (DistanceTwo G x).card≤4) {i j : ℕ}
    (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    DistanceTwo G x=FlankVertices p x ∧
    FlankIndices p x = ({i-1,i+1,j-1,j+1}:Finset ℕ) := by
  have pins : Pins p x={i,j} := (eq_of_subset_of_card_le
    (show ({i,j}:Finset ℕ)⊆Pins p x from fun k hk =>
      (mem_insert.mp hk).elim (fun e => e.symm ▸ hi) (fun e => (mem_singleton.mp e).symm ▸ hj))
    (by simpa only [card_insert_of_not_mem (show i∉({j}:Finset ℕ) by
          intro h; have e := mem_singleton.mp h; omega),card_singleton] using F2)).symm
  have f : FlankIndices p x=({i-1,i+1,j-1,j+1}:Finset ℕ) := by
    ext k
    simp only [FlankIndices,pins,image_insert,image_singleton,mem_union,mem_insert,mem_singleton]
    tauto
  have n1 : i-1≠i+1 := by omega
  have n2 : i-1≠j-1 := by omega
  have n3 : i-1≠j+1 := by omega
  have n4 : i+1≠j-1 := by omega
  have n5 : i+1≠j+1 := by omega
  have n6 : j-1≠j+1 := by omega
  have fc : (FlankVertices p x).card=4 := by
    rw [cardinal_flankVertices hp,f]
    have h1 : i-1∉({i+1,j-1,j+1}:Finset ℕ) := by simp [n1,n2,n3]
    have h2 : i+1∉({j-1,j+1}:Finset ℕ) := fun h => (mem_insert.mp h).elim n4 (fun e => n5 (mem_singleton.mp e))
    have h3 : j-1∉({j+1}:Finset ℕ) := by simp [n6]
    rw [card_insert_of_not_mem h1,card_insert_of_not_mem h2,card_insert_of_not_mem h3,card_singleton]
  have sub : FlankVertices p x⊆DistanceTwo G x :=
    fun _ h => (mem_sdiff.mp (flanks_outside_boundary hc hp xo h)).1
  exact ⟨(eq_of_subset_of_card_le sub (by omega)).symm,f⟩

private theorem second_pin_no_start_of_high {a b x : V} {p : G.Walk a b}
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (hp : EdgeOptimal p) (bh : 4≤G.degree b) (xo : x∉p.support)
    (F2 : (Pins p x).card≤2) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x)
    (gap : i+3≤j) (hiend : 4≤G.degree (p.getVert (j-1))) :
    ¬G.Adj a (p.getVert j) := by
  intro e
  have ha := (no_endpoints hp.1 xo).1
  have nae : x≠a := fun e => xo (e.symm ▸ p.start_mem_support)
  have ax : a∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc nae ha (pin_data hj).2 e.symm)
  have cap := distanceTwo_le_of_even 4 x (even x)
  obtain ⟨f,fi⟩ := two_flanks_full hp.1 hc xo F2 cap hi hj gap
  rw [f] at ax
  obtain ⟨t,tf,ta⟩ := mem_image.mp ax
  rw [fi] at tf
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp.1 xo hi
  have tl : t≤p.length := by simp only [mem_insert,mem_singleton] at tf; rcases tf with rfl|rfl|rfl|rfl <;> omega
  have tz : t=0 := hp.1.1.getVert_injOn tl (Nat.zero_le _) (ta.trans p.getVert_zero.symm)
  have ione : i=1 := by
    simp only [mem_insert,mem_singleton] at tf
    rcases tf with h|h|h|h <;> omega
  have je : j-1+1=j := by omega
  obtain ⟨q,hq,same,ql,map⟩ := MultiRotation.rotate_start_map hp.1 (j-1)
    (by omega) (by rwa [je])
  have assigned : EdgeOptimal q := same_support_optimal hp hq same
  have qxo : x∉q.support := fun e => xo ((same x).mpr e)
  have qj : j∈Pins q x := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
    rw [map j jl.le,if_neg (show ¬j≤j-1 by omega)]
    exact (pin_data hj).2
  have qi : j-2∈Pins q x := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
    rw [map (j-2) (by omega),if_pos (show j-2≤j-1 by omega)]
    have h : j-1-(j-2)=i := by omega
    rw [h]
    exact (pin_data hi).2
  have paired : j-2∈PairedPins q x := mem_filter.mpr ⟨qi,j,qj,Or.inr (by omega)⟩
  rw [no_paired_pins_at_four hc even conn degree assigned hiend bh qxo] at paired
  exact not_mem_empty _ paired

/-- At degree threshold four, the distance-even Graffiti.pc #189 hypothesis
and 2-connectivity imply traceability on at most eleven vertices. -/
theorem traceable_of_order_le_eleven (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤11) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_contra fail
  obtain ⟨a,b,p,hp,ah,bh⟩ := exists_edge_optimal_with_high_ends hc 2 4 (by decide) conn degree fail
  obtain ⟨u,uo⟩ : ∃ u,u∉p.support := not_forall.mp (fun h => fail ⟨a,b,p,hp.1.1,h⟩)
  obtain ⟨S,ux,Sne,Soff,Sclosed,Sjoined⟩ := exists_omitted_component uo
  let H : OmittedComponent p := ⟨S,Sne,Soff,Sclosed,Sjoined⟩
  have se := componentPins_card hp.1 H 2 conn
  obtain ⟨y,yp⟩ := card_pos.mp (show 0<(componentPins H).card by omega)
  obtain ⟨yp,x,xH,xy⟩ := mem_filter.mp yp
  have xo := H.off x xH
  have yp' := List.mem_toFinset.mp yp
  have lower := mark_length hp.1 xo yp' xy ∅ (empty_subset _) (by simp)
  let O := (univ : Finset V)\p.support.toFinset
  have cardO : O.card+(p.length+1)=Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    rwa [List.toFinset_card_of_nodup hp.1.1.support_nodup,length_support,card_univ] at h
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few {a b : V} {q : G.Walk a b} (hq : EdgeOptimal q) {x : V} (xo : x∉q.support) :
      (Pins q x).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hq xo).1
  have low {z : V} (zo : z∉p.support) : ¬4≤G.degree z := by
    have f := few hp zo
    have bd := degree_off_bound hp.1 zo
    change G.degree z≤(Pins p z).card+O.card-1 at bd
    simp only [card_empty,Nat.add_zero] at lower
    omega
  have only {z : V} (zo : z∉p.support) : z=x :=
    Classical.byContradiction (fun e => (degree z x e).elim (low zo) (low xo))
  have high_in {z : V} (zp : z∈p.support) : 4≤G.degree z :=
    (degree z x (fun e => xo (e ▸ zp))).resolve_right (low xo)
  have xl : 2≤G.degree x := by
    simp only [card_empty,Nat.add_zero] at lower
    exact Graffiti189LongestPath.TwoCut.min_two_from_connectivity conn (by omega) x
  have xcard : 1<(G.neighborFinset x).card := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨r,rn,s,sn,rs⟩ := one_lt_card.mp xcard
  have onpath (y : V) (xy : G.Adj x y) : y∈p.support :=
    Classical.byContradiction (fun o => xy.ne (only o).symm)
  have axr := (mem_neighborFinset G x r).mp rn
  have axs := (mem_neighborFinset G x s).mp sn
  obtain ⟨i,hi,eqi⟩ := pin_of_neighbor_mem hp.1 xo (onpath r axr) axr
  obtain ⟨j,hj,eqj⟩ := pin_of_neighbor_mem hp.1 xo (onpath s axs) axs
  have ne : i≠j := fun e => rs (eqi.symm.trans ((congrArg p.getVert e).trans eqj))
  obtain ⟨i,j,hi,hj,orderPins⟩ : ∃ i j, i∈Pins p x ∧ j∈Pins p x ∧ i<j := by
    rcases lt_or_gt_of_ne ne with e|e
    · exact ⟨i,j,hi,hj,e⟩
    · exact ⟨j,i,hj,hi,e⟩
  have gap := component_pins_spaced_four hc even conn degree hp ah bh H xH xH hi hj orderPins
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp.1 xo hi
  have jp := pin_pos hp.1 xo hj
  have r1 : ¬G.Adj a (p.getVert j) := second_pin_no_start_of_high hc even conn degree hp bh xo
    (few hp xo) hi hj gap (high_in (p.getVert_mem_support (j-1)))
  have rev := reverse_long hp.1
  have ep : EdgeOptimal p.reverse := same_support_optimal hp rev (by intro z; simp)
  have ro : x∉p.reverse.support := by simpa using xo
  have rgh : 4≤G.degree (p.reverse.getVert (p.length-i-1)) := by
    apply high_in
    exact (List.mem_reverse.mp (by
      rw [←support_reverse]; exact p.reverse.getVert_mem_support _))
  have l1 : ¬G.Adj b (p.getVert i) := by
    have e := second_pin_no_start_of_high hc even conn degree ep ah ro
      (few ep ro) (reverse_pin hp.1 xo hj) (reverse_pin hp.1 xo hi) (by omega) rgh
    rw [getVert_reverse] at e
    have eq : p.length-(p.length-i)=i := by omega
    rwa [eq] at e
  let M := ({i,j-1}:Finset ℕ)
  have nr : M⊆range p.length := by
    intro z zh
    rcases mem_insert.mp zh with e|e
    · exact mem_range.mpr (by omega)
    · have nx := mem_singleton.mp e
      exact mem_range.mpr (by omega)
  have nd : Disjoint (LeftMarks p∪RightMarks p) M := by
    apply disjoint_left.mpr
    intro z zm zh
    rcases mem_insert.mp zh with e|e
    · subst z
      exact (mem_union.mp zm).elim
        (fun lm => start_not_adj_pin_successor hp.1 xo hi (mem_filter.mp lm).2)
        (fun rm => l1 (mem_filter.mp rm).2)
    · have eq := mem_singleton.mp e
      subst z
      exact (mem_union.mp zm).elim
        (fun lm => r1 (by
          have h := (mem_filter.mp lm).2
          have eq : j-1+1=j := by omega
          rwa [eq] at h))
        (fun rm => end_not_adj_pin_predecessor hp.1 xo hj (mem_filter.mp rm).2)
  have mc : M.card=2 := by
    rw [show M=({i,j-1}:Finset ℕ) from rfl,card_insert_of_not_mem
      (show i∉({j-1}:Finset ℕ) from fun h => by have e := mem_singleton.mp h; omega),card_singleton]
  have strong := mark_length hp.1 xo yp' xy M nr nd
  rw [mc] at strong
  have op : 0<O.card := card_pos.mpr ⟨x,mem_sdiff.mpr ⟨mem_univ _,fun e => xo (List.mem_toFinset.mp e)⟩⟩
  omega

#print axioms traceable_of_order_le_eleven
end Graffiti189LongestPath.TwoCut.SmallOrderFour
