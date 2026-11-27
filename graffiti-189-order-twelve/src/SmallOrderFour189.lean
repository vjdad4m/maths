import NoPairs189
import TinyFourOrder12189
import Mathlib.Tactic.NormNum
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
    have lower := componentPins_card hp.1 H 2 conn
    have sub : componentPins H ⊆ G.neighborFinset x := by
      intro z hz
      obtain ⟨_,u,hu,e⟩ := mem_filter.mp hz
      have ux : u=x := only (H.off u hu)
      subst u
      exact (mem_neighborFinset G x z).mpr e
    have upper := card_le_card sub
    rw [card_neighborFinset_eq_degree] at upper
    exact lower.trans upper
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

theorem order_twelve_shape (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤12)
    (fail : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support) :
    ∃ a b x : V, ∃ p : G.Walk a b, EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      p.length=10 ∧ x∉p.support ∧ (∀ z,z∉p.support → z=x) := by
  classical
  have ord : Fintype.card V=12 := by
    by_contra h
    exact fail (traceable_of_order_le_eleven hc even conn degree (by omega))
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
  simp only [card_empty,Nat.add_zero] at lower
  have not_three : O.card≠3 := by
    intro three
    have len : p.length=8 := by omega
    obtain ⟨r,rO,s,sO,rs⟩ := one_lt_card.mp (show 1<O.card by omega)
    obtain ⟨z,zO,zh⟩ : ∃ z,z∈O ∧ 4≤G.degree z := by
      rcases degree r s rs with h|h
      · exact ⟨r,rO,h⟩
      · exact ⟨s,sO,h⟩
    have zo : z∉p.support := fun h => (mem_sdiff.mp zO).2 (List.mem_toFinset.mpr h)
    have pn := few hp zo
    have db := degree_off_bound hp.1 zo
    change G.degree z≤(Pins p z).card+O.card-1 at db
    obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp (show 1<(Pins p z).card by omega)
    obtain ⟨i,j,hi,hj,ij⟩ : ∃ i j, i∈Pins p z ∧ j∈Pins p z ∧ i<j := by
      rcases lt_or_gt_of_ne ne with h|h
      · exact ⟨i,j,hi,hj,h⟩
      · exact ⟨j,i,hj,hi,h⟩
    obtain ⟨T,zT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component zo
    let Q : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
    have gap := component_pins_spaced_four hc even conn degree hp ah bh Q zT zT hi hj ij
    have il := (pin_data hi).1
    have jl := (pin_data hj).1
    have ip := pin_pos hp.1 zo hi
    have ends_ne : p.getVert (j-1) ≠ p.getVert (i+1) := by
      intro h
      have e := hp.1.1.getVert_injOn (show j-1≤p.length by omega)
        (show i+1≤p.length by omega) h
      omega
    rcases degree _ _ ends_ne with hh|hh
    · have banned := second_pin_no_start_of_high hc even conn degree hp bh zo pn hi hj gap hh
      have disj : Disjoint (LeftMarks p∪RightMarks p) ({j-1}:Finset ℕ) := by
        apply disjoint_left.mpr
        intro v vm vv
        have eq := mem_singleton.mp vv
        subst v
        exact (mem_union.mp vm).elim
          (fun lm => banned (by
            have h := (mem_filter.mp lm).2
            have eq : j-1+1=j := by omega
            rwa [eq] at h))
          (fun rm => end_not_adj_pin_predecessor hp.1 zo hj (mem_filter.mp rm).2)
      have bd := mark_length hp.1 xo yp' xy {j-1} (singleton_subset_iff.mpr (mem_range.mpr (by omega))) disj
      simp at bd
      omega
    · have rev := reverse_long hp.1
      have ep : EdgeOptimal p.reverse := same_support_optimal hp rev (by intro z; simp)
      have ro : z∉p.reverse.support := by simpa using zo
      have rgh : 4≤G.degree (p.reverse.getVert (p.length-i-1)) := by
        rw [getVert_reverse,show p.length-(p.length-i-1)=i+1 by omega]
        exact hh
      have banned : ¬G.Adj b (p.getVert i) := by
        have e := second_pin_no_start_of_high hc even conn degree ep ah ro
          (few ep ro) (reverse_pin hp.1 zo hj) (reverse_pin hp.1 zo hi) (by omega) rgh
        rw [getVert_reverse,show p.length-(p.length-i)=i by omega] at e
        exact e
      have disj : Disjoint (LeftMarks p∪RightMarks p) ({i}:Finset ℕ) := by
        apply disjoint_left.mpr
        intro v vm vv
        have eq := mem_singleton.mp vv
        subst v
        exact (mem_union.mp vm).elim
          (fun lm => start_not_adj_pin_successor hp.1 zo hi (mem_filter.mp lm).2)
          (fun rm => banned (mem_filter.mp rm).2)
      have bd := mark_length hp.1 xo yp' xy {i} (singleton_subset_iff.mpr (mem_range.mpr il)) disj
      simp at bd
      omega
  have low {z : V} (zo : z∉p.support) : ¬4≤G.degree z := by
    have f := few hp zo
    have bd := degree_off_bound hp.1 zo
    change G.degree z≤(Pins p z).card+O.card-1 at bd
    omega
  have only {z : V} (zo : z∉p.support) : z=x :=
    Classical.byContradiction (fun e => (degree z x e).elim (low zo) (low xo))
  have Oeq : O={x} := by
    ext z
    simp only [O,mem_sdiff,mem_univ,true_and,List.mem_toFinset,mem_singleton]
    exact ⟨only,fun e => e.symm ▸ xo⟩
  rw [Oeq,card_singleton] at cardO
  exact ⟨a,b,x,p,hp,ah,bh,by omega,xo,fun _ => only⟩
#print axioms order_twelve_shape
theorem order_twelve_normal_marks (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤12)
    (fail : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support) :
    ∃ a b x : V, ∃ p : G.Walk a b, EdgeOptimal p ∧ p.length=10 ∧ x∉p.support ∧
      (∀ z,z∉p.support → z=x) ∧ (∀ z∈p.support, 4≤G.degree z) ∧
      Pins p x={1,9} ∧ DistanceTwo G x=FlankVertices p x ∧
      FlankIndices p x={0,2,8,10} ∧
      ¬G.Adj a (p.getVert 9) ∧ ¬G.Adj b (p.getVert 1) ∧
      (LeftMarks p ∪ RightMarks p) ∪ ({1,8}:Finset ℕ) = range 10 ∧
      (LeftMarks p).card=4 ∧ (RightMarks p).card=4 := by
  classical
  obtain ⟨a,b,x,p,hp,ah,bh,len,xo,only⟩ := order_twelve_shape hc even conn degree order fail
  obtain ⟨S,xS,Sne,Soff,Sclosed,Sjoined⟩ := exists_omitted_component xo
  let H : OmittedComponent p := ⟨S,Sne,Soff,Sclosed,Sjoined⟩
  have xH : x∈H.vertices := xS
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few {a b : V} {q : G.Walk a b} (hq : EdgeOptimal q) {z : V} (zo : z∉q.support) :
      (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hq zo).1
  let O := (univ : Finset V)\p.support.toFinset
  have Oeq : O={x} := by
    ext z
    simp only [O,mem_sdiff,mem_univ,true_and,List.mem_toFinset,mem_singleton]
    exact ⟨fun o => only z o,fun e => e.symm ▸ xo⟩
  have low : ¬4≤G.degree x := by
    have f := few hp xo
    have d := degree_off_bound hp.1 xo
    change G.degree x≤(Pins p x).card+O.card-1 at d
    rw [Oeq,card_singleton] at d
    omega
  have high_in {z : V} (zp : z∈p.support) : 4≤G.degree z :=
    (degree z x (fun e => xo (e ▸ zp))).resolve_right low
  have xl : 2≤G.degree x := by
    have lower := componentPins_card hp.1 H 2 conn
    have sub : componentPins H ⊆ G.neighborFinset x := by
      intro z hz
      obtain ⟨_,u,hu,e⟩ := mem_filter.mp hz
      have ux : u=x := only u (H.off u hu)
      subst u
      exact (mem_neighborFinset G x z).mpr e
    have upper := card_le_card sub
    rw [card_neighborFinset_eq_degree] at upper
    exact lower.trans upper
  have xcard : 1<(G.neighborFinset x).card := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨r,rn,s,sn,rs⟩ := one_lt_card.mp xcard
  have onpath (y : V) (xy : G.Adj x y) : y∈p.support :=
    Classical.byContradiction (fun o => xy.ne (only y o).symm)
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
  have pm := (pin_data hi).2
  have pp := p.getVert_mem_support i
  have strong := mark_length hp.1 xo pp pm M nr nd
  rw [mc] at strong
  have dh : G.degree a=4 ∧ G.degree b=4 := by omega
  obtain ⟨f,fi⟩ := two_flanks_full hp.1 hc xo (few hp xo) (cap x) hi hj gap
  have contact_a {k : ℕ} (hk : k∈Pins p x) (e : G.Adj a (p.getVert k)) : i=1 := by
    have nae : x≠a := fun e => xo (e.symm ▸ p.start_mem_support)
    have ax : a∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae (no_endpoints hp.1 xo).1 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have t0 : t=0 := hp.1.1.getVert_injOn tr (Nat.zero_le _) (ta.trans p.getVert_zero.symm)
    rcases cases with h|h|h|h <;> omega
  have contact_b {k : ℕ} (hk : k∈Pins p x) (e : G.Adj b (p.getVert k)) : j+1=p.length := by
    have nae : x≠b := fun e => xo (e.symm ▸ p.end_mem_support)
    have ax : b∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae (no_endpoints hp.1 xo).2 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have te : t=p.length := hp.1.1.getVert_injOn tr (Nat.le_refl _) (ta.trans p.getVert_length.symm)
    rcases cases with h|h|h|h <;> omega
  have no_extra {z : ℕ} (zr : z<p.length) (zne : z≠i ∧ z≠j-1)
      (za : ¬G.Adj a (p.getVert (z+1))) (zb : ¬G.Adj b (p.getVert z)) : False := by
    have sub : insert z M ⊆ range p.length := insert_subset (mem_range.mpr zr) nr
    have disj : Disjoint (LeftMarks p∪RightMarks p) (insert z M) := by
      apply disjoint_left.mpr
      intro k km kh
      rcases mem_insert.mp kh with e|e
      · subst k
        exact (mem_union.mp km).elim (fun h => za (mem_filter.mp h).2)
          (fun h => zb (mem_filter.mp h).2)
      · exact disjoint_left.mp nd km e
    have cd : (insert z M).card=3 := by
      rw [card_insert_of_not_mem (by simpa [M] using zne),mc]
    have h := mark_length hp.1 xo pp pm (insert z M) sub disj
    rw [cd] at h
    omega
  have ii : i=1 := by
    by_cases hi' : i=1
    · exact hi'
    exfalso
    apply no_extra (z:=i-1) (by omega) (by omega)
    · rw [show i-1+1=i by omega]
      exact fun e => hi' (contact_a hi e)
    · exact end_not_adj_pin_predecessor hp.1 xo hi
  have jj : j=9 := by
    by_cases hj' : j=9
    · exact hj'
    exfalso
    apply no_extra (z:=j) (by omega) (by omega)
    · exact start_not_adj_pin_successor hp.1 xo hj
    · exact fun e => hj' (by have h := contact_b hj e; omega)
  subst i
  subst j
  have pin_eq : Pins p x=({1,9}:Finset ℕ) := (eq_of_subset_of_card_le
    (show ({1,9}:Finset ℕ)⊆Pins p x from fun k hk =>
      (mem_insert.mp hk).elim (fun e => e.symm ▸ hi) (fun e => (mem_singleton.mp e).symm ▸ hj))
    (by simpa using few hp xo)).symm
  have disj : Disjoint (LeftMarks p) (RightMarks p) := disjoint_left.mpr (by
    intro j jl jr
    exact not_adj_both_end_marks hp.1 xo pp pm (mem_range.mp (mem_filter.mp jl).1)
      (mem_filter.mp jl).2 (mem_filter.mp jr).2)
  have cdL := card_leftMarks hp.1
  have cdR := card_rightMarks hp.1
  have cu : ((LeftMarks p∪RightMarks p)∪M).card=10 := by
    rw [card_union_of_disjoint nd,card_union_of_disjoint disj,cdL,cdR,mc]
    omega
  have us : (LeftMarks p∪RightMarks p)∪M⊆range 10 := by
    rw [←len]
    apply union_subset _ nr
    exact union_subset (filter_subset _ _) (filter_subset _ _)
  have ueq := eq_of_subset_of_card_le us (by rw [cu,card_range])
  exact ⟨a,b,x,p,hp,len,xo,only,fun _ => high_in,pin_eq,f,by simpa using fi,r1,l1,
    ueq,cdL.trans dh.1,cdR.trans dh.2⟩

set_option linter.unnecessarySimpa false in
open FourOrder12 in
set_option maxHeartbeats 250000 in
theorem traceable_of_order_le_twelve (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤12) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_contra fail
  obtain ⟨a,b,x,p,hp,len,xo,only,high,pins,dt,fl,r1,l1,marks,mL,mR⟩ :=
    order_twelve_normal_marks hc even conn degree order fail
  let φ (u : Fin 12) : V := if u.val=11 then x else p.getVert u.val
  have inj : Function.Injective φ := by
    intro i j h
    by_cases li : i.val=11 <;> by_cases lj : j.val=11
    · exact Fin.ext (li.trans lj.symm)
    · simp only [φ,if_pos li,if_neg lj] at h
      exact False.elim (xo (h.symm ▸ p.getVert_mem_support j.val))
    · simp only [φ,if_neg li,if_pos lj] at h
      exact False.elim (xo (h ▸ p.getVert_mem_support i.val))
    · apply Fin.ext
      exact hp.1.1.getVert_injOn (show i.val≤p.length by omega) (show j.val≤p.length by omega)
        (by simpa only [φ,if_neg li,if_neg lj] using h)
  have onto : Function.Surjective φ := by
    intro z
    by_cases h : z∈p.support
    · obtain ⟨i,iv,ir⟩ := mem_support_iff_exists_getVert.mp h
      exact ⟨⟨i,by omega⟩,by simpa [φ,show i≠11 by omega] using iv⟩
    · exact ⟨11,by simpa [φ] using (only z h).symm⟩
  have p1 : 1∈Pins p x := by rw [pins]; simp
  have p9 : 9∈Pins p x := by rw [pins]; simp
  have px1 := (pin_data p1).2
  have px9 := (pin_data p9).2
  have near (z : V) (hz : G.Adj x z) : z=p.getVert 1 ∨ z=p.getVert 9 := by
    have on : z∈p.support := Classical.byContradiction (fun o => hz.ne (only z o).symm)
    obtain ⟨i,pi,ie⟩ := pin_of_neighbor_mem hp.1 xo on hz
    rw [pins,mem_insert,mem_singleton] at pi
    rcases pi with h|h <;> subst i
    · exact Or.inl ie.symm
    · exact Or.inr ie.symm
  have short (i : ℕ) (hi : i<10) : G.Adj (p.getVert i) (p.getVert (i+1)) :=
    p.adj_getVert_succ (by omega)
  have zer : p.getVert 0=a := p.getVert_zero
  have ten : p.getVert 10=b := by simpa only [len] using p.getVert_length
  have ab : ¬G.Adj a b := by
    intro e
    have ar : 9<p.length := by omega
    have ea : G.Adj a (p.getVert (9+1)) := by simpa only [ten] using e
    have eb : G.Adj b (p.getVert 9) := by simpa only [ten] using (short 9 (by decide)).symm
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support 1) px1 ar ea eb
  have lzero : 0∈LeftMarks p :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa only [zer] using short 0 (by decide)⟩
  have rnine : 9∈RightMarks p :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa only [ten] using (short 9 (by decide)).symm⟩
  have disj : Disjoint (LeftMarks p) (RightMarks p) := disjoint_left.mpr (by
    intro j jl jr
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support 1) px1
      (mem_range.mp (mem_filter.mp jl).1) (mem_filter.mp jl).2 (mem_filter.mp jr).2)
  have lholes : 1∉LeftMarks p ∧ 8∉LeftMarks p ∧ 9∉LeftMarks p := by
    exact ⟨fun h => start_not_adj_pin_successor hp.1 xo p1 (mem_filter.mp h).2,
      fun h => r1 (mem_filter.mp h).2,fun h => disjoint_left.mp disj h rnine⟩
  have rholes : 0∉RightMarks p ∧ 1∉RightMarks p ∧ 8∉RightMarks p := by
    exact ⟨fun h => disjoint_left.mp disj lzero h,fun h => l1 (mem_filter.mp h).2,
      fun h => end_not_adj_pin_predecessor hp.1 xo p9 (mem_filter.mp h).2⟩
  have cover {j : ℕ} (lo : 2≤j) (hi : j≤7) : j∈LeftMarks p ∨ j∈RightMarks p := by
    have hj : j∈range 10 := mem_range.mpr (by omega)
    rw [←marks] at hj
    rcases mem_union.mp hj with hh|hh
    · exact mem_union.mp hh
    · simp only [mem_insert,mem_singleton] at hh
      omega
  have complementary {j : ℕ} (lo : 2≤j) (hi : j≤7) : j∈RightMarks p ↔ j∉LeftMarks p := by
    exact ⟨fun h e => disjoint_left.mp disj e h,fun h => (cover lo hi).resolve_left h⟩
  let m : Bits := fun i => decide (i.val+2∈LeftMarks p)
  let e := decide (G.Adj (p.getVert 1) (p.getVert 9))
  let f := decide (G.Adj (p.getVert 1) (p.getVert 8))
  let g := decide (G.Adj (p.getVert 2) (p.getVert 9))
  have left : (univ.filter fun i : Fin 6 => m i=true).card=3 := by
    let L : Finset (Fin 6) := univ.filter fun i : Fin 6 => m i=true
    have eq : L.image (fun i => i.val+2)=(LeftMarks p).erase 0 := by
      ext j
      constructor
      · intro h
        obtain ⟨i,im,ii⟩ := mem_image.mp h
        have il : i.val+2∈LeftMarks p := of_decide_eq_true (mem_filter.mp im).2
        exact mem_erase.mpr ⟨by omega,ii ▸ il⟩
      · intro jh
        obtain ⟨jn,jm⟩ := mem_erase.mp jh
        have jl := mem_range.mp (mem_filter.mp jm).1
        have a : j≠1 := fun q => lholes.1 (q ▸ jm)
        have b : j≠8 := fun q => lholes.2.1 (q ▸ jm)
        have c : j≠9 := fun q => lholes.2.2 (q ▸ jm)
        refine mem_image.mpr ⟨⟨j-2,by omega⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,by change j-2+2=j; omega⟩
        exact decide_eq_true (by simpa only [show j-2+2=j by omega] using jm)
    have c := congrArg Finset.card eq
    rw [card_image_of_injective _ (show Function.Injective (fun i : Fin 6 => i.val+2) by
      intro i j h; apply Fin.ext; change i.val+2=j.val+2 at h; omega),card_erase_of_mem lzero,mL] at c
    exact c
  have from_pin {i j : ℕ} (il : i≤10) (jl : j≤10) (hi : i=1 ∨ i=9)
      (hed : G.Adj (p.getVert i) (p.getVert j)) : j=0 ∨ j=1 ∨ j=2 ∨ j=8 ∨ j=9 ∨ j=10 := by
    by_cases nh : j=0 ∨ j=1 ∨ j=2 ∨ j=8 ∨ j=9 ∨ j=10
    · exact nh
    exfalso
    have nj : ¬G.Adj x (p.getVert j) := by
      intro h
      rcases near _ h with h|h
      · have eq := hp.1.1.getVert_injOn (show j≤p.length by omega) (show 1≤p.length by omega) h
        tauto
      · have eq := hp.1.1.getVert_injOn (show j≤p.length by omega) (show 9≤p.length by omega) h
        tauto
    have pi : G.Adj x (p.getVert i) := by rcases hi with a|a <;> subst i <;> assumption
    have dd : p.getVert j∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc (fun h => xo (h.symm ▸ p.getVert_mem_support j)) nj pi hed)
    rw [dt] at dd
    obtain ⟨t,tf,tj⟩ := mem_image.mp dd
    rw [fl] at tf
    have tp : t=0 ∨ t=2 ∨ t=8 ∨ t=10 := by simpa using tf
    have tj' := hp.1.1.getVert_injOn (show t≤p.length by rcases tp with k|k|k|k <;> omega)
      (show j≤p.length by omega) tj
    omega

  have φpath {i : Fin 12} (hi : i.val≤10) : φ i=p.getVert i.val := by simp [φ,show i.val≠11 by omega]
  have forward (u v : Fin 12) (h : dir m e f g u v=true) : G.Adj (φ u) (φ v) := by
    simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with (((((h|h)|h)|h)|h)|h)|h
    · rw [φpath (by omega : u.val≤10),φpath h.2,h.1]
      exact short _ (by omega)
    · have vl : v.val=11 := h.2
      have ul : u.val≤10 := by rcases h.1 with k|k <;> omega
      simp only [φ,if_pos vl,if_neg (show u.val≠11 by omega)]
      rcases h.1 with k|k
      · rw [k]; exact px1.symm
      · rw [k]; exact px9.symm
    · split at h
      next q =>
        rw [φpath (by omega : u.val≤10),φpath (by omega : v.val≤10),q.1,zer]
        have mm := of_decide_eq_true h
        have adj := (mem_filter.mp mm).2
        rwa [show v.val-3+2+1=v.val by omega] at adj
      next => simp at h
    · split at h
      next q =>
        rw [φpath (by omega : u.val≤10),φpath (by omega : v.val≤10),q.1,ten]
        have mr : u.val∉LeftMarks p := by
          intro hm
          have mm : m ⟨u.val-2,by omega⟩=true := by
            exact decide_eq_true (by simpa only [show u.val-2+2=u.val by omega] using hm)
          simp [mm] at h
        exact ((mem_filter.mp ((complementary q.2.1 q.2.2).mpr mr)).2).symm
      next => simp at h
    · rw [φpath (by omega : u.val≤10),φpath (by omega : v.val≤10),h.1.1,h.1.2]
      exact of_decide_eq_true h.2
    · rw [φpath (by omega : u.val≤10),φpath (by omega : v.val≤10),h.1.1,h.1.2]
      exact of_decide_eq_true h.2
    · rw [φpath (by omega : u.val≤10),φpath (by omega : v.val≤10),h.1.1,h.1.2]
      exact of_decide_eq_true h.2
  have edges (u v : Fin 12) (h : edge m e f g u v=true) : G.Adj (φ u) (φ v) :=
    (show dir m e f g u v=true ∨ dir m e f g v u=true by
      simpa only [edge,Bool.or_eq_true] using h).elim (forward u v) (fun h => G.symm (forward v u h))
  have φ0 : φ 0=a := zer
  have φ1 : φ 1=p.getVert 1 := rfl
  have φ2 : φ 2=p.getVert 2 := rfl
  have φ8 : φ 8=p.getVert 8 := rfl
  have φ9 : φ 9=p.getVert 9 := rfl
  have φ10 : φ 10=b := ten
  have φ11 : φ 11=x := rfl
  have c9 : (9 : Fin 12).val=9 := rfl
  have c10 : (10 : Fin 12).val=10 := rfl
  have ad0 (v : Fin 12) (adj : G.Adj (φ 0) (φ v)) : edge m e f g 0 v=true := by
    have vno : v.val≠11 := fun h => (no_endpoints hp.1 xo).1 (by
      simpa only [φ0,φ,if_pos h] using adj.symm)
    have vlt : v.val≤10 := by omega
    rw [φ0,φpath vlt] at adj
    have v0 : v.val≠0 := fun h => G.loopless a (by simpa [h,zer] using adj)
    have v2 : v.val≠2 := fun h => start_not_adj_pin_successor hp.1 xo p1 (by simpa [h] using adj)
    have v9 : v.val≠9 := fun h => r1 (by simpa [h] using adj)
    have v10 : v.val≠10 := fun h => ab (by simpa [h,ten] using adj)
    simp only [edge,Bool.or_eq_true]
    left
    by_cases q : v.val=1
    · norm_num [dir,c9,c10,Fin.val_natCast,q]
    · have ran : 3≤v.val ∧ v.val≤8 := by omega
      have i : v.val-1∈LeftMarks p :=
        mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [show v.val-1+1=v.val by omega]⟩
      have br : m ⟨v.val-3,by omega⟩=true :=
        decide_eq_true (by simpa only [show v.val-3+2=v.val-1 by omega] using i)
      norm_num [dir,c9,c10,Fin.val_natCast,ran.1,ran.2,br]
  have ad10 (v : Fin 12) (adj : G.Adj (φ 10) (φ v)) : edge m e f g 10 v=true := by
    have vno : v.val≠11 := fun h => (no_endpoints hp.1 xo).2 (by
      simpa only [φ10,φ,if_pos h] using adj.symm)
    have vlt : v.val≤10 := by omega
    rw [φ10,φpath vlt] at adj
    have v0 : v.val≠0 := fun h => ab (by simpa [h,zer] using adj.symm)
    have v1 : v.val≠1 := fun h => l1 (by simpa [h] using adj)
    have v8 : v.val≠8 := fun h => end_not_adj_pin_predecessor hp.1 xo p9 (by simpa [h] using adj)
    have v10 : v.val≠10 := fun h => G.loopless b (by simpa [h,ten] using adj)
    simp only [edge,Bool.or_eq_true]
    right
    by_cases q : v.val=9
    · norm_num [dir,c9,c10,Fin.val_natCast,q]
    · have ran : 2≤v.val ∧ v.val≤7 := by omega
      have ii : v.val∈RightMarks p := mem_filter.mpr ⟨mem_range.mpr (by omega),adj⟩
      have br : m ⟨v.val-2,by omega⟩=false := decide_eq_false (by
        simpa only [show v.val-2+2=v.val by omega] using (complementary ran.1 ran.2).mp ii)
      norm_num [dir,c9,c10,Fin.val_natCast,ran.1,ran.2,br]
  have ad1 (v : Fin 12) (adj : G.Adj (φ 1) (φ v)) : edge m e f g 1 v=true := by
    by_cases isx : v.val=11
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,isx]
    have hv : v.val≤10 := by omega
    rw [φ1,φpath hv] at adj
    rcases from_pin (i:=1) (j:=v.val) (by decide) hv (.inl rfl) adj with q|q|q|q|q|q
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,q]
    · exact (G.loopless (p.getVert 1) (by simpa [q] using adj)).elim
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,q]
    · have fe : f=true := decide_eq_true (by simpa [q] using adj)
      norm_num [edge,dir,c9,c10,Fin.val_natCast,q,fe]
    · have ee : e=true := decide_eq_true (by simpa [q] using adj)
      norm_num [edge,dir,c9,c10,Fin.val_natCast,q,ee]
    · exact (l1 (by simpa [q,ten] using adj.symm)).elim
  have ad9 (v : Fin 12) (adj : G.Adj (φ 9) (φ v)) : edge m e f g 9 v=true := by
    by_cases isx : v.val=11
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,isx]
    have hv : v.val≤10 := by omega
    rw [φ9,φpath hv] at adj
    rcases from_pin (i:=9) (j:=v.val) (by decide) hv (.inr rfl) adj with q|q|q|q|q|q
    · exact (r1 (by simpa [q,zer] using adj.symm)).elim
    · have ee : e=true := decide_eq_true (by simpa [q] using adj.symm)
      norm_num [edge,dir,c9,c10,Fin.val_natCast,q,ee]
    · have ge : g=true := decide_eq_true (by simpa [q] using adj.symm)
      norm_num [edge,dir,c9,c10,Fin.val_natCast,q,ge]
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,q]
    · exact (G.loopless (p.getVert 9) (by simpa [q] using adj)).elim
    · norm_num [edge,dir,c9,c10,Fin.val_natCast,q]
  have centers u (hu : u∈({0,1,9,10}:Finset (Fin 12))) v (adj : G.Adj (φ u) (φ v)) :
      edge m e f g u v=true := by
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with qt|qt|qt|qt <;> subst u
    · exact ad0 v adj
    · exact ad1 v adj
    · exact ad9 v adj
    · exact ad10 v adj
  have optionals : (e || f)=true ∧ (e || g)=true := by
    constructor
    · by_cases h : (e || f)=true
      · exact h
      exfalso
      have he : e=false := by
        have q : (e || f)=false := Bool.eq_false_of_not_eq_true h
        simp only [Bool.or_eq_false_iff] at q
        exact q.1
      have hf : f=false := by
        have q : (e || f)=false := Bool.eq_false_of_not_eq_true h
        simp only [Bool.or_eq_false_iff] at q
        exact q.2
      have sub : G.neighborFinset (φ 1) ⊆ ({φ 0,φ 2,φ 11}:Finset V) := by
        intro y hy
        obtain ⟨v,rfl⟩ := onto y
        by_cases ev : v.val=11
        · have ev' : v=(11:Fin 12) := Fin.ext ev
          subst v
          simp
        · have vlt : v.val≤10 := by omega
          have adj := (mem_neighborFinset G _ _).mp hy
          rw [φ1,φpath vlt] at adj
          rcases from_pin (i:=1) (j:=v.val) (by decide) vlt (.inl rfl) adj with r|r|r|r|r|r
          · have e' : v=(0:Fin 12) := Fin.ext r
            subst v
            simp
          · exact (G.loopless _ (by rw [r] at adj; exact adj)).elim
          · have e' : v=(2:Fin 12) := Fin.ext r
            subst v
            simp
          · have h' : f=true := decide_eq_true (by rwa [r] at adj)
            simp [hf] at h'
          · have h' : e=true := decide_eq_true (by rwa [r] at adj)
            simp [he] at h'
          · exact (l1 (by simpa [r,ten] using adj.symm)).elim
      have cd := card_le_card sub
      rw [card_neighborFinset_eq_degree,φ1] at cd
      have bd : ({φ 0,φ 2,φ 11}:Finset V).card≤3 := by
        have e1 := card_insert_le (φ 0) ({φ 2,φ 11}:Finset V)
        have e2 := card_insert_le (φ 2) ({φ 11}:Finset V)
        simp only [card_singleton] at e2
        omega
      have hh := high _ (p.getVert_mem_support 1)
      omega
    · by_cases h : (e || g)=true
      · exact h
      exfalso
      have he : e=false := by
        have q : (e || g)=false := Bool.eq_false_of_not_eq_true h
        simp only [Bool.or_eq_false_iff] at q
        exact q.1
      have hg : g=false := by
        have q : (e || g)=false := Bool.eq_false_of_not_eq_true h
        simp only [Bool.or_eq_false_iff] at q
        exact q.2
      have sub : G.neighborFinset (φ 9) ⊆ ({φ 8,φ 10,φ 11}:Finset V) := by
        intro y hy
        obtain ⟨v,rfl⟩ := onto y
        by_cases ev : v.val=11
        · have ev' : v=(11:Fin 12) := Fin.ext ev
          subst v
          simp
        · have vlt : v.val≤10 := by omega
          have adj := (mem_neighborFinset G _ _).mp hy
          rw [φ9,φpath vlt] at adj
          rcases from_pin (i:=9) (j:=v.val) (by decide) vlt (.inr rfl) adj with r|r|r|r|r|r
          · exact (r1 (by simpa [r,zer] using adj.symm)).elim
          · have h' : e=true := decide_eq_true (by simpa only [r] using adj.symm)
            simp [he] at h'
          · have h' : g=true := decide_eq_true (by simpa only [r] using adj.symm)
            simp [hg] at h'
          · have e' : v=(8:Fin 12) := Fin.ext r
            subst v
            simp
          · exact (G.loopless _ (by rw [r] at adj; exact adj)).elim
          · have e' : v=(10:Fin 12) := Fin.ext r
            subst v
            simp
      have cd := card_le_card sub
      rw [card_neighborFinset_eq_degree,φ9] at cd
      have bd : ({φ 8,φ 10,φ 11}:Finset V).card≤3 := by
        have e1 := card_insert_le (φ 8) ({φ 10,φ 11}:Finset V)
        have e2 := card_insert_le (φ 10) ({φ 11}:Finset V)
        simp only [card_singleton] at e2
        omega
      have hh := high _ (p.getVert_mem_support 9)
      omega
  exact fail (FourOrder12.lift hc (fun z => distanceTwo_le_of_even 4 z (even z))
    m e f g φ inj onto left optionals.1 optionals.2 edges centers)

#print axioms traceable_of_order_le_twelve

#print axioms order_twelve_normal_marks
end Graffiti189LongestPath.TwoCut.SmallOrderFour
