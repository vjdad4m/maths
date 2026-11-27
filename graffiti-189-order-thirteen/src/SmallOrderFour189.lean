import TinyFourOrder13189
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



/-- The two standard exposure positions; a high rotated endpoint makes one an empty mark. -/
private theorem two_pin_hole_dichotomy
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (xo : x∉p.support)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (4≤G.degree (p.getVert (j-1)) → j-1∉LeftMarks p∪RightMarks p) ∧
    (4≤G.degree (p.getVert (i+1)) → i∉LeftMarks p∪RightMarks p) ∧
    (j-1∉LeftMarks p∪RightMarks p ∨ i∉LeftMarks p∪RightMarks p) := by
  classical
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few {a b : V} {q : G.Walk a b} (hq : EdgeOptimal q) {z : V} (zo : z∉q.support) :
      (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hq zo).1
  have positive := pin_pos hp.1 xo hi
  have jl := (pin_data hj).1
  have left (hh : 4≤G.degree (p.getVert (j-1))) : j-1∉LeftMarks p∪RightMarks p := by
    have ban := second_pin_no_start_of_high hc even conn degree hp bh xo (few hp xo) hi hj gap hh
    intro hm
    rcases mem_union.mp hm with h|h
    · exact ban (by
        have g := (mem_filter.mp h).2
        rwa [show j-1+1=j by omega] at g)
    · exact end_not_adj_pin_predecessor hp.1 xo hj (mem_filter.mp h).2
  have right (hh : 4≤G.degree (p.getVert (i+1))) : i∉LeftMarks p∪RightMarks p := by
    have ep : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
    have ro : x∉p.reverse.support := by simpa using xo
    have rgh : 4≤G.degree (p.reverse.getVert (p.length-i-1)) := by
      rw [getVert_reverse,show p.length-(p.length-i-1)=i+1 by omega]
      exact hh
    have ban : ¬G.Adj b (p.getVert i) := by
      have e := second_pin_no_start_of_high hc even conn degree ep ah ro
        (few ep ro) (reverse_pin hp.1 xo hj) (reverse_pin hp.1 xo hi) (by omega) rgh
      rwa [getVert_reverse,show p.length-(p.length-i)=i by omega] at e
    intro hm
    exact (mem_union.mp hm).elim
      (fun h => start_not_adj_pin_successor hp.1 xo hi (mem_filter.mp h).2)
      (fun h => ban (mem_filter.mp h).2)
  have ne : p.getVert (j-1)≠p.getVert (i+1) := by
    intro e
    have h := hp.1.1.getVert_injOn (show j-1≤p.length by omega) (show i+1≤p.length by omega) e
    omega
  exact ⟨left,right,(degree _ _ ne).imp left right⟩


private theorem at_most_one_hole
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yp : y∈p.support) (xy : G.Adj x y)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length≤9)
    {i j : ℕ} (ir : i<p.length) (jr : j<p.length)
    (ih : i∉LeftMarks p∪RightMarks p) (jh : j∉LeftMarks p∪RightMarks p) :
    i=j := by
  by_cases eq : i=j
  · exact eq
  exfalso
  have sub : ({i,j}:Finset ℕ)⊆range p.length := by
    intro z zm
    rcases mem_insert.mp zm with h|h
    · exact mem_range.mpr (h.symm ▸ ir)
    · exact mem_range.mpr ((mem_singleton.mp h).symm ▸ jr)
  have disj : Disjoint (LeftMarks p∪RightMarks p) ({i,j}:Finset ℕ) := by
    apply disjoint_left.mpr
    intro k km kh
    rcases mem_insert.mp kh with h|h
    · exact ih (h ▸ km)
    · exact jh ((mem_singleton.mp h) ▸ km)
  have bd := mark_length hp xo yp xy {i,j} sub disj
  rw [card_insert_of_not_mem (by simpa using eq),card_singleton] at bd
  omega

private theorem no_holes_when_length_eight
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yp : y∈p.support) (xy : G.Adj x y)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length≤8)
    {i : ℕ} (ir : i<p.length) :
    i∈LeftMarks p∪RightMarks p := by
  by_contra h
  have disj : Disjoint (LeftMarks p∪RightMarks p) ({i}:Finset ℕ) := by
    apply disjoint_left.mpr
    intro k km kh
    exact h ((mem_singleton.mp kh) ▸ km)
  have bd := mark_length hp xo yp xy {i} (singleton_subset_iff.mpr (mem_range.mpr ir)) disj
  rw [card_singleton] at bd
  omega


private theorem off_neighbors_complete_of_tight
    {a b x z : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (zo : z∉p.support) (ne : z≠x)
    (tight : (Pins p x).card + ((univ : Finset V)\p.support.toFinset).card-1 ≤ G.degree x) :
    G.Adj x z := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have xO : x∈O := mem_sdiff.mpr ⟨mem_univ _,fun e => xo (List.mem_toFinset.mp e)⟩
  have zO : z∈O := mem_sdiff.mpr ⟨mem_univ _,fun e => zo (List.mem_toFinset.mp e)⟩
  have sub : G.neighborFinset x ⊆ PinVertices p x∪O.erase x := by
    intro y yn
    have xy := (mem_neighborFinset G x y).mp yn
    by_cases yp : y∈p.support
    · obtain ⟨i,hi,e⟩ := pin_of_neighbor_mem hp xo yp xy
      exact mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,e⟩))
    · exact mem_union.mpr (.inr (mem_erase.mpr
        ⟨xy.ne.symm,mem_sdiff.mpr ⟨mem_univ _,fun e => yp (List.mem_toFinset.mp e)⟩⟩))
  have cb := card_union_le (PinVertices p x) (O.erase x)
  rw [card_erase_of_mem xO,card_pinVertices hp] at cb
  have op : 0<O.card := card_pos.mpr ⟨x,xO⟩
  change (Pins p x).card + O.card-1 ≤ G.degree x at tight
  have bd : (PinVertices p x∪O.erase x).card≤(G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  have eq := eq_of_subset_of_card_le sub bd
  exact (mem_neighborFinset G x z).mp (eq ▸ mem_union.mpr (.inr (mem_erase.mpr ⟨ne,zO⟩)))

private theorem pins_gap_at_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j) :
    i+3≤j := by
  obtain ⟨T,xT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component xo
  let H : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
  exact component_pins_spaced_four hc even conn degree hp ah bh H xT xT hi hj ij


private theorem pin_two_contacts_end
    {a b x : V} {p : G.Walk a b}
    (hp : IsLongest p) (hc : G.Connected) (xo : x∉p.support)
    (F2 : (Pins p x).card≤2) (cap : (DistanceTwo G x).card≤4)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (∀ k∈Pins p x,G.Adj a (p.getVert k) → i=1) ∧
      (∀ k∈Pins p x,G.Adj b (p.getVert k) → j+1=p.length) := by
  obtain ⟨f,fi⟩ := two_flanks_full hp hc xo F2 cap hi hj gap
  have ip := pin_pos hp xo hi
  have jl := (pin_data hj).1
  have no := no_endpoints hp xo
  constructor
  · intro k hk e
    have nae : x≠a := fun e => xo (e.symm ▸ p.start_mem_support)
    have ax : a∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae no.1 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have t0 : t=0 := hp.1.getVert_injOn tr (Nat.zero_le _) (ta.trans p.getVert_zero.symm)
    rcases cases with h|h|h|h <;> omega
  · intro k hk e
    have nae : x≠b := fun e => xo (e.symm ▸ p.end_mem_support)
    have ax : b∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae no.2 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have te : t=p.length := hp.1.getVert_injOn tr (Nat.le_refl _) (ta.trans p.getVert_length.symm)
    rcases cases with h|h|h|h <;> omega


private theorem common_off_three_pins_oriented
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=9) (off : ((univ : Finset V)\p.support.toFinset).card=3)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j)
    (low : ¬4≤G.degree (p.getVert (j-1))) :
    (∀ z∉p.support, Pins p z={1,8}) ∧
      (∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ∧
      G.Adj a (p.getVert 7) := by
  classical
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo hi hj ij
  have ip := pin_pos hp.1 xo hi
  have jl := (pin_data hj).1
  have il := (pin_data hi).1
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few {z : V} (zo : z∉p.support) : (Pins p z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp zo).1
  have onlow : p.getVert (j-1)∈p.support := p.getVert_mem_support _
  have high {z : V} (zo : z∉p.support) : 4≤G.degree z :=
    (degree z _ (fun e => zo (e ▸ onlow))).resolve_right low
  have disx := two_pin_hole_dichotomy hc even conn degree hp ah bh xo hi hj gap
  have hole (zr : i<p.length) (m : i∉LeftMarks p∪RightMarks p) {k : ℕ}
      (kr : k<p.length) (ne : k≠i) : k∈LeftMarks p∪RightMarks p := by
    by_contra no
    exact ne (at_most_one_hole hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 ah bh
      (by omega) kr zr no m)
  have inoth : i∉LeftMarks p∪RightMarks p := by
    rcases disx.2.2 with h|h
    · by_cases inside : i∈LeftMarks p∪RightMarks p
      · have iHi : 4≤G.degree (p.getVert (i+1)) := by
          apply (degree _ (p.getVert (j-1)) _).resolve_right low
          intro e
          have q := hp.1.1.getVert_injOn (show i+1≤p.length by omega) (show j-1≤p.length by omega) e
          omega
        exact (disx.2.1 iHi inside).elim
      · exact inside
    · exact h
  have eqhole {k} (kr : k<p.length) (hm : k∉LeftMarks p∪RightMarks p) : k=i :=
    at_most_one_hole hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 ah bh (by omega)
      kr il hm inoth
  have union_jm := hole il inoth (show j-1<p.length by omega) (by omega)
  have union_j := hole il inoth jl (by omega)
  have first : G.Adj a (p.getVert j) := by
    have marked := (mem_union.mp union_jm).resolve_right
      (fun m => end_not_adj_pin_predecessor hp.1 xo hj (mem_filter.mp m).2)
    have e := (mem_filter.mp marked).2
    rwa [show j-1+1=j by omega] at e
  have second : G.Adj b (p.getVert j) := by
    have marked := (mem_union.mp union_j).resolve_left
      (fun m => start_not_adj_pin_successor hp.1 xo hj (mem_filter.mp m).2)
    exact (mem_filter.mp marked).2
  obtain ⟨left,right⟩ := pin_two_contacts_end hp.1 hc xo (few xo) (cap x) hi hj gap
  have ie : i=1 := left j hj first
  have je : j=8 := by have h := right j hj second; omega
  have pins {z : V} (zo : z∉p.support) : Pins p z={1,8} := by
    have bd := degree_off_bound hp.1 zo
    rw [off] at bd
    have zh := high zo
    obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp (show 1<(Pins p z).card by omega)
    obtain ⟨u,v,hu,hv,uv⟩ : ∃ u v,u∈Pins p z ∧ v∈Pins p z ∧ u<v := by
      rcases lt_or_gt_of_ne uv with h|h
      · exact ⟨u,v,hu,hv,h⟩
      · exact ⟨v,u,hv,hu,h⟩
    have gg := pins_gap_at_four hc even conn degree hp ah bh zo hu hv uv
    have ul := (pin_data hu).1
    have vl := (pin_data hv).1
    obtain ⟨lh,rh,either⟩ := two_pin_hole_dichotomy hc even conn degree hp ah bh zo hu hv gg
    have uv' : u=i ∧ v=j := by
      rcases either with lm|rm
      · have ev := eqhole (show v-1<p.length by omega) lm
        omega
      · have eu := eqhole ul rm
        have lo : ¬4≤G.degree (p.getVert (v-1)) := by
          intro hh
          have ev := eqhole (show v-1<p.length by omega) (lh hh)
          omega
        have eq : p.getVert (v-1)=p.getVert (j-1) := Classical.byContradiction (fun ne =>
          (degree _ _ ne).elim lo low)
        have q := hp.1.1.getVert_injOn (show v-1≤p.length by omega) (show j-1≤p.length by omega) eq
        omega
    have sub : ({1,8}:Finset ℕ)⊆Pins p z := by
      intro k km
      rcases mem_insert.mp km with e|e
      · exact (uv'.1.trans ie |>.trans e.symm) ▸ hu
      · exact (uv'.2.trans je |>.trans (mem_singleton.mp e).symm) ▸ hv
    exact (eq_of_subset_of_card_le sub (by simpa using few zo)).symm
  have clique {z w : V} (zo : z∉p.support) (wo : w∉p.support) (ne : z≠w) : G.Adj z w := by
    apply off_neighbors_complete_of_tight hp.1 zo wo ne.symm
    rw [off,pins zo]
    simpa using high zo
  have ap8 : G.Adj a (p.getVert 8) := je ▸ first
  have ap1 : G.Adj a (p.getVert 1) := by
    simpa using p.adj_getVert_succ (i:=0) (by omega)
  have a2 : ¬G.Adj a (p.getVert 2) := by
    have pm : 1∈Pins p x := by rw [pins xo]; simp
    exact start_not_adj_pin_successor hp.1 xo pm
  have ap7 : G.Adj a (p.getVert 7) := by
    by_contra no7
    let O := (univ : Finset V)\p.support.toFinset
    let S := insert (p.getVert 2) (insert (p.getVert 7) O)
    have d2left : p.getVert 2∈DistanceTwo G a := by
      apply mem_distanceTwo.mpr
      exact dist_two hc (fun h => by
        have e := hp.1.1.getVert_injOn (show 0≤p.length by omega) (show 2≤p.length by omega)
          (p.getVert_zero.trans h)
        omega) a2 ap1 (p.adj_getVert_succ (i:=1) (by omega))
    have d2right : p.getVert 7∈DistanceTwo G a := by
      apply mem_distanceTwo.mpr
      exact dist_two hc (fun h => by
        have e := hp.1.1.getVert_injOn (show 0≤p.length by omega) (show 7≤p.length by omega)
          (p.getVert_zero.trans h)
        omega) no7 ap8 (p.adj_getVert_succ (i:=7) (by omega)).symm
    have sub : S⊆DistanceTwo G a := by
      intro z zs
      rcases mem_insert.mp zs with h|h
      · rwa [h]
      rcases mem_insert.mp h with h|h
      · rwa [h]
      have zo : z∉p.support := fun e => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr e)
      have one : 1∈Pins p z := by rw [pins zo]; simp
      exact mem_distanceTwo.mpr (dist_two hc (fun e => zo (e.symm ▸ p.start_mem_support))
        (fun e => (no_endpoints hp.1 zo).1 e.symm) ap1 (pin_data one).2.symm)
    have f7 : p.getVert 7∉O := fun h => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr (p.getVert_mem_support 7))
    have f2 : p.getVert 2∉insert (p.getVert 7) O := by
      intro h
      rcases mem_insert.mp h with h|h
      · have e := hp.1.1.getVert_injOn (show 2≤p.length by omega) (show 7≤p.length by omega) h
        omega
      · exact (mem_sdiff.mp h).2 (List.mem_toFinset.mpr (p.getVert_mem_support 2))
    have c := card_le_card sub
    rw [show S=insert (p.getVert 2) (insert (p.getVert 7) O) from rfl,
      card_insert_of_not_mem f2,card_insert_of_not_mem f7,show O.card=3 from off] at c
    have cb := cap a
    omega
  exact ⟨fun _ => pins,fun _ zo _ wo => clique zo wo,ap7⟩


private theorem hamilton_of_labeled_chain {n : ℕ} (φ : Fin n→V)
    [Nonempty V] (inj : Function.Injective φ) (onto : Function.Surjective φ)
    (l : List (Fin n)) (nd : l.Nodup) (all : ∀ i, i∈l)
    (chain : List.Chain' (fun i j => G.Adj (φ i) (φ j)) l) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ x,x∈p.support := by
  have make (a : V) (L : List V) (adj : List.Chain' G.Adj (a::L)) :
      ∃ b,∃ p : G.Walk a b,p.support=a::L := by
    induction L generalizing a with
    | nil => exact ⟨a,.nil,rfl⟩
    | cons b L ih =>
      obtain ⟨c,p,eq⟩ := ih b adj.tail
      exact ⟨c,.cons adj.rel_head p,by simp [eq]⟩
  have nl : (l.map φ).Nodup := nd.map inj
  have ml (x : V) : x∈l.map φ := by
    obtain ⟨i,rfl⟩ := onto x
    exact List.mem_map.mpr ⟨i,all i,rfl⟩
  have cl : List.Chain' G.Adj (l.map φ) := List.chain'_map_of_chain' φ (fun _ _ h => h) chain
  cases e : l.map φ with
  | nil =>
    -- The graph has a vertex in all intended applications.
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    have h := ml x
    simp [e] at h
  | cons a l =>
    rw [e] at cl nl
    obtain ⟨b,p,eq⟩ := make a l cl
    exact ⟨a,b,p,IsPath.mk' (eq.symm ▸ nl),fun x => by rw [eq,←e]; exact ml x⟩


private theorem close_off_three_oriented
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=9) (off : ((univ : Finset V)\p.support.toFinset).card=3)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j)
    (low : ¬4≤G.degree (p.getVert (j-1))) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  obtain ⟨pins,clique,chord⟩ := common_off_three_pins_oriented hc even conn degree hp ah bh len off xo hi hj ij low
  let O := (univ : Finset V)\p.support.toFinset
  obtain ⟨u,v,w,uv,uw,vw,oo⟩ := card_eq_three.mp (show O.card=3 from off)
  have out {z : V} : z∈O ↔ z∉p.support := by
    simp [O]
  have uo : u∉p.support := out.mp (by simp [oo])
  have vo : v∉p.support := out.mp (by simp [oo])
  have wo : w∉p.support := out.mp (by simp [oo])
  have r1 : 1∈Pins p w := by rw [pins w wo]; simp
  have r8 : 8∈Pins p u := by rw [pins u uo]; simp
  let L : List (Fin 13) := [9,8,10,11,12,1,0,7,6,5,4,3,2]
  let φ (k : Fin 13) : V := if k.val=10 then u else if k.val=11 then v else
    if k.val=12 then w else p.getVert k.val
  letI : Nonempty V := ⟨a⟩
  have value {k : Fin 13} (h : k.val≤9) : φ k=p.getVert k.val := by
    simp [φ,show k.val≠10 by omega,show k.val≠11 by omega,show k.val≠12 by omega]
  have classify (k : Fin 13) : k.val≤9 ∨ k=10 ∨ k=11 ∨ k=12 := by
    by_cases h10 : k.val=10
    · exact .inr (.inl (Fin.ext h10))
    by_cases h11 : k.val=11
    · exact .inr (.inr (.inl (Fin.ext h11)))
    by_cases h12 : k.val=12
    · exact .inr (.inr (.inr (Fin.ext h12)))
    exact .inl (by omega)
  have phi10 : φ 10=u := rfl
  have phi11 : φ 11=v := rfl
  have phi12 : φ 12=w := rfl
  have lab_inj : Function.Injective φ := by
    intro k l eq
    rcases classify k with kh|kh|kh|kh <;>
      rcases classify l with lh|lh|lh|lh
    · exact Fin.ext (hp.1.1.getVert_injOn (show k.val≤p.length by omega) (show l.val≤p.length by omega) ((value kh).symm.trans (eq.trans (value lh))))
    all_goals try subst k
    all_goals try subst l
    all_goals try rfl
    all_goals try rw [value kh] at eq
    all_goals try rw [value lh] at eq
    all_goals simp only [phi10,phi11,phi12] at eq
    all_goals exfalso
    all_goals first | exact uv eq | exact uv eq.symm | exact uw eq | exact uw eq.symm | exact vw eq | exact vw eq.symm | exact uo (eq ▸ p.getVert_mem_support _) | exact vo (eq ▸ p.getVert_mem_support _) | exact wo (eq ▸ p.getVert_mem_support _)
  have lab_sur : Function.Surjective φ := by
    intro z
    by_cases on : z∈p.support
    · obtain ⟨k,e,kl⟩ := mem_support_iff_exists_getVert.mp on
      exact ⟨⟨k,by omega⟩,(value (show k≤9 by omega)).trans e⟩
    · have member := out.mpr on
      rw [oo,mem_insert,mem_insert,mem_singleton] at member
      rcases member with r|r|r <;> subst z
      · exact ⟨10,rfl⟩
      · exact ⟨11,rfl⟩
      · exact ⟨12,rfl⟩
  apply hamilton_of_labeled_chain φ lab_inj lab_sur L (by decide) (by intro k; fin_cases k <;> decide)
  have line (k : ℕ) (h : k<9) :
      G.Adj (p.getVert (k+1)) (p.getVert k) := (p.adj_getVert_succ (by omega)).symm
  have at0 : p.getVert 0=a := p.getVert_zero
  have pin81 := (pin_data r8).2.symm
  have pin11 := (pin_data r1).2
  have l0 := line 0 (by decide)
  have l2 := line 2 (by decide)
  have l3 := line 3 (by decide)
  have l4 := line 4 (by decide)
  have l5 := line 5 (by decide)
  have l6 := line 6 (by decide)
  have l8 := line 8 (by decide)
  have uc := clique u uo v vo uv
  have vc := clique v vo w wo vw
  have cc : G.Adj (p.getVert 0) (p.getVert 7) := at0.symm ▸ chord
  have aa : G.Adj (p.getVert 1) a := by simpa using l0
  have cl : List.Chain' G.Adj
    [p.getVert 9,p.getVert 8,u,v,w,p.getVert 1,p.getVert 0,p.getVert 7,
      p.getVert 6,p.getVert 5,p.getVert 4,p.getVert 3,p.getVert 2] := by
    simp [List.chain'_cons,l8,pin81,uc,vc,pin11,l0,cc,aa,chord,l6,l5,l4,l3,l2]
  simp only [L,List.chain'_cons,List.chain'_singleton] at *
  exact cl


theorem traceable_if_three_off_order_thirteen
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=9) (off : ((univ : Finset V)\p.support.toFinset).card=3) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have oc : O.card=3 := off
  obtain ⟨r,hr,s,hs,ne⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨x,xO,xh⟩ : ∃ x,x∈O ∧ 4≤G.degree x := by
    rcases degree r s ne with dh|dh
    · exact ⟨r,hr,dh⟩
    · exact ⟨s,hs,dh⟩
  have xo : x∉p.support := fun e => (mem_sdiff.mp xO).2 (List.mem_toFinset.mpr e)
  have bd := degree_off_bound hp.1 xo
  rw [off] at bd
  obtain ⟨i,hi,j,hj,ij⟩ := one_lt_card.mp (show 1<(Pins p x).card by omega)
  obtain ⟨i,j,hi,hj,ij⟩ : ∃ i j,i∈Pins p x ∧ j∈Pins p x ∧ i<j := by
    rcases lt_or_gt_of_ne ij with e|e
    · exact ⟨i,j,hi,hj,e⟩
    · exact ⟨j,i,hj,hi,e⟩
  by_cases lo : 4≤G.degree (p.getVert (j-1))
  · have gap := pins_gap_at_four hc even conn degree hp ah bh xo hi hj ij
    have il := (pin_data hi).1
    have jl := (pin_data hj).1
    obtain ⟨fh,sh,_⟩ := two_pin_hole_dichotomy hc even conn degree hp ah bh xo hi hj gap
    have rlo : ¬4≤G.degree (p.getVert (i+1)) := by
      intro uh
      have eq := at_most_one_hole hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 ah bh (by omega)
        (show j-1<p.length by omega) il (fh lo) (sh uh)
      omega
    have ep : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
    have rev_eq : p.reverse.support.toFinset=p.support.toFinset := by
      ext z
      simp
    have one := reverse_pin hp.1 xo hj
    have two := reverse_pin hp.1 xo hi
    have rlh : ¬4≤G.degree (p.reverse.getVert (p.length-i-1)) := by
      rw [getVert_reverse,show p.length-(p.length-i-1)=i+1 by omega]
      exact rlo
    exact close_off_three_oriented hc even conn degree ep bh ah (by simpa using len)
      (by rwa [rev_eq]) (by simpa using xo) one two (by omega) rlh
  · exact close_off_three_oriented hc even conn degree hp ah bh len off xo hi hj ij lo

#print axioms traceable_if_three_off_order_thirteen



private theorem four_off_clique_ports
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=8) (off : ((univ : Finset V)\p.support.toFinset).card=4) :
    (∀ x∉p.support,(Pins p x).card≤1) ∧
    (∀ x∉p.support, 4≤G.degree x → (Pins p x).card=1) ∧
    (∀ x∉p.support, ∀ y∉p.support, x≠y → G.Adj x y) ∧
    (∀ x∉p.support,∀ i∈Pins p x,G.Adj a (p.getVert i) ∧ G.Adj b (p.getVert i)) := by
  classical
  have mark_all {z : V} (zo : z∉p.support) {i k : ℕ} (hi : i∈Pins p z)
      (kr : k<p.length) : k∈LeftMarks p∪RightMarks p :=
    no_holes_when_length_eight hp.1 zo (p.getVert_mem_support i) (pin_data hi).2 ah bh len.le kr
  have few {z : V} (zo : z∉p.support) : (Pins p z).card≤1 := by
    by_contra! h
    obtain ⟨i,hi,j,hj,ij⟩ := one_lt_card.mp h
    obtain ⟨i,j,hi,hj,ij⟩ : ∃ i j,i∈Pins p z ∧ j∈Pins p z ∧ i<j := by
      rcases lt_or_gt_of_ne ij with e|e
      · exact ⟨i,j,hi,hj,e⟩
      · exact ⟨j,i,hj,hi,e⟩
    have gap := pins_gap_at_four hc even conn degree hp ah bh zo hi hj ij
    have jl := (pin_data hj).1
    rcases (two_pin_hole_dichotomy hc even conn degree hp ah bh zo hi hj gap).2.2 with l|r
    · exact l (mark_all zo hi (show j-1<p.length by omega))
    · exact r (mark_all zo hi (pin_data hi).1)
  have one {x : V} (xo : x∉p.support) (xh : 4≤G.degree x) : (Pins p x).card=1 := by
    have lo := degree_off_bound hp.1 xo
    rw [off] at lo
    have all := few xo
    omega
  have complete {x y : V} (xo : x∉p.support) (yo : y∉p.support)
     (ne : x≠y) (xh : 4≤G.degree x) : G.Adj x y := by
    apply off_neighbors_complete_of_tight hp.1 xo yo ne.symm
    rw [off,one xo xh]
    exact xh
  refine ⟨fun _ => few,fun _ => one,?_,?_⟩
  · intro x xo y yo ne
    exact (degree x y ne).elim (complete xo yo ne) (fun yh => (complete yo xo ne.symm yh).symm)
  · intro z zo i hi
    have ip := pin_pos hp.1 zo hi
    have il := (pin_data hi).1
    have one := mark_all zo hi il
    have two := mark_all zo hi (show i-1<p.length by omega)
    constructor
    · have h := (mem_union.mp two).resolve_right
        (fun m => end_not_adj_pin_predecessor hp.1 zo hi (mem_filter.mp m).2)
      have e := (mem_filter.mp h).2
      rwa [show i-1+1=i by omega] at e
    · exact (mem_filter.mp ((mem_union.mp one).resolve_left
        (fun m => start_not_adj_pin_successor hp.1 zo hi (mem_filter.mp m).2))).2


private theorem four_off_only_end_ports
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=8) (off : ((univ : Finset V)\p.support.toFinset).card=4) :
    (∀ x∉p.support, ∀ i∈Pins p x, i=1 ∨ i=7) ∧
      (∃ x∉p.support,1∈Pins p x) ∧ (∃ x∉p.support,7∈Pins p x) := by
  classical
  obtain ⟨few,one,clique,ends⟩ := four_off_clique_ports hc even conn degree hp ah bh len off
  have same {x : V} (xo : x∉p.support) (H : OmittedComponent p) (xH : x∈H.vertices) :
      ∀ y∉p.support,y∈H.vertices := by
    intro y yo
    by_contra yn
    have xy : x≠y := fun e => yn (e ▸ xH)
    exact yo (H.closed x xH y yn (clique x xo y yo xy))
  have two {x : V} (xo : x∉p.support) {i : ℕ} (hi : i∈Pins p x) :
      ∃ y∉p.support,∃ j∈Pins p y, j≠i ∧ (i+3≤j ∨ j+3≤i) := by
    obtain ⟨T,xT,ne,out,cl,jn⟩ := exists_omitted_component xo
    let H : OmittedComponent p := ⟨T,ne,out,cl,jn⟩
    have low := componentPins_card hp.1 H 2 conn
    have own : p.getVert i∈componentPins H :=
      mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),x,xT,(pin_data hi).2⟩
    have ex : ∃ y∈componentPins H, y≠p.getVert i := by
      by_contra no
      have sub : componentPins H ⊆ {p.getVert i} := by
        intro y hy
        exact mem_singleton.mpr (Classical.byContradiction (fun n => no ⟨y,hy,n⟩))
      have u := card_le_card sub
      rw [card_singleton] at u
      omega
    obtain ⟨y,ym,yn⟩ := ex
    obtain ⟨yp,z,zH,zy⟩ := mem_filter.mp ym
    have zo := H.off z zH
    obtain ⟨j,hj,jy⟩ := pin_of_neighbor_mem hp.1 zo (List.mem_toFinset.mp yp) zy
    have ij : j≠i := fun e => yn (jy.symm.trans (congrArg p.getVert e))
    have gap : i+3≤j ∨ j+3≤i := by
      rcases lt_or_gt_of_ne ij with lt|lt
      · exact .inr (component_pins_spaced_four hc even conn degree hp ah bh H zH xT hj hi lt)
      · exact .inl (component_pins_spaced_four hc even conn degree hp ah bh H xT zH hi hj lt)
    exact ⟨z,zo,j,hj,ij,gap⟩
  have restrict {x : V} (xo : x∉p.support) {i : ℕ} (hi : i∈Pins p x) : i=1 ∨ i=7 := by
    by_cases now : i=1 ∨ i=7
    · exact now
    exfalso
    have ip := pin_pos hp.1 xo hi
    have il := (pin_data hi).1
    obtain ⟨y,yo,j,hj,jn,gap⟩ := two xo hi
    have jp := pin_pos hp.1 yo hj
    have jl := (pin_data hj).1
    have j_not : j∉Pins p x := by
      intro hm
      have low := one_lt_card.mpr ⟨j,hm,i,hi,jn⟩
      have up := few x xo
      omega
    have no_j : ¬G.Adj x (p.getVert j) := by
      intro e
      exact j_not (mem_filter.mpr ⟨mem_range.mpr jl,e⟩)
    have xy : x≠y := fun e => j_not (e.symm ▸ hj)
    have p2_j : p.getVert j∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc
      (fun e => xo (e.symm ▸ p.getVert_mem_support j)) no_j (clique x xo y yo xy) (pin_data hj).2)
    have en := ends x xo i hi
    have p2_a : a∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc
      (fun e => xo (e.symm ▸ p.start_mem_support)) (no_endpoints hp.1 xo).1 (pin_data hi).2 en.1.symm)
    have p2_b : b∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc
      (fun e => xo (e.symm ▸ p.end_mem_support)) (no_endpoints hp.1 xo).2 (pin_data hi).2 en.2.symm)
    have p2_left : p.getVert (i-1)∈DistanceTwo G x := by
      apply (mem_sdiff.mp (flanks_outside_boundary hc hp.1 xo _)).1
      apply mem_image.mpr
      exact ⟨i-1,mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩
    have p2_right : p.getVert (i+1)∈DistanceTwo G x := by
      apply (mem_sdiff.mp (flanks_outside_boundary hc hp.1 xo _)).1
      apply mem_image.mpr
      exact ⟨i+1,mem_union.mpr (.inr (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩
    let S : Finset ℕ := {0,8,i-1,i+1,j}
    have step_b : p.getVert 8=b := by simpa only [len] using p.getVert_length
    have small {k : ℕ} (h : k∈S) : k≤p.length := by
      simp only [S,mem_insert,mem_singleton] at h
      rcases h with h|h|h|h|h <;> omega
    have sub : S.image p.getVert ⊆ DistanceTwo G x := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      simp only [S,mem_insert,mem_singleton] at hk
      rcases hk with e|e|e|e|e <;> subst k
      · simpa only [getVert_zero] using p2_a
      · simpa only [step_b] using p2_b
      · exact p2_left
      · exact p2_right
      · exact p2_j
    have inj : (S.image p.getVert).card=S.card := card_image_iff.mpr
      (fun _ iu _ iv h => hp.1.1.getVert_injOn (small iu) (small iv) h)
    have cd : S.card=5 := by
      have n0 : 0∉({8,i-1,i+1,j}:Finset ℕ) := by
        simp only [mem_insert,mem_singleton]; omega
      have n8 : 8∉({i-1,i+1,j}:Finset ℕ) := by
        simp only [mem_insert,mem_singleton]; omega
      have nl : i-1∉({i+1,j}:Finset ℕ) := by
        simp only [mem_insert,mem_singleton]; omega
      have nr : i+1∉({j}:Finset ℕ) := by
        simp only [mem_singleton]; omega
      rw [show S=({0,8,i-1,i+1,j}:Finset ℕ) from rfl,card_insert_of_not_mem n0,
        card_insert_of_not_mem n8,card_insert_of_not_mem nl,card_insert_of_not_mem nr,card_singleton]
    have c := card_le_card sub
    rw [inj,cd] at c
    have cb := distanceTwo_le_of_even 4 x (even x)
    omega
  have init : ∃ x∉p.support,∃ i∈Pins p x, True := by
    let O := (univ : Finset V)\p.support.toFinset
    have oc : O.card=4 := off
    obtain ⟨r,hr,s,hs,ne⟩ := one_lt_card.mp (show 1<O.card by omega)
    obtain ⟨x,xO,xh⟩ : ∃ x,x∈O ∧ 4≤G.degree x := by
      rcases degree r s ne with dh|dh
      · exact ⟨r,hr,dh⟩
      · exact ⟨s,hs,dh⟩
    have xo : x∉p.support := fun e => (mem_sdiff.mp xO).2 (List.mem_toFinset.mpr e)
    obtain ⟨i,hi⟩ := card_pos.mp (show 0<(Pins p x).card by rw [one x xo xh]; decide)
    exact ⟨x,xo,i,hi,trivial⟩
  obtain ⟨x,xo,i,hi,_⟩ := init
  obtain ⟨y,yo,j,hj,jn,_⟩ := two xo hi
  refine ⟨fun _ xo _ hi => restrict xo hi,?_⟩
  rcases restrict xo hi with ie|ie
  · have je : j=7 := (restrict yo hj).resolve_left (fun e => jn (e.trans ie.symm))
    exact ⟨⟨x,xo,ie ▸ hi⟩,⟨y,yo,je ▸ hj⟩⟩
  · have je : j=1 := (restrict yo hj).resolve_right (fun e => jn (e.trans ie.symm))
    exact ⟨⟨y,yo,je ▸ hj⟩,⟨x,xo,ie ▸ hi⟩⟩


private theorem four_off_splice_chord
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=8) (off : ((univ : Finset V)\p.support.toFinset).card=4) :
    G.Adj a (p.getVert 6) := by
  classical
  obtain ⟨few,one,clique,ends⟩ := four_off_clique_ports hc even conn degree hp ah bh len off
  obtain ⟨_,⟨u,uo,u1⟩,⟨v,vo,v7⟩⟩ := four_off_only_end_ports hc even conn degree hp ah bh len off
  by_cases adj : G.Adj a (p.getVert 6)
  · exact adj
  exfalso
  let O := (univ : Finset V)\p.support.toFinset
  have oc : O.card=4 := off
  let good := O.filter (fun z=>4≤G.degree z)
  let bad := O.filter (fun z=>¬4≤G.degree z)
  have bd : bad.card≤1 := by
    by_contra! h
    obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp h
    exact (degree x y ne).elim (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have gc : 3≤good.card := by
    have eq : good.card+bad.card=O.card := filter_card_add_filter_neg_card_eq_card _
    omega
  have ap1 := (ends u uo 1 u1).1
  have ap7 := (ends v vo 7 v7).1
  have a2 : ¬G.Adj a (p.getVert 2) := start_not_adj_pin_successor hp.1 uo u1
  have step_ne {i : ℕ} (il : i≤p.length) (ip : 0<i) : a≠p.getVert i := by
    intro e
    have h := hp.1.1.getVert_injOn (Nat.zero_le _) il (p.getVert_zero.trans e)
    omega
  have d2two : p.getVert 2∈DistanceTwo G a := mem_distanceTwo.mpr
    (dist_two hc (step_ne (i:=2) (by omega) (by decide)) a2 ap1
      (p.adj_getVert_succ (i:=1) (by omega)))
  have d2six : p.getVert 6∈DistanceTwo G a := mem_distanceTwo.mpr
    (dist_two hc (step_ne (i:=6) (by omega) (by decide)) adj ap7
      (p.adj_getVert_succ (i:=6) (by omega)).symm)
  have sub : insert (p.getVert 2) (insert (p.getVert 6) good) ⊆ DistanceTwo G a := by
    intro z zh
    rcases mem_insert.mp zh with zz|zz
    · rwa [zz]
    rcases mem_insert.mp zz with zz|zz
    · rwa [zz]
    have zo : z∉p.support := fun h => (mem_sdiff.mp (mem_filter.mp zz).1).2 (List.mem_toFinset.mpr h)
    have high := (mem_filter.mp zz).2
    obtain ⟨i,hi⟩ := card_pos.mp (show 0<(Pins p z).card by rw [one z zo high]; decide)
    exact mem_distanceTwo.mpr (dist_two hc (fun e => zo (e ▸ p.start_mem_support))
      (fun e => (no_endpoints hp.1 zo).1 e.symm) (ends z zo i hi).1 (pin_data hi).2.symm)
  have good_not {n : ℕ} : p.getVert n∉good := by
    intro e
    exact (mem_sdiff.mp (mem_filter.mp e).1).2 (List.mem_toFinset.mpr (p.getVert_mem_support n))
  have n2 : p.getVert 2∉insert (p.getVert 6) good := by
    intro h
    rcases mem_insert.mp h with e|e
    · have ij := hp.1.1.getVert_injOn (show 2≤p.length by omega) (show 6≤p.length by omega) e
      omega
    · exact good_not e
  have c := card_le_card sub
  rw [card_insert_of_not_mem n2,card_insert_of_not_mem (good_not (n:=6))] at c
  have cap := distanceTwo_le_of_even 4 a (even a)
  omega


theorem traceable_if_four_off_order_thirteen
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=8) (off : ((univ : Finset V)\p.support.toFinset).card=4) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  obtain ⟨few,_,clique,ends⟩ := four_off_clique_ports hc even conn degree hp ah bh len off
  obtain ⟨_,⟨w,wo,r1⟩,⟨u,uo,r7⟩⟩ := four_off_only_end_ports hc even conn degree hp ah bh len off
  have une : u≠w := by
    intro e
    subst w
    have lo := one_lt_card.mpr ⟨1,r1,7,r7,by decide⟩
    have up := few u uo
    omega
  have chord := four_off_splice_chord hc even conn degree hp ah bh len off
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have uO := out.mpr uo
  have wO := out.mpr wo
  have wE : w∈O.erase u := mem_erase.mpr ⟨une.symm,wO⟩
  have ec : ((O.erase u).erase w).card=2 := by
    rw [card_erase_of_mem wE,card_erase_of_mem uO,show O.card=4 from off]
  obtain ⟨v,t,vt,oo⟩ := card_eq_two.mp ec
  have vm : v∈(O.erase u).erase w := by simp [oo]
  have tm : t∈(O.erase u).erase w := by simp [oo]
  have vn := mem_erase.mp vm
  have tn := mem_erase.mp tm
  have vn' := mem_erase.mp vn.2
  have tn' := mem_erase.mp tn.2
  have vo := out.mp vn'.2
  have toff := out.mp tn'.2
  let L : List (Fin 13) := [8,7,9,10,11,12,1,0,6,5,4,3,2]
  let φ (k : Fin 13) : V := if k.val=9 then u else if k.val=10 then v else
    if k.val=11 then t else if k.val=12 then w else p.getVert k.val
  letI : Nonempty V := ⟨a⟩
  have value {k : Fin 13} (h : k.val≤8) : φ k=p.getVert k.val := by
    simp [φ,show k.val≠9 by omega,show k.val≠10 by omega,show k.val≠11 by omega,show k.val≠12 by omega]
  have classify (k : Fin 13) : k.val≤8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 := by
    by_cases h9 : k.val=9
    · exact .inr (.inl (Fin.ext h9))
    by_cases h10 : k.val=10
    · exact .inr (.inr (.inl (Fin.ext h10)))
    by_cases h11 : k.val=11
    · exact .inr (.inr (.inr (.inl (Fin.ext h11))))
    by_cases h12 : k.val=12
    · exact .inr (.inr (.inr (.inr (Fin.ext h12))))
    exact .inl (by omega)
  have val9 : φ 9=u := rfl
  have val10 : φ 10=v := rfl
  have val11 : φ 11=t := rfl
  have val12 : φ 12=w := rfl
  have lab_inj : Function.Injective φ := by
    intro k l eq
    rcases classify k with kh|kh|kh|kh|kh <;>
      rcases classify l with lh|lh|lh|lh|lh
    · exact Fin.ext (hp.1.1.getVert_injOn (show k.val≤p.length by omega)
        (show l.val≤p.length by omega) ((value kh).symm.trans (eq.trans (value lh))))
    all_goals try subst k
    all_goals try subst l
    all_goals try rfl
    all_goals try rw [value kh] at eq
    all_goals try rw [value lh] at eq
    all_goals simp only [val9,val10,val11,val12] at eq
    all_goals exfalso
    all_goals first | exact une eq | exact une eq.symm | exact vt eq | exact vt eq.symm | exact vn.1 eq | exact vn.1 eq.symm | exact tn.1 eq | exact tn.1 eq.symm | exact vn'.1 eq | exact vn'.1 eq.symm | exact tn'.1 eq | exact tn'.1 eq.symm | exact uo (eq ▸ p.getVert_mem_support _) | exact vo (eq ▸ p.getVert_mem_support _) | exact toff (eq ▸ p.getVert_mem_support _) | exact wo (eq ▸ p.getVert_mem_support _)
  have lab_sur : Function.Surjective φ := by
    intro z
    by_cases on : z∈p.support
    · obtain ⟨k,e,kl⟩ := mem_support_iff_exists_getVert.mp on
      exact ⟨⟨k,by omega⟩,(value (show k≤8 by omega)).trans e⟩
    · by_cases zu : z=u
      · subst z; exact ⟨9,rfl⟩
      by_cases zw : z=w
      · subst z; exact ⟨12,rfl⟩
      have zz : z∈(O.erase u).erase w := mem_erase.mpr ⟨zw,mem_erase.mpr ⟨zu,out.mpr on⟩⟩
      rw [oo,mem_insert,mem_singleton] at zz
      rcases zz with hv|ht <;> subst z
      · exact ⟨10,rfl⟩
      · exact ⟨11,rfl⟩
  apply hamilton_of_labeled_chain φ lab_inj lab_sur L (by decide) (by intro k; fin_cases k <;> decide)
  have line (k : ℕ) (h : k<8) :
      G.Adj (p.getVert (k+1)) (p.getVert k) := (p.adj_getVert_succ (by omega)).symm
  have pin7 := (pin_data r7).2.symm
  have pin1 := (pin_data r1).2
  have l0 : G.Adj (p.getVert 1) a := by simpa using line 0 (by decide)
  have l2 := line 2 (by decide)
  have l3 := line 3 (by decide)
  have l4 := line 4 (by decide)
  have l5 := line 5 (by decide)
  have l7 := line 7 (by decide)
  have uv := clique u uo v vo vn'.1.symm
  have vv := clique v vo t toff vt
  have tw := clique t toff w wo tn.1
  have cl : List.Chain' G.Adj
    [p.getVert 8,p.getVert 7,u,v,t,w,p.getVert 1,p.getVert 0,p.getVert 6,
      p.getVert 5,p.getVert 4,p.getVert 3,p.getVert 2] := by
    simp [List.chain'_cons,l7,pin7,uv,vv,tw,pin1,l0,chord,l5,l4,l3,l2]
  simp only [L,List.chain'_cons,List.chain'_singleton] at *
  exact cl

#print axioms traceable_if_four_off_order_thirteen


theorem order_thirteen_shape (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤13)
    (fail : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support) :
    ∃ a b x : V, ∃ p : G.Walk a b, EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      p.length=11 ∧ x∉p.support ∧ (∀ z,z∉p.support → z=x) := by
  classical
  have ord : Fintype.card V=13 := by
    by_contra h
    exact fail (traceable_of_order_le_twelve hc even conn degree (by omega))
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
    intro t
    exact fail (traceable_if_three_off_order_thirteen hc even conn degree hp ah bh (by omega) t)
  have not_four : O.card≠4 := by
    intro t
    exact fail (traceable_if_four_off_order_thirteen hc even conn degree hp ah bh (by omega) t)
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
#print axioms order_thirteen_shape


private theorem order_thirteen_marks_raw (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=11) (xo : x∉p.support) (only : ∀ z,z∉p.support→z=x) :
    ∃ i j : ℕ, 0<i ∧ j<11 ∧ i+3≤j ∧
      (i=1 ∨ j=10) ∧ (∀ z∈p.support,4≤G.degree z) ∧
      Pins p x={i,j} ∧ DistanceTwo G x=FlankVertices p x ∧
      FlankIndices p x={i-1,i+1,j-1,j+1} ∧
      ¬G.Adj a (p.getVert j) ∧ ¬G.Adj b (p.getVert i) ∧
      Disjoint (LeftMarks p) (RightMarks p) ∧
      i∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p ∧
      (i≠1 → i-1∉LeftMarks p∪RightMarks p) ∧
      (j≠10 → j∉LeftMarks p∪RightMarks p) ∧
      4≤(LeftMarks p).card ∧ 4≤(RightMarks p).card := by
  classical
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
  have pin_eq : Pins p x=({i,j}:Finset ℕ) := (eq_of_subset_of_card_le
    (show ({i,j}:Finset ℕ)⊆Pins p x from fun k hk =>
      (mem_insert.mp hk).elim (fun e => e.symm ▸ hi) (fun e => (mem_singleton.mp e).symm ▸ hj))
    (by
      have ne : i∉({j}:Finset ℕ) := by
        intro e; have z := mem_singleton.mp e; omega
      simpa only [card_insert_of_not_mem ne, card_singleton] using few hp xo)).symm
  obtain ⟨f,fi⟩ := two_flanks_full hp.1 hc xo (few hp xo) (cap x) hi hj gap
  obtain ⟨left,right⟩ := pin_two_contacts_end hp.1 hc xo (few hp xo) (cap x) hi hj gap
  have mi : i∉LeftMarks p∪RightMarks p := by
    intro h
    exact disjoint_left.mp nd h (mem_insert_self _ _)
  have mj : j-1∉LeftMarks p∪RightMarks p := by
    intro h
    exact disjoint_left.mp nd h (mem_insert_of_mem (mem_singleton_self _))
  have ml : i≠1 → i-1∉LeftMarks p∪RightMarks p := by
    intro ne h
    rcases mem_union.mp h with h|h
    · have chord := (mem_filter.mp h).2
      rw [show i-1+1=i by omega] at chord
      exact ne (left i hi chord)
    · exact end_not_adj_pin_predecessor hp.1 xo hi (mem_filter.mp h).2
  have mr : j≠10 → j∉LeftMarks p∪RightMarks p := by
    intro ne h
    rcases mem_union.mp h with h|h
    · exact start_not_adj_pin_successor hp.1 xo hj (mem_filter.mp h).2
    · have e := right j hj (mem_filter.mp h).2
      omega
  have pm := (pin_data hi).2
  have pp := p.getVert_mem_support i
  have disj : Disjoint (LeftMarks p) (RightMarks p) := disjoint_left.mpr (by
    intro j jl jr
    exact not_adj_both_end_marks hp.1 xo pp pm (mem_range.mp (mem_filter.mp jl).1)
      (mem_filter.mp jl).2 (mem_filter.mp jr).2)
  have orient : i=1 ∨ j=10 := by
    by_cases ie : i=1
    · exact .inl ie
    by_cases je : j=10
    · exact .inr je
    exfalso
    let S : Finset ℕ := {i-1,i,j-1,j}
    have within : S ⊆ range p.length := by
      intro k h
      simp only [S,mem_insert,mem_singleton] at h
      exact mem_range.mpr (by rcases h with z|z|z|z <;> omega)
    have no : Disjoint (LeftMarks p∪RightMarks p) S := by
      apply disjoint_left.mpr
      intro k km hk
      simp only [S,mem_insert,mem_singleton] at hk
      rcases hk with e|e|e|e <;> subst k
      · exact ml ie km
      · exact mi km
      · exact mj km
      · exact mr je km
    have n1 : i-1∉({i,j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have n2 : i∉({j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have n3 : j-1∉({j}:Finset ℕ) := by simp only [mem_singleton]; omega
    have cd : S.card=4 := by
      rw [show S=({i-1,i,j-1,j}:Finset ℕ) from rfl,
        card_insert_of_not_mem n1,card_insert_of_not_mem n2,card_insert_of_not_mem n3,card_singleton]
    have q := mark_length hp.1 xo pp pm S within no
    omega
  exact ⟨i,j,ip,by omega,gap,orient,fun _ => high_in,pin_eq,f,fi,r1,l1,disj,mi,mj,ml,mr,
    (card_leftMarks hp.1).symm ▸ ah,(card_rightMarks hp.1).symm ▸ bh⟩


private theorem order_thirteen_normal_marks (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤13)
    (fail : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v,v∈p.support) :
    ∃ a b x : V,∃ p : G.Walk a b,∃ j : ℕ,
      EdgeOptimal p ∧ p.length=11 ∧ x∉p.support ∧ (∀ z,z∉p.support→z=x) ∧
      4≤j ∧ j≤10 ∧ (∀ z∈p.support,4≤G.degree z) ∧
      Pins p x={1,j} ∧ DistanceTwo G x=FlankVertices p x ∧
      FlankIndices p x={0,2,j-1,j+1} ∧
      ¬G.Adj a (p.getVert j) ∧ ¬G.Adj b (p.getVert 1) ∧
      Disjoint (LeftMarks p) (RightMarks p) ∧
      1∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p ∧
      (j≠10 → j∉LeftMarks p∪RightMarks p) ∧
      4≤(LeftMarks p).card ∧ 4≤(RightMarks p).card := by
  obtain ⟨a,b,x,p,hp,ah,bh,len,xo,only⟩ := order_thirteen_shape hc even conn degree order fail
  obtain ⟨i,j,ip,jl,gap,side,hi,pins,d2,fl,lj,r1,disj,no1,noj,_,mr,cl,cr⟩ :=
    order_thirteen_marks_raw hc even conn degree hp ah bh len xo only
  rcases side with rfl|jh
  · exact ⟨a,b,x,p,j,hp,len,xo,only,gap,by omega,hi,pins,d2,by simpa using fl,lj,r1,
      disj,no1,noj,mr,cl,cr⟩
  have hj : j∈Pins p x := by rw [pins]; simp
  have h1 : 1∈Pins p.reverse x := by
    have h := reverse_pin hp.1 xo hj
    rwa [show p.length-j=1 by omega] at h
  have ep : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have lr : p.reverse.length=11 := by simpa using len
  have xo' : x∉p.reverse.support := by simpa using xo
  have only' : ∀ z,z∉p.reverse.support→z=x := by simpa using only
  obtain ⟨u,v,up,vl,gg,_,hi,pp,dd,ff,lq,rq,qq,n1,nj,_,nr,na,nb⟩ :=
    order_thirteen_marks_raw hc even conn degree ep bh ah lr xo' only'
  have u1 : u=1 := by
    rw [pp,mem_insert,mem_singleton] at h1
    rcases h1 with h|h <;> omega
  subst u
  exact ⟨b,a,x,p.reverse,v,ep,lr,xo',only',gg,by omega,hi,pp,dd,by simpa using ff,lq,rq,
    qq,n1,nj,nr,na,nb⟩


private theorem n13_model_d2_upper (hc : G.Connected)
    (φ : Fin 13 → V) (inj : Function.Injective φ)
    (E : Fin 13 → Fin 13 → Bool) (z : Fin 13)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card≤4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 13,E z u=true ∧ E u y=true).card≤4 := by
  classical
  let Q := univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 13,E z u=true ∧ E u y=true
  have sub : Q.image φ ⊆ DistanceTwo G (φ z) := by
    intro y hy
    obtain ⟨v,vq,rfl⟩ := mem_image.mp hy
    obtain ⟨vne,no,w,zw,wv⟩ := (mem_filter.mp vq).2
    have ne : φ z≠φ v := fun e => vne (inj e).symm
    have no' : ¬G.Adj (φ z) (φ v) := fun e => by
      have r := rev v e
      simp [r] at no
    exact mem_distanceTwo.mpr (dist_two hc ne no' (forw z w zw) (forw w v wv))
  have c := card_le_card sub
  rw [card_image_of_injective _ inj] at c
  exact c.trans cap

private theorem n13_model_degree_lower
    (φ : Fin 13 → V) (onto : Function.Surjective φ)
    (E : Fin 13 → Fin 13 → Bool) (z : Fin 13)
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (high : 4≤G.degree (φ z)) :
    4≤(univ.filter fun y => E z y=true).card := by
  classical
  let Q := univ.filter fun y => E z y=true
  have sub : G.neighborFinset (φ z) ⊆ Q.image φ := by
    intro y hy
    obtain ⟨v,rfl⟩ := onto y
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,rev v ((mem_neighborFinset G _ _).mp hy)⟩,rfl⟩
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  exact high.trans (c.trans card_image_le)



open FourOrder13 in
set_option linter.unnecessarySimpa false in
set_option maxHeartbeats 500000 in
theorem traceable_of_order_le_thirteen (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (low : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤13) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_contra fail
  obtain ⟨a,b,x,p,j,hp,len,xo,only,jlo,jhi,high,pins,dt,fl,rj,l1,disj,n1,nj,nj',cL,cR⟩ :=
    order_thirteen_normal_marks hc even conn low order fail
  let φ (u : Fin 13) : V := if u.val=12 then x else p.getVert u.val
  have path {i : Fin 13} (hi : i.val≤11) : φ i=p.getVert i.val := by
    simp [φ,show i.val≠12 by omega]
  have inj : Function.Injective φ := by
    intro i k h
    by_cases li : i.val=12 <;> by_cases lk : k.val=12
    · exact Fin.ext (li.trans lk.symm)
    · simp only [φ,if_pos li,if_neg lk] at h
      exact False.elim (xo (h.symm ▸ p.getVert_mem_support k.val))
    · simp only [φ,if_neg li,if_pos lk] at h
      exact False.elim (xo (h ▸ p.getVert_mem_support i.val))
    · apply Fin.ext
      exact hp.1.1.getVert_injOn (show i.val≤p.length by omega) (show k.val≤p.length by omega)
        (by simpa only [φ,if_neg li,if_neg lk] using h)
  have onto : Function.Surjective φ := by
    intro z
    by_cases h : z∈p.support
    · obtain ⟨i,iv,ir⟩ := mem_support_iff_exists_getVert.mp h
      exact ⟨⟨i,by omega⟩,by simpa [φ,show i≠12 by omega] using iv⟩
    · exact ⟨12,by simpa [φ] using (only z h).symm⟩
  let J : Fin 13 := ⟨j,by omega⟩
  have pv0 : φ 0=a := p.getVert_zero
  have pv1 : φ 1=p.getVert 1 := rfl
  have pvj : φ J=p.getVert j := path (by show j≤11; omega)
  have pv11 : φ 11=b := by simpa only [len] using p.getVert_length
  have pv12 : φ 12=x := rfl
  have last : p.getVert 11=b := by simpa only [len] using p.getVert_length
  have p1 : 1∈Pins p x := by rw [pins]; simp
  have pj : j∈Pins p x := by rw [pins]; simp
  have px1 := (pin_data p1).2
  have pxj := (pin_data pj).2
  have pp {n : ℕ} (h : n<11) : G.Adj (p.getVert n) (p.getVert (n+1)) :=
    p.adj_getVert_succ (by omega)
  have ax {z : V} (hz : G.Adj x z) : z=p.getVert 1 ∨ z=p.getVert j := by
    have zp : z∈p.support := Classical.byContradiction (fun o => hz.ne (only z o).symm)
    obtain ⟨i,pi,ie⟩ := pin_of_neighbor_mem hp.1 xo zp hz
    rw [pins,mem_insert,mem_singleton] at pi
    rcases pi with h|h <;> subst i
    · exact Or.inl ie.symm
    · exact Or.inr ie.symm
  have ab : ¬G.Adj a b := by
    intro e
    have ar : 10<p.length := by omega
    have ea : G.Adj a (p.getVert (10+1)) := by simpa only [last] using e
    have eb : G.Adj b (p.getVert 10) := by simpa only [last] using (pp (n:=10) (by decide)).symm
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support 1) px1 ar ea eb
  have L0 : 0∈LeftMarks p := mem_filter.mpr ⟨mem_range.mpr (by omega),
    by simpa only [getVert_zero] using pp (n:=0) (by decide)⟩
  have R10 : 10∈RightMarks p := mem_filter.mpr ⟨mem_range.mpr (by omega),
    by simpa only [last] using (pp (n:=10) (by decide)).symm⟩
  let m : Marks := fun i => if i.val∈LeftMarks p then 1 else if i.val∈RightMarks p then 2 else 0
  have bL (i : Fin 11) : m i=1 ↔ i.val∈LeftMarks p := by
    by_cases h : i.val∈LeftMarks p <;> by_cases h' : i.val∈RightMarks p <;> simp [m,h,h']
  have bR (i : Fin 11) : m i=2 ↔ i.val∈RightMarks p := by
    by_cases h : i.val∈LeftMarks p
    · have no : i.val∉RightMarks p := fun hh => disjoint_left.mp disj h hh
      simp [m,h,no]
    · by_cases r : i.val∈RightMarks p <;> simp [m,h,r]
  have b0 {i : Fin 11} (h : i.val∉LeftMarks p∪RightMarks p) : m i=0 := by
    have nL := fun e => h (mem_union.mpr (Or.inl e))
    have nR := fun e => h (mem_union.mpr (Or.inr e))
    simp only [m,if_neg nL,if_neg nR]
  have m0 : m 0=1 := (bL 0).mpr L0
  have m10 : m 10=2 := (bR 10).mpr R10
  have m1 : m 1=0 := b0 n1
  have mkj (k : Fin 11) (hk : k.val+1=j) : m k=0 := b0 (by rwa [show k.val=j-1 by omega])
  have mj (k : Fin 11) (hk : k.val=j) (hj : j≠10) : m k=0 := b0 (by rw [hk]; exact nj' hj)
  have left : 4≤(univ.filter fun i : Fin 11 => m i=1).card := by
    let L : Finset (Fin 11) := univ.filter fun i => m i=1
    have images : L.image Fin.val=LeftMarks p := by
      ext n
      constructor
      · intro h
        obtain ⟨k,km,rfl⟩ := mem_image.mp h
        exact (bL k).mp (mem_filter.mp km).2
      · intro h
        have lim := mem_range.mp (mem_filter.mp h).1
        refine mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        exact (bL _).mpr h
    have c := congrArg Finset.card images
    rw [card_image_of_injective _ (show Function.Injective (Fin.val : Fin 11→ℕ) from fun _ _ => Fin.ext)] at c
    rw [←c] at cL
    exact cL
  have right : 4≤(univ.filter fun i : Fin 11 => m i=2).card := by
    let L : Finset (Fin 11) := univ.filter fun i => m i=2
    have images : L.image Fin.val=RightMarks p := by
      ext n
      constructor
      · intro h
        obtain ⟨k,km,rfl⟩ := mem_image.mp h
        exact (bR k).mp (mem_filter.mp km).2
      · intro h
        have lim := mem_range.mp (mem_filter.mp h).1
        refine mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        exact (bR _).mpr h
    have c := congrArg Finset.card images
    rw [card_image_of_injective _ (show Function.Injective (Fin.val : Fin 11→ℕ) from fun _ _ => Fin.ext)] at c
    rw [←c] at cR
    exact cR
  let e := decide (G.Adj (p.getVert 1) (p.getVert j))
  let f := decide (G.Adj (p.getVert 1) (p.getVert (j-1)))
  let g := decide (G.Adj (p.getVert 2) (p.getVert j))
  let h := decide (G.Adj (p.getVert 1) (p.getVert (j+1)))
  have near_pin {i k : ℕ} (il : i≤11) (kl : k≤11) (ip : i=1 ∨ i=j)
      (hed : G.Adj (p.getVert i) (p.getVert k)) :
      k=0 ∨ k=1 ∨ k=2 ∨ k=j-1 ∨ k=j ∨ k=j+1 := by
    by_cases nh : k=0 ∨ k=1 ∨ k=2 ∨ k=j-1 ∨ k=j ∨ k=j+1
    · exact nh
    exfalso
    have nk : ¬G.Adj x (p.getVert k) := by
      intro adj
      rcases ax adj with hh|hh
      · have eq := hp.1.1.getVert_injOn (show k≤p.length by omega) (show 1≤p.length by omega) hh
        tauto
      · have eq := hp.1.1.getVert_injOn (show k≤p.length by omega) (show j≤p.length by omega) hh
        tauto
    have pin : G.Adj x (p.getVert i) := by rcases ip with a|a <;> subst i <;> assumption
    have dd : p.getVert k∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc (fun e => xo (e.symm ▸ p.getVert_mem_support k)) nk pin hed)
    rw [dt] at dd
    obtain ⟨v,vf,vk⟩ := mem_image.mp dd
    rw [fl] at vf
    have vp : v=0 ∨ v=2 ∨ v=j-1 ∨ v=j+1 := by simpa using vf
    have eq := hp.1.1.getVert_injOn (show v≤p.length by rcases vp with y|y|y|y <;> omega)
      (show k≤p.length by omega) vk
    omega

  have c0 : (0 : Fin 13).val=0 := rfl
  have c1 : (1 : Fin 13).val=1 := rfl
  have c11 : (11 : Fin 13).val=11 := rfl
  have c12 : (12 : Fin 13).val=12 := rfl
  have cj : J.val=j := rfl
  have forward (u v : Fin 13) (H : dir j m e f g h u v=true) : G.Adj (φ u) (φ v) := by
    simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at H
    rcases H with ((((((H|H)|H)|H)|H)|H)|H)|H
    · rw [path (by omega : u.val≤11),path H.2,H.1]
      exact pp (by omega)
    · have vl : v.val=12 := H.2
      have ul : u.val≤11 := by rcases H.1 with k|k <;> omega
      simp only [φ,if_pos vl,if_neg (show u.val≠12 by omega)]
      rcases H.1 with k|k
      · rw [k]; exact px1.symm
      · rw [k]; exact pxj.symm
    · split at H
      next q =>
        rw [path (by omega : u.val≤11),path (by omega : v.val≤11),q.1,getVert_zero]
        have ml := (bL ⟨v.val-1,by omega⟩).mp (of_decide_eq_true H)
        have adj := (mem_filter.mp ml).2
        rwa [show v.val-1+1=v.val by omega] at adj
      next => simp at H
    · split at H
      next q =>
        rw [path (by omega : u.val≤11),path (by omega : v.val≤11),q.1,last]
        have mr := (bR ⟨u.val,q.2⟩).mp (of_decide_eq_true H)
        exact (mem_filter.mp mr).2.symm
      next => simp at H
    · rw [path (by omega : u.val≤11),path (by omega : v.val≤11),H.1.1,H.1.2]
      exact of_decide_eq_true H.2
    · rw [path (by omega : u.val≤11),path (by omega : v.val≤11),H.1.1,H.1.2]
      exact of_decide_eq_true H.2
    · rw [path (by omega : u.val≤11),path (by omega : v.val≤11),H.1.1,H.1.2]
      exact of_decide_eq_true H.2
    · rw [path (by omega : u.val≤11),path (by omega : v.val≤11),H.1.2.1,H.1.2.2]
      exact of_decide_eq_true H.2
  let E := edge j m e f g h
  have edges (u v : Fin 13) (H : E u v=true) : G.Adj (φ u) (φ v) :=
    (show dir j m e f g h u v=true ∨ dir j m e f g h v u=true by
      simpa only [E,edge,Bool.or_eq_true] using H).elim (forward u v)
      (fun H => G.symm (forward v u H))
  have swap (u v : Fin 13) (hv : E u v=true) : E v u=true := by
    change (dir j m e f g h v u || dir j m e f g h u v)=true
    rw [Bool.or_comm]
    exact hv
  have edge_chain {u v : Fin 13} (eq : v.val=u.val+1) (big : v.val≤11) : E u v=true := by
    have bd : u.val+1≤11 := eq ▸ big
    simp [E,edge,dir,eq,bd]
  have edge_x {u v : Fin 13} (eq : u.val=1 ∨ u.val=j) (vv : v.val=12) : E u v=true := by
    simp [E,edge,dir,eq,vv]
  have edge_left {u v : Fin 13} (q : u.val=0 ∧ 1≤v.val ∧ v.val≤11)
      (H : m ⟨v.val-1,by omega⟩=1) : E u v=true := by
    simp [E,edge,dir,q.1,q.2.1,q.2.2,H]
  have edge_right {u v : Fin 13} (q : v.val=11 ∧ u.val<11)
      (H : m ⟨u.val,q.2⟩=2) : E u v=true := by
    simp [E,edge,dir,q.1,q.2,H]
  have edge_e {u v : Fin 13} (q : u.val=1 ∧ v.val=j) (H : e=true) : E u v=true := by
    simp [E,edge,dir,q.1,q.2,H]
  have edge_f {u v : Fin 13} (q : u.val=1 ∧ v.val=j-1) (H : f=true) : E u v=true := by
    simp [E,edge,dir,q.1,q.2,H]
  have edge_g {u v : Fin 13} (q : u.val=2 ∧ v.val=j) (H : g=true) : E u v=true := by
    simp [E,edge,dir,q.1,q.2,H]
  have edge_h {u v : Fin 13} (q : j≠10 ∧ u.val=1 ∧ v.val=j+1) (H : h=true) : E u v=true := by
    simp [E,edge,dir,q.1,q.2.1,q.2.2,H]
  have ad0 (v : Fin 13) (adj : G.Adj (φ 0) (φ v)) : E 0 v=true := by
    have vno : v.val≠12 := fun H => (no_endpoints hp.1 xo).1 (by
      simpa only [pv0,φ,if_pos H] using adj.symm)
    have vlt : v.val≤11 := by omega
    rw [pv0,path vlt] at adj
    have node : 1≤v.val := by
      by_cases bad : 1≤v.val
      · exact bad
      exfalso
      have vv : v.val=0 := by omega
      exact G.loopless a (by simpa [vv] using adj)
    have hm : v.val-1∈LeftMarks p :=
      mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [show v.val-1+1=v.val by omega]⟩
    exact edge_left ⟨c0,node,vlt⟩ ((bL _).mpr hm)
  have ad11 (v : Fin 13) (adj : G.Adj (φ 11) (φ v)) : E 11 v=true := by
    have vno : v.val≠12 := fun H => (no_endpoints hp.1 xo).2 (by
      simpa only [pv11,φ,if_pos H] using adj.symm)
    have vlt : v.val≤11 := by omega
    rw [pv11,path vlt] at adj
    have node : v.val<11 := by
      by_cases bad : v.val<11
      · exact bad
      exfalso
      have vv : v.val=11 := by omega
      exact G.loopless b (by simpa [vv,last] using adj)
    have hm : v.val∈RightMarks p := mem_filter.mpr ⟨mem_range.mpr (by omega),adj⟩
    exact swap _ _ (edge_right ⟨c11,node⟩ ((bR _).mpr hm))
  have ad1 (v : Fin 13) (adj : G.Adj (φ 1) (φ v)) : E 1 v=true := by
    by_cases isx : v.val=12
    · exact edge_x (.inl c1) isx
    have vlt : v.val≤11 := by omega
    rw [pv1,path vlt] at adj
    rcases near_pin (i:=1) (by decide) vlt (.inl rfl) adj with eq|eq|eq|eq|eq|eq
    · exact swap _ _ (edge_chain (by omega) (by decide))
    · exact (G.loopless (p.getVert 1) (by simpa [eq] using adj)).elim
    · exact edge_chain (by omega) vlt
    · exact edge_f ⟨c1,eq⟩ (decide_eq_true (by rwa [eq] at adj))
    · exact edge_e ⟨c1,eq⟩ (decide_eq_true (by rwa [eq] at adj))
    · have jn : j≠10 := by
        intro ej
        have ev : v.val=11 := by omega
        exact l1 (by simpa [ev,last] using adj.symm)
      exact edge_h ⟨jn,c1,eq⟩ (decide_eq_true (by rwa [eq] at adj))
  have adjj (v : Fin 13) (adj : G.Adj (φ J) (φ v)) : E J v=true := by
    by_cases isx : v.val=12
    · exact edge_x (.inr cj) isx
    have vlt : v.val≤11 := by omega
    rw [pvj,path vlt] at adj
    rcases near_pin (i:=j) (by omega) vlt (.inr rfl) adj with eq|eq|eq|eq|eq|eq
    · exact (rj (by simpa only [eq,getVert_zero] using adj.symm)).elim
    · exact swap _ _ (edge_e ⟨eq,cj⟩ (decide_eq_true (by simpa only [eq] using adj.symm)))
    · exact swap _ _ (edge_g ⟨eq,cj⟩ (decide_eq_true (by simpa only [eq] using adj.symm)))
    · exact swap _ _ (edge_chain (by omega) (by omega))
    · exact (G.loopless (p.getVert j) (by simpa only [eq] using adj)).elim
    · exact edge_chain (by omega) vlt
  have adx (v : Fin 13) (adj : G.Adj (φ 12) (φ v)) : E 12 v=true := by
    obtain e|e := ax (pv12 ▸ adj)
    · have eq : φ v=φ 1 := e.trans pv1.symm
      have q := inj eq
      subst v
      exact swap _ _ (edge_x (.inl c1) c12)
    · have eq : φ v=φ J := e.trans pvj.symm
      have q := inj eq
      subst v
      exact swap _ _ (edge_x (.inr cj) c12)
  have deg1 : 4≤degree j m e f g h 1 := by
    apply n13_model_degree_lower φ onto E 1 ad1
    rw [pv1]
    exact high _ (p.getVert_mem_support _)
  have degj : 4≤degree j m e f g h J := by
    apply n13_model_degree_lower φ onto E J adjj
    rw [pvj]
    exact high _ (p.getVert_mem_support _)
  have d2 (z : Fin 13) (rev : ∀ v,G.Adj (φ z) (φ v) → E z v=true) :
      (d2Set j m e f g h z).card≤4 := by
    have bd := n13_model_d2_upper hc φ inj E z edges rev
      (distanceTwo_le_of_even 4 (φ z) (even (φ z)))
    simpa only [d2Set,E] using bd
  obtain ⟨l,nd,all,chain⟩ := FourOrder13.tiny j jlo jhi m e f g h m0 m10 m1 mkj mj left right
    deg1 degj (d2 0 ad0) (d2 1 ad1) (d2 J adjj) (d2 11 ad11) (d2 12 adx)
  letI : Nonempty V := ⟨a⟩
  exact fail (hamilton_of_labeled_chain φ inj onto l nd all (chain.imp (fun u v H => edges u v H)))

#print axioms traceable_of_order_le_thirteen

end Graffiti189LongestPath.TwoCut.SmallOrderFour
