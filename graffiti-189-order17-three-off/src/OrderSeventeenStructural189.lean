import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open private mem_distanceTwo dist_two from SmallOrderFour189

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Distinct distance-two witnesses outside a common-neighborhood block
reduce the number of nonneighbors that a block vertex can have. -/
theorem common_neighbor_block_degree_budget
    (hc : G.Connected) {K W : Finset V} {x z : V}
    (hz : z∈K) (xz : G.Adj z x)
    (adj : ∀ w∈K,G.Adj x w)
    (outside : Disjoint W K) (wit : W⊆DistanceTwo G z) :
    K.card + W.card ≤ (G.neighborFinset z ∩ K).card + (DistanceTwo G z).card + 1 := by
  classical
  let N := G.neighborFinset z ∩ K
  let T := K \ insert z N
  have nK : N⊆K := inter_subset_right
  have zn : z∉N := fun h => G.loopless z ((G.mem_neighborFinset z z).mp (mem_inter.mp h).1)
  have insK : insert z N⊆K := insert_subset hz nK
  have ct : T.card + (N.card+1)=K.card := by
    have e := card_sdiff_add_card_eq_card insK
    rwa [card_insert_of_not_mem zn] at e
  have sub : T ⊆ DistanceTwo G z := by
    intro w h
    obtain ⟨wk,wn⟩ := mem_sdiff.mp h
    have nw : ¬G.Adj z w := fun e => wn (mem_insert_of_mem (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr e,wk⟩))
    exact mem_distanceTwo.mpr (dist_two hc (fun eq => wn (mem_insert.mpr (.inl eq.symm))) nw xz (adj _ wk))
  have d : Disjoint W T := outside.mono_right (sdiff_subset)
  have s := card_le_card (union_subset wit sub)
  rw [card_union_of_disjoint d] at s
  change K.card + W.card ≤ N.card + (DistanceTwo G z).card + 1
  omega

/-- With two exterior witnesses and the degree-four distance-two budget,
a block of six common neighbors has internal minimum degree at least three. -/
theorem common_neighbor_block_six_internal_degree
    (hc : G.Connected) {K : Finset V} {x z u v : V}
    (hz : z∈K) (xz : G.Adj z x) (adj : ∀ w∈K,G.Adj x w)
    (ku : u∉K) (kv : v∉K) (uv : u≠v)
    (hu : u∈DistanceTwo G z) (hv : v∈DistanceTwo G z)
    (n : K.card=6) (cap : (DistanceTwo G z).card≤4) :
    3≤(G.neighborFinset z ∩ K).card := by
  classical
  let W : Finset V := {u,v}
  have d : Disjoint W K := disjoint_left.mpr (by
    intro w hw wk
    rcases mem_insert.mp hw with rfl|g
    · exact ku wk
    · exact kv ((mem_singleton.mp g) ▸ wk))
  have sub : W⊆DistanceTwo G z := insert_subset hu (singleton_subset_iff.mpr hv)
  have h := common_neighbor_block_degree_budget hc hz xz adj d sub
  have w : W.card=2 := by simp [W,uv]
  omega

#print axioms common_neighbor_block_degree_budget
#print axioms common_neighbor_block_six_internal_degree

open SimpleGraph.Walk
open private mark_length degree_off_bound from SmallOrderFour189

/-- Shape of a possible degree-four obstruction at order at most seventeen,
given traceability up to sixteen and the two existing short-path reductions.
No order-seventeen case is assumed settled. -/
theorem order_seventeen_shape_from_short_reductions
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (closed16 : Fintype.card V≤16 →
      ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support)
    (uniqueBound : ∀ {a b x : V} {p : G.Walk a b},EdgeOptimal p →
      4≤G.degree a → 4≤G.degree b → x∉p.support →
      (∀ z∉p.support,z=x) → Fintype.card V≤13)
    (nineBan : ∀ {a b : V} {p : G.Walk a b},EdgeOptimal p →
      4≤G.degree a → 4≤G.degree b → p.length=9 →
      2≤((univ : Finset V)\p.support.toFinset).card →
      ((univ : Finset V)\p.support.toFinset).card≤7 → False)
    (order : Fintype.card V≤17)
    (fail : ¬∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support) :
    Fintype.card V=17 ∧
    ∃ a b : V,∃ p : G.Walk a b, EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      ((p.length=8 ∧ ((univ : Finset V)\p.support.toFinset).card=8) ∨
       (p.length=10 ∧ ((univ : Finset V)\p.support.toFinset).card=6) ∨
       (p.length=11 ∧ ((univ : Finset V)\p.support.toFinset).card=5) ∨
       (p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4) ∨
       (p.length=13 ∧ ((univ : Finset V)\p.support.toFinset).card=3)) := by
  classical
  have ord : Fintype.card V=17 := by
    by_contra h
    exact fail (closed16 (by omega))
  obtain ⟨a,b,p,best,ah,bh⟩ := exists_edge_optimal_with_high_ends hc 2 4 (by decide) conn degree fail
  obtain ⟨x,xo⟩ : ∃ u,u∉p.support := not_forall.mp (fun h => fail ⟨a,b,p,best.1.1,h⟩)
  obtain ⟨S,_,sne,soff,sclosed,sjoined⟩ := exists_omitted_component xo
  let H : OmittedComponent p := ⟨S,sne,soff,sclosed,sjoined⟩
  have se := componentPins_card best.1 H 2 conn
  obtain ⟨y,yp⟩ := card_pos.mp (show 0<(componentPins H).card by omega)
  obtain ⟨yp,u,uh,uy⟩ := mem_filter.mp yp
  have low := mark_length best.1 (H.off _ uh) (List.mem_toFinset.mp yp) uy ∅ (empty_subset _) (by simp)
  simp only [card_empty,Nat.add_zero] at low
  let O := (univ : Finset V)\p.support.toFinset
  have total : O.card+(p.length+1)=Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    rwa [List.toFinset_card_of_nodup best.1.1.support_nodup,length_support,card_univ] at h
  have large : 3≤O.card := by
    by_contra h
    have vertexLow {z : V} (zo : z∉p.support) : ¬4≤G.degree z := by
      have few := (at_most_two_pins_one_slack hc 2 (by decide)
        (fun v => distanceTwo_le_of_even 4 v (even v)) conn degree best zo).1
      have d := degree_off_bound best.1 zo
      change G.degree z≤(Pins p z).card+O.card-1 at d
      omega
    have only (z : V) (zo : z∉p.support) : z=x :=
      Classical.byContradiction (fun e => (degree z x e).elim (vertexLow zo) (vertexLow xo))
    have bound := uniqueBound best ah bh xo only
    omega
  have n9 : p.length≠9 := fun h => nineBan best ah bh h
    (show 2≤O.card by omega) (show O.card≤7 by omega)
  refine ⟨ord,a,b,p,best,ah,bh,?_⟩
  change (p.length=8 ∧ O.card=8) ∨ (p.length=10 ∧ O.card=6) ∨
    (p.length=11 ∧ O.card=5) ∨ (p.length=12 ∧ O.card=4) ∨ (p.length=13 ∧ O.card=3)
  omega

#print axioms order_seventeen_shape_from_short_reductions


private theorem walk_of_nonempty_chain (a : V) (L : List V)
    (adj : List.Chain' G.Adj (a::L)) :
    ∃ b,∃ p : G.Walk a b,p.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,p,eq⟩ := ih b adj.tail
    exact ⟨c,.cons adj.rel_head p,by simp [eq]⟩

/-- A length-eight spine with the saturated end chord and a path through
its omitted vertices cannot be longest. The omitted path need not span. -/
theorem no_longest_eight_with_saturated_splice
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=8)
    (q : G.Walk y x) (path : q.IsPath) (off : ∀ z∈q.support,z∉p.support)
    (left : G.Adj x (p.getVert 1)) (right : G.Adj y (p.getVert 7))
    (chord : G.Adj a (p.getVert 6)) : False := by
  classical
  let f : Fin 9→V := fun i => p.getVert i.val
  have fi : Function.Injective f := by
    intro i j h
    have il := i.isLt
    have jl := j.isLt
    exact Fin.ext (hp.1.getVert_injOn (show i.val≤p.length by omega)
      (show j.val≤p.length by omega) h)
  let A : List V := ([8,7] : List (Fin 9)).map f
  let B : List V := ([1,0,6,5,4,3,2] : List (Fin 9)).map f
  have ndAB : (A++B).Nodup := by
    change ((([8,7] : List (Fin 9)).map f)++(([1,0,6,5,4,3,2] : List (Fin 9)).map f)).Nodup
    rw [← List.map_append]
    exact (by decide : ([8,7]++[1,0,6,5,4,3,2] : List (Fin 9)).Nodup).map fi
  have inA (z : V) (mz : z∈A) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mz
    exact p.getVert_mem_support i.val
  have inB (z : V) (mz : z∈B) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mz
    exact p.getVert_mem_support i.val
  have da : A.Disjoint q.support := fun _ h g => off _ g (inA _ h)
  have db : q.support.Disjoint B := fun _ h g => off _ h (inB _ g)
  have dj : (A++q.support).Disjoint B := by
    intro z h g
    rcases List.mem_append.mp h with h|h
    · exact (List.disjoint_of_nodup_append ndAB) h g
    · exact db h g
  have nd : ((A++q.support)++B).Nodup :=
    ((ndAB.of_append_left).append path.support_nodup da).append ndAB.of_append_right dj
  have step (i : ℕ) (hi : i<8) : G.Adj (p.getVert (i+1)) (p.getVert i) :=
    (p.adj_getVert_succ (by omega)).symm
  have ca : List.Chain' G.Adj A := by
    change List.Chain' G.Adj [p.getVert 8,p.getVert 7]
    simpa using step 7 (by decide)
  have cb : List.Chain' G.Adj B := by
    change List.Chain' G.Adj [p.getVert 1,p.getVert 0,p.getVert 6,
      p.getVert 5,p.getVert 4,p.getVert 3,p.getVert 2]
    simp [List.chain'_cons,p.getVert_zero,show G.Adj (p.getVert 1) a by simpa using step 0 (by decide),
      chord,step 5 (by decide),step 4 (by decide),step 3 (by decide),step 2 (by decide)]
  have cq : List.Chain' G.Adj (A++q.support) := ca.append q.chain'_adj_support (by
    intro i im j jm
    have ai : p.getVert 7=i := by simpa [A,f] using im
    have qe : q.support.head?=some y := by cases q <;> rfl
    have aj : y=j := by simpa [qe] using jm
    subst i
    subst j
    exact right.symm)
  have last : (A++q.support).getLast?=some x := by
    have qe : q.support≠[] := q.support_ne_nil
    rw [List.getLast?_append, List.getLast?_eq_getLast qe]
    simp [q.getLast_support]
  have chain : List.Chain' G.Adj ((A++q.support)++B) := cq.append cb (by
    intro i im j jm
    have ai : x=i := by simpa [last] using im
    have aj : p.getVert 1=j := by simpa [B,f] using jm
    subst i
    subst j
    exact left)
  let L := (A++q.support)++B
  change List.Chain' G.Adj L at chain
  have Lne : L≠[] := by simp [L,A]
  rcases h : L with _|⟨r,R⟩
  · contradiction
  have n : (r::R).Nodup := h ▸ nd
  obtain ⟨s,w,eq⟩ := walk_of_nonempty_chain r R (h ▸ chain)
  have wpath : w.IsPath := IsPath.mk' (eq.symm ▸ n)
  have le := hp.2 _ _ w wpath
  have e := congrArg List.length eq
  rw [←h] at e
  simp only [L,List.length_append,A,B,List.length_map,List.length_cons,List.length_nil,
    length_support] at e
  omega

#print axioms no_longest_eight_with_saturated_splice


open private pin_data pin_of_neighbor_mem from SmallOrderFour189

/-- The prior saturated port classification suffices for a contradiction at
any order, with no assumption on the size or connectivity of the full omitted set. -/
theorem no_longest_eight_from_saturated_port_rules
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=8)
    (H : OmittedComponent p)
    (few : ∀ z∉p.support,(Pins p z).card≤1)
    (position : ∀ {x y : V}, x∈H.vertices → y∈H.vertices → x≠y →
      ∀ {i j : ℕ}, i∈Pins p x → j∈Pins p y → (i+3≤j ∨ j+3≤i) → (i=1 ∨ i=7))
    (chordRule : ∀ {x y : V}, x∈H.vertices → y∈H.vertices → x≠y →
      1∈Pins p x → 7∈Pins p y → G.Adj a (p.getVert 6)) : False := by
  classical
  have enough := componentPins_card hp.1 H 2 conn
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp (show 1<(componentPins H).card by omega)
  obtain ⟨up,x,xH,xu⟩ := mem_filter.mp hu
  obtain ⟨vp,y,yH,yv⟩ := mem_filter.mp hv
  have xo := H.off x xH
  have yo := H.off y yH
  obtain ⟨i,hi,iu⟩ := pin_of_neighbor_mem hp.1 xo (List.mem_toFinset.mp up) xu
  obtain ⟨j,hj,jv⟩ := pin_of_neighbor_mem hp.1 yo (List.mem_toFinset.mp vp) yv
  have ij : i≠j := fun e => uv (iu.symm.trans ((congrArg p.getVert e).trans jv))
  have xy : x≠y := by
    intro e
    subst y
    have lo := one_lt_card.mpr ⟨i,hi,j,hj,ij⟩
    have up := few x xo
    omega
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ij with gt|lt
    · exact .inl (component_pins_spaced_four hc even conn degree hp ah bh H xH yH hi hj gt)
    · exact .inr (component_pins_spaced_four hc even conn degree hp ah bh H yH xH hj hi lt)
  have ii := position xH yH xy hi hj gap
  have jj := position yH xH xy.symm hj hi gap.symm
  obtain ⟨x,y,xH,yH,xy,hi,hj⟩ : ∃ x y : V, x∈H.vertices ∧ y∈H.vertices ∧ x≠y ∧
      1∈Pins p x ∧ 7∈Pins p y := by
    rcases ii with i1|i7
    · have j7 := jj.resolve_left (fun j1 => ij (i1.trans j1.symm))
      exact ⟨x,y,xH,yH,xy,i1 ▸ hi,j7 ▸ hj⟩
    · have j1 := jj.resolve_right (fun j7 => ij (i7.trans j7.symm))
      exact ⟨y,x,yH,xH,xy.symm,j1 ▸ hj,i7 ▸ hi⟩
  obtain ⟨q,_,inH⟩ := H.joined y yH x xH
  exact no_longest_eight_with_saturated_splice hp.1 len (q.toPath : G.Walk y x)
    q.toPath.property (fun z zm=>H.off z (inH z (q.support_toPath_subset zm)))
    (pin_data hi).2 (pin_data hj).2 (chordRule xH yH xy hi hj)

#print axioms no_longest_eight_from_saturated_port_rules

end Graffiti189LongestPath.TwoCut
