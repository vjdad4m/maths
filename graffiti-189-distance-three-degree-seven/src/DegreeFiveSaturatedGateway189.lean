import DegreeFiveEightNoBridge189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common distance_to_b_ge_three_at_no_bridge from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

noncomputable def gatewayVisible : Finset V := by
  classical
  exact S.L.filter (fun t=> ¬G.Adj a t ∧ ¬G.Adj b t ∧ ∃ p∈S.localA,G.Adj p t)

noncomputable def gatewayDark (z : V) : Finset V :=
  S.L \ insert z (S.localA∪gatewayVisible S)

theorem saturated_gateway_shape (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (foreignFour : S.foreignA.card=4)
    (noBridge : ¬portBridge S) :
    ∃ z∈S.L,G.Adj b z ∧
      (∃ r∈gatewayVisible S,G.Adj r z) ∧
      CompleteOn G S.localA ∧
      (∀ p∈S.localA,∀ r∈gatewayVisible S,G.Adj p r) ∧
      (∀ t∈gatewayDark S z,G.Adj z t) ∧
      (∀ t∈gatewayDark S z,∀ u,G.Adj t u → u=z ∨ u=b ∨ u∈gatewayDark S z) := by
  classical
  let A := S.localA
  let Y := gatewayVisible S
  let get (p : V) (pp : p∈A) : ∃ u∈S.L,∃ z∈S.L,¬G.Adj a u ∧ ¬G.Adj b u ∧
      G.Adj b z ∧ G.Adj p u ∧ G.Adj u z ∧ z∈DistanceTwo G p :=
    b_gateway_from_a_port_without_bridge S hc far even foreignFour noBridge
      (mem_filter.mp pp).1 (mem_filter.mp pp).2
  have cl : CompleteOn G A := by
    intro p pp q qp pq
    obtain ⟨pL,ap⟩ := mem_filter.mp pp
    obtain ⟨qL,aq⟩ := mem_filter.mp qp
    obtain ⟨_,_,z,zL,_,_,bz,_,_,z2⟩ := get p pp
    apply Classical.byContradiction
    intro no
    have q2 := d2 hc pq no ap.symm aq
    exact not_common far aq
      ((singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zL qL z2 q2) ▸ bz)
  have see (p : V) (pp : p∈A) (r : V) (ry : r∈Y) : G.Adj p r := by
    obtain ⟨rL,nar,nbr,q,qa,qr⟩ := mem_filter.mp ry
    by_cases pq : p=q
    · exact pq.symm ▸ qr
    obtain ⟨pL,ap⟩ := mem_filter.mp pp
    obtain ⟨_,_,z,zL,_,_,bz,_,_,z2⟩ := get p pp
    apply Classical.byContradiction
    intro no
    have pr : p≠r := fun e=>nar (e ▸ ap)
    have r2 := d2 hc pr no (cl p pp q qa pq) qr
    exact nbr
      ((singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zL rL z2 r2) ▸ bz)
  obtain ⟨x,xL,ax⟩ := S.leftA
  have xa : x∈A := mem_filter.mpr ⟨xL,ax⟩
  obtain ⟨r,rL,z,zL,nar,nbr,bz,xr,rz,z2⟩ := get x xa
  have ry : r∈Y := mem_filter.mpr ⟨rL,nar,nbr,x,xa,xr⟩
  let T := gatewayDark S z
  have tprops (t : V) (tt : t∈T) : t∈S.L ∧ t≠z ∧ t∉A ∧ t∉Y := by
    obtain ⟨tl,no⟩ := mem_sdiff.mp tt
    refine ⟨tl,fun e=>no (mem_insert.mpr (.inl e)),?_,?_⟩
    · exact fun h=>no (mem_insert_of_mem (mem_union_left _ h))
    exact fun h=>no (mem_insert_of_mem (mem_union_right _ h))
  have noA (t : V) (tt : t∈T) (p : V) (pa : p∈A) : ¬G.Adj p t := by
    intro pt
    obtain ⟨tl,_,na,ny⟩ := tprops t tt
    obtain ⟨pl,ap⟩ := mem_filter.mp pa
    have at' : ¬G.Adj a t := fun h=>na (mem_filter.mpr ⟨tl,h⟩)
    have bt : ¬G.Adj b t := fun bt=>noBridge ⟨p,pl,t,tl,ap,pt,bt⟩
    exact ny (mem_filter.mpr ⟨tl,at',bt,p,pa,pt⟩)
  have notTwo (t : V) (tt : t∈T) : t∉DistanceTwo G x := by
    obtain ⟨tl,tz,_,_⟩ := tprops t tt
    exact fun t2=>tz (singleton_local_distance_two_at_opposite_four S hc even foreignFour xL ax tl zL t2 z2)
  have close (t : V) (tt : t∈T) : G.dist x t=3 := by
    have xt : x≠t := fun e=>(tprops t tt).2.2.1 (e ▸ xa)
    have lo := hc.one_lt_dist_of_ne_of_not_adj xt (noA t tt x xa)
    have hi := (saturated_at_opposite_four S hc far even foreignFour xL ax).2 t
    have ne : G.dist x t≠2 := fun h=>notTwo t tt (by simp [DistanceTwo,h])
    omega
  have bound (t : V) (tt : t∈T) (u : V) (tu : G.Adj t u) :
      u=z ∨ u=b ∨ u∈T := by
    obtain ⟨tl,_,ta,_⟩ := tprops t tt
    rcases left_boundary S t tl u tu with ea|eb|ul
    · exact (ta (mem_filter.mpr ⟨tl,ea ▸ tu.symm⟩)).elim
    · exact .inr (.inl eb)
    by_cases uz : u=z
    · exact .inl uz
    have ua : u∉A := fun h=>noA t tt u h tu.symm
    have uy : u∉Y := by
      intro uy
      have xt : x≠t := fun e=>ta (e ▸ xa)
      have t2 := d2 hc xt (noA t tt x xa) (see x xa u uy) tu.symm
      exact notTwo t tt t2
    exact .inr (.inr (mem_sdiff.mpr ⟨ul,fun m=>(mem_insert.mp m).elim uz (fun h=>(mem_union.mp h).elim ua uy)⟩))
  have link (t : V) (tt : t∈T) : G.Adj z t := by
    have three := close t tt
    obtain ⟨w,wlen⟩ := hc.exists_walk_length_eq_dist t x
    have wl : w.length=3 := by rw [wlen,dist_comm,three]
    have prev {u v : V} (p : G.Walk u v) (len : p.length=3) (eq : G.dist v u=3) :
        ∃ w,G.Adj u w ∧ G.dist v w=2 := by
      cases p with
      | nil => simp at len
      | @cons u w v e q =>
        refine ⟨w,e,?_⟩
        have n := G.dist_le q.reverse
        simp only [length_reverse] at n
        have tri := hc.dist_triangle (u:=v) (v:=w) (w:=u)
        have edge := dist_eq_one_iff_adj.mpr e.symm
        simp only [length_cons] at len
        omega
    obtain ⟨u,tu,ux⟩ := prev w wl three
    rcases bound t tt u tu with h|h|ut
    · exact h ▸ tu.symm
    · have lo := distance_to_b_ge_three_at_no_bridge S hc far noBridge xL ax
      rw [h] at ux
      omega
    have k := close u ut
    omega
  exact ⟨z,zL,bz,⟨r,ry,rz⟩,cl,see,link,bound⟩

#print axioms saturated_gateway_shape
end Graffiti189LongestPath.CrossSaturation.Split.Five
