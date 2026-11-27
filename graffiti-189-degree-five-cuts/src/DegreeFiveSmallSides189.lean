import TwoTerminalOre189
import DegreeFiveFarCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary right_boundary from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem not_both (far : 3≤G.dist a b) {x : V} (ax : G.Adj a x) :
    ¬G.Adj b x := by
  intro bx
  have e := G.dist_le (Walk.cons ax (Walk.cons bx.symm .nil))
  simp at e
  omega

private theorem left_high_inside (far : 3≤G.dist a b) {x : V}
    (xl : x∈S.L) (high : 5≤G.degree x) :
    4≤(ArticulationPair.inside G S.L x).card := by
  classical
  let N := ArticulationPair.inside G S.L x
  have inclA (no : ¬G.Adj b x) : G.neighborFinset x ⊆ insert a N := by
    intro z hz
    have xz := (mem_neighborFinset G x z).mp hz
    rcases left_boundary S x xl z xz with rfl|rfl|zl
    · exact mem_insert_self _ _
    · exact (no xz.symm).elim
    · exact mem_insert_of_mem (mem_filter.mpr ⟨zl,xz⟩)
  have inclB (no : ¬G.Adj a x) : G.neighborFinset x ⊆ insert b N := by
    intro z hz
    have xz := (mem_neighborFinset G x z).mp hz
    rcases left_boundary S x xl z xz with rfl|rfl|zl
    · exact (no xz.symm).elim
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨zl,xz⟩)
  change 4≤N.card
  by_cases ax : G.Adj a x
  · have h := card_le_card (inclA (not_both far ax))
    rw [card_neighborFinset_eq_degree] at h
    have c := card_insert_le a N
    omega
  have h := card_le_card (inclB ax)
  rw [card_neighborFinset_eq_degree] at h
  have c := card_insert_le b N
  omega

private theorem lift_side_path (A : Finset V) {u v : ↑(↑A : Set V)}
    (p : (G.induce (↑A : Set V)).Walk u v) (pp : p.IsPath)
    (all : ∀ z,z∈p.support) :
    ∃ q : G.Walk u.val v.val,q.IsPath ∧ ∀ z,z∈q.support ↔ z∈A := by
  classical
  let f : (G.induce (↑A : Set V)) →g G := {toFun:=Subtype.val,map_rel' := fun e=>e}
  have hp : (p.map f).IsPath := by
    rw [isPath_def,support_map]
    exact pp.support_nodup.map Subtype.val_injective
  refine ⟨p.map f,hp,?_⟩
  intro z
  rw [support_map,List.mem_map]
  constructor
  · rintro ⟨v,_,rfl⟩
    exact v.property
  · intro h
    exact ⟨⟨z,h⟩,all _,rfl⟩

private theorem terminal_left_path (far : 3≤G.dist a b)
    (small : S.L.card≤7) (high : ∀ u∈S.L,5≤G.degree u) :
    ∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support ↔ z=a ∨ z=b ∨ z∈S.L := by
  classical
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨y,yl,by'⟩ := S.leftB
  have xy : x≠y := fun e=>not_both far ax (e.symm ▸ by')
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let xx : U := ⟨x,xl⟩
  let yy : U := ⟨y,yl⟩
  have distinct : xx≠yy := fun e=>xy (congrArg Subtype.val e)
  have size : Fintype.card ↑(↑S.L : Set V)≤7 := by
    change Fintype.card {v : V // v∈S.L}≤7
    rwa [Fintype.card_coe]
  have hd (u : U) : 4≤J.degree u := by
    have e := ArticulationPair.inside_card_eq_degree_induce (G:=G) S.L u
    exact e ▸ left_high_inside S far u.property (high _ u.property)
  obtain ⟨p,pp,all⟩ := hamilton_connected_of_ore (G:=J) (fun u v _ _=>by
    have u4 := hd u
    have v4 := hd v
    omega) distinct
  obtain ⟨q,qp,qs⟩ := lift_side_path S.L p pp all
  have bno : b∉q.support := fun h=>S.leftOff.2 ((qs _).mp h)
  have aq : a∉(q.concat by'.symm).support := by
    intro h
    rw [support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at h
    rcases h with h|h
    · exact S.leftOff.1 ((qs _).mp h)
    · rw [h,SimpleGraph.dist_self] at far
      omega
  refine ⟨Walk.cons ax (q.concat by'.symm),(path_concat_new q qp _ bno).cons aq,?_⟩
  intro z
  simp only [support_cons,List.mem_cons,support_concat,List.concat_eq_append,List.mem_append,qs,
    List.mem_singleton,List.not_mem_nil,or_false,or_comm (a:=z∈S.L) (b:=z=b)]

private theorem any_internal_neighbor {z : V} (zl : z∈S.L)
    (far : 3≤G.dist a b) : ∃ v∈S.L,G.Adj z v := by
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨y,yl,by'⟩ := S.leftB
  have xy : x≠y := fun e=>not_both far ax (e.symm ▸ by')
  have other : ∃ w∈S.L,w≠z := by
    by_cases xz : x=z
    · exact ⟨y,yl,fun e=>xy (xz.trans e.symm)⟩
    exact ⟨x,xl,xz⟩
  obtain ⟨w,wl,wz⟩ := other
  let U : Set V := ↑S.L
  obtain ⟨p⟩ := S.leftConnected.preconnected (⟨z,zl⟩ : U) (⟨w,wl⟩ : U)
  cases p with
  | nil => exact (wz rfl).elim
  | @cons u v w uv q => exact ⟨v.val,v.property,uv⟩

private theorem left_can_root_at_one_cut (far : 3≤G.dist a b) (small : S.L.card≤8)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    ∃ x∈S.L, (G.Adj a x ∨ G.Adj b x) ∧
      ∃ y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support ↔ z∈S.L := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  have u8 : Fintype.card U≤8 := by
    change Fintype.card {v : V // v∈S.L}≤8
    rwa [Fintype.card_coe]
  have q4 (v : U) (hv : 5≤G.degree v.val) : 4≤J.degree v := by
    have e := ArticulationPair.inside_card_eq_degree_induce (G:=G) S.L v
    exact e ▸ left_high_inside S far v.property hv
  let ore : RootedClosureAPI := by
    intro U _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  have finish (x : V) (xl : x∈S.L) (hit : G.Adj a x ∨ G.Adj b x)
      (path : RootedSpan J (⟨x,xl⟩ : U)) :
      ∃ x∈S.L, (G.Adj a x ∨ G.Adj b x) ∧
        ∃ y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support ↔ z∈S.L := by
    obtain ⟨y,p,pp,pa⟩ := path
    obtain ⟨q,qp,qs⟩ := lift_side_path S.L p pp pa
    exact ⟨x,xl,hit,y.val,q,qp,qs⟩
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨y,yl,by'⟩ := S.leftB
  have xy : x≠y := fun e=>not_both far ax (e.symm ▸ by')
  by_cases low : ∃ z∈S.L, ¬5≤G.degree z
  · obtain ⟨z,zl,zl5⟩ := low
    let zz : U := ⟨z,zl⟩
    let A : Finset U := univ.erase zz
    let K := completeWith J A
    have clique : CompleteOn K A := completeWith_of_mem J A
    have cap (u : U) (ua : u∈A) (v : U) (va : v∈A) : Fintype.card U≤J.degree u+J.degree v := by
      have uz : u.val≠z := fun e=>(mem_erase.mp ua).1 (Subtype.ext e)
      have vz : v.val≠z := fun e=>(mem_erase.mp va).1 (Subtype.ext e)
      have uh := q4 u ((degree _ _ uz).resolve_right zl5)
      have vh := q4 v ((degree _ _ vz).resolve_right zl5)
      omega
    obtain ⟨w,wl,zw⟩ := any_internal_neighbor S zl far
    let ww : U := ⟨w,wl⟩
    by_cases zhit : G.Adj a z ∨ G.Adj b z
    · apply finish z zl zhit
      refine close_completed_class ore A zz cap ?_
      exact rooted_path_from_root_into_clique K
        (completeWith_mono J A (show J.Adj zz ww from zw)) clique
    have take (r : V) (rl : r∈S.L) (hr : G.Adj a r ∨ G.Adj b r) (rw' : r≠w) :
      ∃ x∈S.L, (G.Adj a x ∨ G.Adj b x) ∧
        ∃ y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support ↔ z∈S.L := by
      apply finish r rl hr
      let rr : U := ⟨r,rl⟩
      have rz : rr≠zz := by
        intro e
        have re : r=z := congrArg Subtype.val e
        exact zhit (re ▸ hr)
      have wz : ww≠zz := fun e=>zw.ne.symm (congrArg Subtype.val e)
      have rrw : rr≠ww := fun e=>rw' (congrArg Subtype.val e)
      refine close_completed_class ore A rr cap ?_
      exact rooted_path_of_clique_and_outlier K rz wz rrw
        (completeWith_mono J A (show J.Adj ww zz from zw.symm)) clique
    by_cases xw : x=w
    · exact take y yl (.inr by') (fun e=>xy (xw.trans e.symm))
    exact take x xl (.inl ax) xw
  apply finish x xl (.inl ax)
  let xx : U := ⟨x,xl⟩
  refine close_completed_class ore univ xx ?_ ?_
  · intro u _ v _
    have ud := q4 u (Classical.byContradiction fun e=>low ⟨u.val,u.property,e⟩)
    have vd := q4 v (Classical.byContradiction fun e=>low ⟨v.val,v.property,e⟩)
    omega
  obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique univ (completeWith_of_mem J univ) (mem_univ xx)
  exact ⟨y,p,pp,fun v=>(ps v).mpr (mem_univ _)⟩

private theorem join_support_at_terminal {e c f : V}
    (p : G.Walk e c) (q : G.Walk c f) (pp : p.IsPath) (qp : q.IsPath)
    (meet : ∀ z∈p.support, z∈q.support → z=c) :
    (p.append q).IsPath := by
  rw [isPath_def,support_append,List.nodup_append]
  refine ⟨pp.support_nodup,qp.support_nodup.tail,?_⟩
  intro z zp zq
  have zc := meet z zp (List.mem_of_mem_tail zq)
  subst z
  cases q with
  | nil => simp at zq
  | cons e q =>
    exact ((cons_isPath_iff _ _).mp qp).2 (by simpa only [support_cons,List.tail_cons] using zq)

/-- In the degree-five case, a distance-three two-cut is enough when an
all-high shore has at most seven vertices and its other shore has at most eight. -/
theorem traceable_of_small_sides (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (leftSize : S.L.card≤7) (rightSize : S.R.card≤8)
    (leftHigh : ∀ u∈S.L,5≤G.degree u)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  obtain ⟨p,pp,ps⟩ := terminal_left_path S far leftSize leftHigh
  obtain ⟨x,xr,hit,y,q,qp,qs⟩ :=
    left_can_root_at_one_cut (switch S rightConnected rightA rightB) far rightSize degree
  change ∀ z,z∈q.support ↔ z∈S.R at qs
  have finish {e c : V} (r : G.Walk e c) (rp : r.IsPath)
      (rs : ∀ z,z∈r.support ↔ z=a ∨ z=b ∨ z∈S.L)
      (cx : G.Adj c x) (off : c∉S.R) :
      ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
    let t := Walk.cons cx q
    have tp : t.IsPath := qp.cons (fun h=>off ((qs _).mp h))
    have ts (z : V) : z∈t.support ↔ z=c ∨ z∈S.R := by simp only [t,support_cons,List.mem_cons,qs]
    have meet (z : V) (zr : z∈r.support) (zt : z∈t.support) : z=c := by
      rcases (ts _).mp zt with h|h
      · exact h
      rcases (rs _).mp zr with ra|rb|rl
      · exact (S.rightOff.1 (ra ▸ h)).elim
      · exact (S.rightOff.2 (rb ▸ h)).elim
      · exact (disjoint_left.mp S.dis rl h).elim
    refine ⟨e,y,r.append t,join_support_at_terminal r t rp tp meet,?_⟩
    intro z
    rw [mem_support_append_iff]
    rcases S.cover z with h|h|h|h
    · exact .inl ((rs _).mpr (.inl h))
    · exact .inl ((rs _).mpr (.inr (.inl h)))
    · exact .inl ((rs _).mpr (.inr (.inr h)))
    · exact .inr ((ts _).mpr (.inr h))
  rcases hit with ax|bx
  · exact finish p.reverse pp.reverse (fun z=>by simpa using ps z) ax S.rightOff.1
  exact finish p pp ps bx S.rightOff.2

theorem traceable_of_sides_at_most_seven (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (leftSize : S.L.card≤7) (rightSize : S.R.card≤7)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases leftHigh : ∀ u∈S.L,5≤G.degree u
  · exact traceable_of_small_sides S far degree leftSize (by omega) leftHigh rightConnected rightA rightB
  push_neg at leftHigh
  obtain ⟨x,xl,xlow⟩ := leftHigh
  have rightHigh (v : V) (vr : v∈S.R) : 5≤G.degree v :=
    (degree x v (fun e=>disjoint_left.mp S.dis (e ▸ xl) vr)).resolve_left (by omega)
  exact traceable_of_small_sides (switch S rightConnected rightA rightB) far degree rightSize
    (by change S.L.card≤8; omega) rightHigh S.leftConnected S.leftA S.leftB

#print axioms traceable_of_small_sides
#print axioms traceable_of_sides_at_most_seven
end Graffiti189LongestPath.CrossSaturation.Split.Five
