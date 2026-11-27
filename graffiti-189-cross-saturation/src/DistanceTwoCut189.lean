import OddPortsCut189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem two_walk_middle {x y : V} (p : G.Walk x y) (h : p.length=2) :
    ∃ z, G.Adj x z ∧ G.Adj z y := by
  cases p with
  | nil => simp at h
  | cons e p =>
    cases p with
    | nil => simp at h
    | cons f p =>
      cases p with
      | nil => exact ⟨_,e,f⟩
      | cons g p => simp at h


/-- Across a partition with boundary s,t, each side meets s if deleting t
leaves a connected graph. -/
theorem side_hits_first_after_deleting_second {s t : V} (st : s≠t)
    (A : Finset V) (nonempty : A.Nonempty) (so : s∉A) (tOff : t∉A)
    (boundary : ∀ u∈A, ∀ v, G.Adj u v → v=s ∨ v=t ∨ v∈A)
    (c : (G.induce ((↑({t} : Finset V) : Set V)ᶜ)).Connected) :
    ∃ u∈A,G.Adj s u := by
  classical
  obtain ⟨u,ua⟩ := nonempty
  let W : Set V := (↑({t} : Finset V) : Set V)ᶜ
  have ut : u≠t := fun e=>tOff (e ▸ ua)
  let u' : W := ⟨u,by simpa [W] using ut⟩
  let s' : W := ⟨s,by simpa [W] using st⟩
  by_contra bad
  have step {p q : W} (w : (G.induce W).Walk p q) :
      p.val∈A → q.val∈A := by
    induction w with
    | nil => exact id
    | @cons p u q e w ih =>
      intro pa
      change G.Adj p.val u.val at e
      apply ih
      rcases boundary _ pa _ e with h|h|h
      · exact (bad ⟨_,pa,h ▸ e.symm⟩).elim
      · exact (u.property (by simp [h])).elim
      · exact h
  obtain ⟨q⟩ := c.preconnected u' s'
  exact so (step q ua)

namespace Split
open private left_boundary right_boundary from AdjacentCut189
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)

private theorem outer_connected
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x) :
    (G.induce (↑(insert a (insert b S.L)) : Set V)).Connected := by
  let O := insert a (insert b S.L)
  let W : Set V := (↑O : Set V)
  let x' : W := ⟨x,by simp [W,O,xl]⟩
  have reach (u : W) : (G.induce W).Reachable u x' := by
    have uo : u.val=a ∨ u.val=b ∨ u.val∈S.L := by
      have h := u.property
      simpa only [W,O,mem_coe,mem_insert] using h
    rcases uo with h|h|h
    · apply Adj.reachable
      change G.Adj u.val x
      rwa [h]
    · apply Adj.reachable
      change G.Adj u.val x
      rwa [h]
    · let u₀ : ↑(↑S.L : Set V) := ⟨u.val,h⟩
      let x₀ : ↑(↑S.L : Set V) := ⟨x,xl⟩
      obtain ⟨p⟩ := S.leftConnected.preconnected u₀ x₀
      have incl : (↑S.L : Set V) ≤ W := by
        intro v vh
        simp [W,O,vh]
      exact (p.map (G.induceHomOfLE incl).toHom).reachable
  letI : Nonempty W := ⟨x'⟩
  change (G.induce W).Connected
  exact SimpleGraph.Connected.mk (fun u v=>(reach u).trans (reach v).symm)

private theorem exclusive_ports_adjacent_case (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {x s t : V} (xl : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (sr : s∈S.R) (tr : t∈S.R) (as' : G.Adj a s) (bt : G.Adj b t)
    (st : G.Adj s t) (na : ¬G.Adj a t) (nb : ¬G.Adj b s)
    (only : ∀ z∈S.R, G.Adj a z ∨ G.Adj b z → z=s ∨ z=t) :
    Fintype.card V≤17 := by
  classical
  let A := insert a (insert b S.L)
  let B := S.R \ {s,t}
  have ao : s∉A ∧ t∉A := by
    have sa : s≠a := fun h=>S.rightOff.1 (h ▸ sr)
    have sb : s≠b := fun h=>S.rightOff.2 (h ▸ sr)
    have ta : t≠a := fun h=>S.rightOff.1 (h ▸ tr)
    have tb : t≠b := fun h=>S.rightOff.2 (h ▸ tr)
    have sl : s∉S.L := fun h=>disjoint_left.mp S.dis h sr
    have tl : t∉S.L := fun h=>disjoint_left.mp S.dis h tr
    simp [A,sa,sb,ta,tb,sl,tl]
  have bo : s∉B ∧ t∉B := by simp [B]
  have cross : ∀ u∈A, ∀ v∈B, ¬G.Adj u v := by
    intro u uh v vh uv
    obtain ⟨vr,vs⟩ := mem_sdiff.mp vh
    have h : u=a ∨ u=b ∨ u∈S.L := by simpa only [A,mem_insert] using uh
    rcases h with rfl|rfl|ul
    · exact vs (by simpa using only _ vr (Or.inl uv))
    · exact vs (by simpa using only _ vr (Or.inr uv))
    · exact S.cross _ ul _ vr uv
  have cov : ∀ z, z=s ∨ z=t ∨ z∈A ∨ z∈B := by
    intro z
    by_cases zs : z=s
    · exact .inl zs
    by_cases zt : z=t
    · exact .inr (.inl zt)
    rcases S.cover z with rfl|rfl|zl|zr
    · exact .inr (.inr (.inl (by simp [A])))
    · exact .inr (.inr (.inl (by simp [A])))
    · exact .inr (.inr (.inl (by simp [A,zl])))
    · exact .inr (.inr (.inr (mem_sdiff.mpr ⟨zr,by simp [zs,zt]⟩)))
  have bd : ∀ u∈B, ∀ v, G.Adj u v → v=s ∨ v=t ∨ v∈B := by
    intro u uh v vu
    rcases cov v with vs|vt|va|vb
    · exact .inl vs
    · exact .inr (.inl vt)
    · exact (cross _ va _ uh vu.symm).elim
    · exact .inr (.inr vb)
  have nonempty : B.Nonempty := by
    by_contra bad
    have qr : ∀ y∈S.R, y=s ∨ y=t := by
      intro y yr
      by_contra h
      exact bad ⟨y,mem_sdiff.mpr ⟨yr,by simpa using h⟩⟩
    have ds : G.neighborFinset s ⊆ {a,t} := by
      intro v vh
      have e := (mem_neighborFinset G s v).mp vh
      rcases right_boundary S s sr v e with h|h|h
      · simp [h]
      · exact (nb (h ▸ e.symm)).elim
      · rcases qr v h with h|h
        · exact (e.ne h.symm).elim
        · simp [h]
    have dt : G.neighborFinset t ⊆ {b,s} := by
      intro v vh
      have e := (mem_neighborFinset G t v).mp vh
      rcases right_boundary S t tr v e with h|h|h
      · exact (na (h ▸ e.symm)).elim
      · simp [h]
      · rcases qr v h with h|h
        · simp [h]
        · exact (e.ne h.symm).elim
    have cs := card_le_card ds
    have ct := card_le_card dt
    rw [card_neighborFinset_eq_degree] at cs ct
    have ns : ({a,t} : Finset V).card≤2 := (card_insert_le a {t}).trans (by simp)
    have nt : ({b,s} : Finset V).card≤2 := (card_insert_le b {s}).trans (by simp)
    rcases degree s t st.ne with h|h <;> omega
  let T : Graffiti189LongestPath.CrossSaturation.Split G s t :=
    ⟨A,B,disjoint_left.mpr (by
          intro v va vb
          have parts : v=a ∨ v=b ∨ v∈S.L := by simpa only [A,mem_insert] using va
          have vr := (mem_sdiff.mp vb).1
          rcases parts with h|h|h
          · exact S.rightOff.1 (h ▸ vr)
          · exact S.rightOff.2 (h ▸ vr)
          · exact disjoint_left.mp S.dis h vr),
      ao,bo,outer_connected S xl ax bx,cross,
      ⟨a,by simp [A],as'.symm⟩,⟨b,by simp [A],bt.symm⟩,cov⟩
  exact T.order_le_seventeen_of_adjacent_cut hc even st
    (side_hits_first_after_deleting_second st.ne B nonempty bo.1 bo.2 bd (conn {t} (by simp)))
    (side_hits_first_after_deleting_second st.ne.symm B nonempty bo.2 bo.1
      (fun u hu v e=>by simpa only [or_left_comm] using bd u hu v e) (conn {s} (by simp)))

private theorem exclusive_ports_nonadjacent_case (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5) (ab : G.dist a b=2)
    {x s t : V} (xl : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (sr : s∈S.R) (as' : G.Adj a s)
    (st : ¬G.Adj s t) (nb : ¬G.Adj b s)
    (other : ∀ z∈S.R, G.Adj b z → z=t) :
    Fintype.card V≤16 := by
  have h1 := dist_eq_one_iff_adj.mpr ax.symm
  have h2 := dist_eq_one_iff_adj.mpr bx.symm
  have h3 := dist_eq_one_iff_adj.mpr as'.symm
  have ab' : ¬G.Adj a b := fun e=>by
    have h := dist_eq_one_iff_adj.mpr e
    omega
  have s3 : G.dist s b=3 := by
    have ne : s≠b := fun e=>S.rightOff.2 (e ▸ sr)
    have lo := hc.one_lt_dist_of_ne_of_not_adj ne (fun e=>nb e.symm)
    have hi := hc.dist_triangle (u:=s) (v:=a) (w:=b)
    have noTwo : G.dist s b≠2 := by
      intro two
      obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist s b
      obtain ⟨v,sv,vb⟩ := two_walk_middle q (ql.trans two)
      rcases right_boundary S s sr v sv with p|p|p
      · exact ab' (p ▸ vb)
      · exact nb (p ▸ sv.symm)
      · exact st (other _ p vb.symm ▸ sv)
    omega
  exact S.order_le_sixteen_of_odd_ports hc even ab xl sr
    (by rw [h1]; decide) (by rw [h2]; decide)
    (by rw [h3]; decide) (by rw [s3]; decide)

/-- The degree-four Graffiti.pc bound implies traceability for a two-cut
whose deleted vertices are distance two and whose first side has a common port.
For an actual two-component cut, some side necessarily has a common port. -/
theorem traceable_of_distance_two_cut_with_common (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5) (ab : G.dist a b=2)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ne : a≠b := by
    intro eq
    rw [← eq,SimpleGraph.dist_self] at ab
    omega
  by_cases many : 3≤S.foreignPorts.card
  · exact S.traceable_of_three_or_more_foreign_ports hc even ne conn degree common many
      rightConnected rightA rightB
  obtain ⟨x,xl,ax,bx⟩ := common
  apply Graffiti189LongestPath.TwoCut.traceable_of_order_le_seventeen hc even conn degree
  by_cases rcommon : ∃ y∈S.R, G.Adj a y ∧ G.Adj b y
  · obtain ⟨y,yr,ay,by'⟩ := rcommon
    have h := S.order_le_sixteen_of_odd_ports hc even ab xl yr
      (by rw [dist_eq_one_iff_adj.mpr ax.symm]; decide)
      (by rw [dist_eq_one_iff_adj.mpr bx.symm]; decide)
      (by rw [dist_eq_one_iff_adj.mpr ay.symm]; decide)
      (by rw [dist_eq_one_iff_adj.mpr by'.symm]; decide)
    omega
  obtain ⟨s,sr,as'⟩ := rightA
  obtain ⟨t,tr,bt⟩ := rightB
  have nb : ¬G.Adj b s := fun bs=>rcommon ⟨s,sr,as',bs⟩
  have na : ¬G.Adj a t := fun at'=>rcommon ⟨t,tr,at',bt⟩
  have st : s≠t := fun e=> na (e ▸ as')
  have eq : S.foreignPorts = {s,t} := by
    have sub : ({s,t} : Finset V) ⊆ S.foreignPorts := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact mem_filter.mpr ⟨sr,.inl as'⟩
      · exact mem_filter.mpr ⟨tr,.inr bt⟩
    have c : ({s,t} : Finset V).card=2 := by simp [st]
    exact (eq_of_subset_of_card_le sub (by omega)).symm
  have only (z : V) (zr : z∈S.R) (p : G.Adj a z ∨ G.Adj b z) : z=s ∨ z=t := by
    have hz : z∈S.foreignPorts := mem_filter.mpr ⟨zr,p⟩
    simpa [eq] using hz
  by_cases edge : G.Adj s t
  · exact exclusive_ports_adjacent_case S hc even conn degree xl ax bx sr tr as' bt edge na nb only
  have h := exclusive_ports_nonadjacent_case S hc even ab xl ax bx sr as' edge nb
    (fun z zr bz=>(only _ zr (.inr bz)).resolve_left (fun e=>nb (e ▸ bz)))
  omega


/-- A two-component cut with endpoints at distance at most two cannot
obstruct degree-four Graffiti.pc #189. -/
theorem traceable_of_cut_distance_at_most_two (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5) (ab : a≠b) (small : G.dist a b≤2)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨z⟩ := rightConnected.nonempty
  have nonempty : S.R.Nonempty := ⟨z.val,z.property⟩
  have rightA := side_hits_first_after_deleting_second ab S.R nonempty S.rightOff.1 S.rightOff.2
    (right_boundary S) (conn {b} (by simp))
  have rightB := side_hits_first_after_deleting_second ab.symm S.R nonempty S.rightOff.2 S.rightOff.1
    (fun u hu v e=>by simpa only [or_left_comm] using right_boundary S u hu v e)
    (conn {a} (by simp))
  by_cases adj : G.Adj a b
  · exact S.traceable_of_adjacent_cut hc even adj rightA rightB conn degree
  have lt := hc.one_lt_dist_of_ne_of_not_adj ab adj
  have two : G.dist a b=2 := by omega
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle q (ql.trans two)
  rcases S.cover x with xa|xb'|xl|xr
  · exact (ax.ne xa.symm).elim
  · exact (xb.ne xb').elim
  · exact S.traceable_of_distance_two_cut_with_common hc even two conn degree ⟨x,xl,ax,xb.symm⟩
      rightConnected rightA rightB
  let T : Graffiti189LongestPath.CrossSaturation.Split G a b :=
    ⟨S.R,S.L,S.dis.symm,S.rightOff,S.leftOff,rightConnected,
      (fun u ur v vl e=>S.cross _ vl _ ur e.symm),rightA,rightB,
      fun v=>by simpa only [or_comm (a:=v∈S.L) (b:=v∈S.R)] using S.cover v⟩
  exact T.traceable_of_distance_two_cut_with_common hc even two conn degree ⟨x,xr,ax,xb.symm⟩
    S.leftConnected S.leftA S.leftB

#print axioms traceable_of_cut_distance_at_most_two
#print axioms side_hits_first_after_deleting_second
#print axioms traceable_of_distance_two_cut_with_common
end Split
end Graffiti189LongestPath.CrossSaturation
