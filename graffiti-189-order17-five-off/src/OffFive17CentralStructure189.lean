import OffSix17CoreLift189
import SixCoreMarkedPath189

namespace Graffiti189SmallMarkedCore
open Finset SimpleGraph
open scoped Classical
set_option linter.unusedSectionVars false
variable {W : Type*} [Fintype W] [DecidableEq W]
variable (D : SimpleGraph W) [DecidableRel D.Adj]
open private contacts contacts_spec two_contacts_of_high contacts_nonempty reverse_exists no_cross
  path4 ripe_neighbor from SixCoreMarkedPath189

private theorem exclusive_low {x y a : W} (small : Fintype.card W  ≤  6)
    (xy : x ≠ y) (none : ¬∃ q : D.Walk x y, q.IsPath ∧ 3  ≤  q.length)
    (btwo : 2  ≤  (contacts D y x).card)
    (ha : a ∈ contacts D x y) (na : a ∉ contacts D y x) :
    D.degree a  ≤  2 := by
  obtain ⟨ay,xa⟩ := (contacts_spec D).mp ha
  have ya : ¬D.Adj y a := fun h => na ((contacts_spec D).mpr ⟨xa.ne.symm,h⟩)
  let bad := insert a (insert y (contacts D y x))
  have yc : y ∉ contacts D y x := by simp [contacts_spec]
  have ab : a ∉ insert y (contacts D y x) := by simp [ay,na]
  have four : 4  ≤  bad.card := by
    rw [show bad=insert a (insert y (contacts D y x)) from rfl,
      card_insert_of_not_mem ab,card_insert_of_not_mem yc]
    omega
  have incl : D.neighborFinset a ⊆ univ \ bad := by
    intro v hv
    have h := (mem_neighborFinset D _ _).mp hv
    simp only [mem_sdiff,mem_univ,true_and,bad,mem_insert,not_or]
    exact ⟨h.ne.symm, (fun e => ya (e ▸ h.symm)),fun hb => no_cross D xy none ha hb h⟩
  have h := card_le_card incl
  rw [card_neighborFinset_eq_degree,card_sdiff (subset_univ bad) ,card_univ] at h
  omega

private theorem outside_high_has_edge {x y c b : W} (small : Fintype.card W  ≤  6)
    (xy : x≠y) (cx : c≠x) (cy : c≠y) (bx : b≠x) (by' : b≠y) (bc : b≠c)
    (hc : 3 ≤  D.degree c) (ncx : ¬D.Adj c x) (ncy : ¬D.Adj c y) :
    D.Adj c b := by
  by_contra no
  let bad : Finset W := {b,c,x,y}
  have four : bad.card = 4 := by
    simp [bad,card_insert_of_not_mem,bc,bx,by',cx,cy,xy]
  have incl : D.neighborFinset c ⊆ univ \ bad := by
    intro v hv
    have e := (mem_neighborFinset D _ _).mp hv
    simp only [mem_sdiff,mem_univ,true_and,bad,mem_insert,mem_singleton,not_or]
    exact ⟨fun h => no (h ▸ e),e.ne.symm,fun h => ncx (h ▸ e),fun h => ncy (h ▸ e)⟩
  have h := card_le_card incl
  rw [card_neighborFinset_eq_degree,card_sdiff (subset_univ bad) ,card_univ,four] at h
  omega

private theorem nested_exists {x y : W} (small : Fintype.card W  ≤  6)
    (wide : ∀ a b : W, a ≠ b → 3  ≤  D.degree a ∨ 3  ≤  D.degree b)
    (xy : x≠y) (sub : contacts D x y ⊆ contacts D y x)
    (anyA : (contacts D x y).Nonempty) (twoB : 2  ≤  (contacts D y x).card) :
    ∃ q : D.Walk x y, q.IsPath ∧ 3  ≤  q.length := by
  by_contra none
  obtain ⟨a,ha,high⟩ : ∃ a∈contacts D x y, 3 ≤ D.degree a := by
    obtain ⟨a,ha⟩ := anyA
    by_cases h : 3 ≤ D.degree a
    · exact ⟨a,ha,h⟩
    have xhigh := (wide x a ((contacts_spec D).mp ha).2.ne).resolve_right h
    obtain ⟨b,hb,ba⟩ := Finset.exists_mem_ne (two_contacts_of_high D (y:=y) xhigh) a
    exact ⟨b,hb,(wide b a ba).resolve_right h⟩
  obtain ⟨c,ac,cx,cy,cb⟩ := ripe_neighbor D xy none ha high
  have ncx : ¬D.Adj c x := fun e => cb (sub ((contacts_spec D).2 ⟨cy,e.symm⟩))
  have ncy : ¬D.Adj c y := fun e => cb ((contacts_spec D).2 ⟨cx,e.symm⟩)
  obtain ⟨ay,xa⟩ := (contacts_spec D).mp ha
  by_cases chigh : 3 ≤ D.degree c
  · obtain ⟨b,hb,ba⟩ := Finset.exists_mem_ne twoB a
    have bc : b≠c := fun e => cb (e ▸ hb)
    obtain ⟨bx,yb⟩ := (contacts_spec D).mp hb
    have cb' := outside_high_has_edge D small xy cx cy bx yb.ne.symm bc chigh ncx ncy
    exact none (path4 D xa ac cb' yb.symm cx.symm bx.symm xy ba.symm ay cy)
  · have xhigh := (wide x c cx.symm).resolve_right chigh
    obtain ⟨a',ha',a'a⟩ := Finset.exists_mem_ne (two_contacts_of_high D (y:=y) xhigh) a
    have haB := sub ha'
    obtain ⟨a'x,ya'⟩ := (contacts_spec D).mp haB
    have a'c : a'≠c := fun e => cb (e ▸ haB)
    have a'high := (wide a' c a'c).resolve_right chigh
    obtain ⟨d,a'd,dx,dy,db⟩ := ripe_neighbor D xy none ha' a'high
    by_cases dc : d=c
    · subst d
      exact none (path4 D xa ac a'd.symm ya'.symm cx.symm a'x.symm xy a'a.symm ay cy)
    · have dhigh := (wide d c dc).resolve_right chigh
      have ndx : ¬D.Adj d x := fun e => db (sub ((contacts_spec D).2 ⟨dy,e.symm⟩))
      have ndy : ¬D.Adj d y := fun e => db ((contacts_spec D).2 ⟨dx,e.symm⟩)
      have ad : a≠d := fun e => db (e ▸ sub ha)
      have da := outside_high_has_edge D small xy dx dy xa.ne.symm ay ad dhigh ndx ndy
      exact none (path4 D xa da.symm a'd.symm ya'.symm dx.symm a'x.symm xy a'a.symm ay dy)

/-- In a simple graph on at most six vertices with no isolated vertices and at most
one vertex of degree below three, any marked pair has a simple path of at
least three edges between it, unless one is a leaf adjacent to the other. -/
theorem small_core_marked_path (small : Fintype.card W  ≤  6)
    (minDeg : ∀ x : W, 1 ≤ D.degree x)
    (wide : ∀ a b : W, a ≠ b → 3  ≤  D.degree a ∨ 3  ≤  D.degree b)
    {x y : W} (xy : x≠y) :
    (∃ q : D.Walk x y,q.IsPath ∧ 3 ≤ q.length) ∨
      D.neighborFinset x={y} ∨ D.neighborFinset y={x} := by
  by_cases h : ∃ q : D.Walk x y,q.IsPath ∧ 3 ≤ q.length
  · exact .inl h
  by_cases hx : D.neighborFinset x={y}
  · exact .inr (.inl hx)
  by_cases hy : D.neighborFinset y={x}
  · exact .inr (.inr hy)
  have anyX := contacts_nonempty D (minDeg x) hx
  have anyY := contacts_nonempty D (minDeg y) hy
  have noRev : ¬∃ q : D.Walk y x,q.IsPath ∧ 3 ≤ q.length :=
    fun e => h ((reverse_exists D).mpr e)
  have ordered {s t : W} (st : s≠t)
      (hs : (contacts D s t).Nonempty) (ht : (contacts D t s).Nonempty)
      (none : ¬∃ q : D.Walk s t,q.IsPath ∧ 3 ≤ q.length)
      (noneR : ¬∃ q : D.Walk t s,q.IsPath ∧ 3 ≤ q.length)
      (th : 3 ≤ D.degree t) : False := by
    have bTwo := two_contacts_of_high D (y:=s) th
    by_cases sub : contacts D s t ⊆ contacts D t s
    · exact none (nested_exists D small wide st sub hs bTwo)
    obtain ⟨a,ha,hab⟩ : ∃ a∈contacts D s t, a∉contacts D t s := by
      by_contra he
      apply sub
      intro a ha
      by_cases hmem : a ∈ contacts D t s
      · exact hmem
      · exact (he ⟨a,ha,hmem⟩).elim
    have alow := exclusive_low D small st none bTwo ha hab
    have as : a≠s := ((contacts_spec D).mp ha).2.ne.symm
    have shigh := (wide a s as).resolve_left (by omega)
    have aTwo := two_contacts_of_high D (y:=t) shigh
    have rev : contacts D t s ⊆ contacts D s t := by
      intro b hb
      by_cases hba : b ∈ contacts D s t
      · exact hba
      exfalso
      have blow := exclusive_low D small st.symm noneR aTwo hb hba
      have ab : a≠b := fun e => hab (e ▸ hb)
      rcases wide a b ab with x|x <;> omega
    exact noneR (nested_exists D small wide st.symm rev ht aTwo)
  exact False.elim ((wide x y xy).elim
    (ordered xy.symm anyY anyX noRev h) (ordered xy anyX anyY h noRev))


#print axioms small_core_marked_path
end Graffiti189SmallMarkedCore

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin reverse_long mark_length
  LeftMarks RightMarks dist_two mem_distanceTwo from SmallOrderFour189
open private pin_two_contacts_end mark_holes_of_pin_and_missing_endpoint omitted_degree_component_bound
  two_pin_flanks_path_only two_pin_universal_in_omitted_component pins_gap_at_four from FourOffGraphSupport189
open private two_pins_choose_ordered omittedDegree_eq omittedNeighbors from FourOffGraphCore189
open private omitted_neighbors_eq_component_neighbors from OffSix17CoreLift189

/-- At length eleven, four interior rotation holes are impossible.
Every double pin has a boundary member. -/
theorem double_pins_hit_boundary_at_eleven
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card   ≤   5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4   ≤   G.degree u ∨ 4   ≤   G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4   ≤   G.degree a) (bh : 4   ≤   G.degree b)
    (len : p.length=11) (xo : x∉p.support)
    {i j : ℕ} (xi : i∈Pins p x) (xj : j∈Pins p x) (ij : i<j) :
    i=1 ∨ j=10 := by
  classical
  by_contra! no
  have cap := fun v=>distanceTwo_le_of_even 4 v (even v)
  have few := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp xo).1
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  have ir := (pin_data xi).1
  have jr := (pin_data xj).1
  have ip := pin_pos hp.1 xo xi
  obtain ⟨ll,rr⟩ := pin_two_contacts_end hp.1 hc xo few (cap x) xi xj gap
  have hi0 := (mark_holes_of_pin_and_missing_endpoint hp.1 xo xi).1 (fun a=>no.1 (ll i xi a))
  have hj0 := (mark_holes_of_pin_and_missing_endpoint hp.1 xo xj).1 (fun a=>no.1 (ll j xj a))
  have hi1 := (mark_holes_of_pin_and_missing_endpoint hp.1 xo xi).2 (fun a=>no.2 (by have e:=rr i xi a; omega))
  have hj1 := (mark_holes_of_pin_and_missing_endpoint hp.1 xo xj).2 (fun a=>no.2 (by have e:=rr j xj a; omega))
  let T : Finset ℕ := {i-1,i,j-1,j}
  have eq (k : ℕ) : k∈T ↔ k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j := by simp [T]
  have tc : T.card=4 := by
    have a : i-1∉({i,j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have b : i∉({j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have c : j-1∉({j}:Finset ℕ) := by simp only [mem_singleton]; omega
    rw [show T={i-1,i,j-1,j} from rfl,card_insert_of_not_mem a,
      card_insert_of_not_mem b,card_insert_of_not_mem c,card_singleton]
  have sub : T⊆range p.length := by
    intro k km
    rcases (eq _).mp km with rfl|rfl|rfl|rfl <;> exact mem_range.mpr (by omega)
  have disj : Disjoint (LeftMarks p∪RightMarks p) T := disjoint_left.mpr (by
    intro k kd km
    rcases (eq _).mp km with rfl|rfl|rfl|rfl
    · exact hi0 kd
    · exact hi1 kd
    · exact hj0 kd
    · exact hj1 kd)
  have budget := mark_length hp.1 xo (p.getVert_mem_support i) (pin_data xi).2 T sub disj
  omega

/-- A nontrivial omitted component cannot contain a double-pin vertex
on a high-ended edge-optimal length-eleven path. -/
theorem single_pins_in_nontrivial_length_eleven_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (H : OmittedComponent p) (large : 2  ≤  H.vertices.card)
    {x : V} (xh : x∈H.vertices) : (Pins p x).card  ≤  1 := by
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
    rcases double_pins_hit_boundary_at_eleven hc even conn degree hp ah bh len xo xi xj ij with rfl|hj
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


/-- Nontrivial omitted components at length eleven attach only at interior
sites 2 through 9. A boundary carrier and any carrier of a different
site would permit the omitted-component splice. -/
theorem no_boundary_pin_in_nontrivial_length_eleven_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (H : OmittedComponent p) (large : 2  ≤  H.vertices.card)
    {x : V} (xh : x∈H.vertices) {i : ℕ} (xi : i∈Pins p x) : 2  ≤  i ∧ i  ≤  9 := by
  classical
  have nl := (pin_data xi).1
  have xo := H.off _ xh
  have ip := pin_pos hp.1 xo xi
  by_contra! alt
  have eq : i=1 ∨ i=10 := by omega
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
    have one := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H large xh
    exact (Nat.not_lt_of_ge one) (one_lt_card.mpr ⟨i,xi,j,yj,ij⟩)
  obtain ⟨q,_,stay⟩ := H.joined x xh y yh
  let Q : G.Walk x y := q.toPath
  have qpath : Q.IsPath := q.toPath.property
  have qpos : 0<Q.length := Nat.pos_of_ne_zero (fun e=>xy (Q.eq_of_length_eq_zero e))
  have safe (v : V) (vv : v∈Q.support) : v∉p.support := H.off _ (stay _ (q.support_toPath_subset vv))
  rcases eq with rfl|i10
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

#print axioms no_boundary_pin_in_nontrivial_length_eleven_component



/-- At length eleven a single-pin carrier cannot be a leaf of the omitted
component with a neighbor carrying another pin. -/
theorem no_foreign_pin_at_omitted_leaf_neighbor_length_eleven
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (H : OmittedComponent p)
    {x y : V} (xh : x∈H.vertices) (yh : y∈H.vertices)
    {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (ij : i≠j)
    (leaf : G.neighborFinset x∩H.vertices={y}) : False := by
  classical
  have xy : G.Adj x y := by
    have m : y∈G.neighborFinset x∩H.vertices := by rw [leaf]; simp
    exact (mem_neighborFinset G _ _).mp (mem_inter.mp m).1
  have large : 2  ≤  H.vertices.card := one_lt_card.mpr ⟨x,xh,y,yh,xy.ne⟩
  have xs := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H large xh
  have ys := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H large yh
  have xd := omittedDegree_eq hp.1 (H.off _ xh)
  rw [omitted_neighbors_eq_component_neighbors H xh,leaf,card_singleton] at xd
  have yd : 4  ≤  G.degree y := (degree x y xy.ne).resolve_left (by omega)
  have ydeg := omittedDegree_eq hp.1 (H.off _ yh)
  rw [omitted_neighbors_eq_component_neighbors H yh] at ydeg
  let T := G.neighborFinset y∩H.vertices
  have xT : x∈T := mem_inter.mpr ⟨(mem_neighborFinset G _ _).mpr xy.symm,xh⟩
  have t3 : 3  ≤  T.card := by change 3  ≤  (G.neighborFinset y∩H.vertices).card; omega
  have c := card_erase_of_mem xT
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<(T.erase x).card by omega)
  let P : Finset ℕ := {i-1,i+1,j}
  have ib := (pin_data xi).1
  have jb := (pin_data yj).1
  have il := pin_pos hp.1 (H.off _ xh) xi
  have gap : i+3  ≤  j ∨ j+3  ≤  i := by
    rcases lt_or_gt_of_ne ij with h|h
    · exact .inl (component_pins_spaced_four hc even conn degree hp ah bh H xh yh xi yj h)
    · exact .inr (component_pins_spaced_four hc even conn degree hp ah bh H yh xh yj xi h)
  have pr {k : ℕ} (m : k∈P) : k  ≤  p.length := by
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

#print axioms no_foreign_pin_at_omitted_leaf_neighbor_length_eleven




theorem distinct_pins_in_nontrivial_length_eleven_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (H : OmittedComponent p)
    (hlo : 2   ≤   H.vertices.card) (hhi : H.vertices.card   ≤   6)
    {x y : V} (xh : x∈H.vertices) (yh : y∈H.vertices)
    {i j : ℕ} (xi : i∈Pins p x) (yj : j∈Pins p y) (lt : i<j) : i=4 ∧ j=7 := by
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
  have bound (z : S) : 4  ≤  G.degree z.val → 3  ≤  D.degree z := by
    have d := omittedDegree_eq hp.1 (H.off _ z.property)
    rw [omitted_neighbors_eq_component_neighbors H z.property,←dc z] at d
    have one := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H
      (by omega) z.property
    omega
  have d3 (s t : S) (ne : s≠t) : 3  ≤  D.degree s ∨ 3  ≤  D.degree t :=
    (degree s.val t.val (fun e=>ne (Subtype.ext e))).imp (bound s) (bound t)
  have d1 (z : S) : 1  ≤  D.degree z := by
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
  have cardS : Fintype.card S   ≤   6 := (Fintype.card_coe H.vertices).trans_le hhi
  have xo := H.off _ xh
  have yo := H.off _ yh
  have xy : x≠y := by
    intro e
    subst y
    have two := one_lt_card.mpr ⟨i,xi,j,yj,lt.ne⟩
    have one := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H hlo xh
    omega
  let sx : S := ⟨x,xh⟩
  let sy : S := ⟨y,yh⟩
  have distinct : sx≠sy := fun e=>xy (congrArg Subtype.val e)
  rcases Graffiti189SmallMarkedCore.small_core_marked_path D cardS d1 d3 distinct with ⟨q,qp,ql⟩|lx|ly
  · let Q : G.Walk x y := q.map f
    have qp' : Q.IsPath := (q.map_isPath_iff_of_injective Subtype.val_injective).mpr qp
    have ql' : 3  ≤  Q.length := by simpa [Q] using ql
    have safe (z : V) (m : z∈Q.support) : z∉p.support := by
      rw [show Q=q.map f from rfl,support_map] at m
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp m
      exact H.off _ w.property
    have gap := component_pins_spaced_four hc even conn degree hp ah bh H xh yh xi yj lt
    have jr := (pin_data yj).1
    by_cases twist : i   ≤   3
    · exact (no_longest_with_long_omitted_path_between_sites hp.1 Q qp' safe lt jr.le
        (by omega) (pin_data xi).2 (pin_data yj).2).elim
    by_cases opposite : 8   ≤   j
    · have j' : p.length-j∈Pins p.reverse y := reverse_pin hp.1 yo yj
      have i' : p.length-i∈Pins p.reverse x := reverse_pin hp.1 xo xi
      have lenQ : 3   ≤   Q.reverse.length := by simpa using ql'
      exact (no_longest_with_long_omitted_path_between_sites (reverse_long hp.1)
        Q.reverse qp'.reverse (fun z zn=>by simpa [support_reverse] using safe z (by simpa using zn))
        (by omega) (pin_data i').1.le (by omega) (pin_data j').2 (pin_data i').2).elim
    omega
  · have hn := neigh sx
    rw [lx,Finset.image_singleton] at hn
    exact False.elim (no_foreign_pin_at_omitted_leaf_neighbor_length_eleven hc even conn degree hp ah bh len H
      xh yh xi yj lt.ne hn.symm)
  · have hn := neigh sy
    rw [ly,Finset.image_singleton] at hn
    exact False.elim (no_foreign_pin_at_omitted_leaf_neighbor_length_eleven hc even conn degree hp ah bh len H
      yh xh yj xi lt.ne.symm hn.symm)


#print axioms distinct_pins_in_nontrivial_length_eleven_component

/-- A high-ended eleven-edge optimum omitting five vertices has a
nontrivial omitted component consisting of four or five vertices.
Its only spine attachments are exactly the two sites 4 and 7. -/
theorem length_eleven_five_off_has_central_component
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4  ≤  G.degree u ∨ 4  ≤  G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=5) :
    ∃ H : OmittedComponent p, 4  ≤  H.vertices.card ∧ H.vertices.card  ≤  5 ∧
      (∀ z∈H.vertices,(Pins p z).card  ≤  1) ∧
      (∀ z∈H.vertices,Pins p z⊆({4,7}:Finset ℕ)) ∧
      (∃ x∈H.vertices,4∈Pins p x) ∧ (∃ y∈H.vertices,7∈Pins p y) := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have oc : O.card=5 := off
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  obtain ⟨u,uo,v,vo,uv⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨w,wo,wd⟩ : ∃ w∈O,4  ≤  G.degree w := (degree u v uv).elim
    (fun h=>⟨u,uo,h⟩) (fun h=>⟨v,vo,h⟩)
  obtain ⟨S,wh,sne,soff,sclosed,sjoined⟩ := exists_omitted_component (out.mp wo)
  let H : OmittedComponent p := ⟨S,sne,soff,sclosed,sjoined⟩
  have sub : H.vertices⊆O := fun z hz=>out.mpr (H.off z hz)
  have upper := card_le_card sub
  have bd := omitted_degree_component_bound hp.1 H wh
  have two := (at_most_two_pins_one_slack hc 2 (by decide) (fun z=> distanceTwo_le_of_even 4 z (even z))
    conn degree hp (out.mp wo)).1
  have hlo : 2  ≤  H.vertices.card := by omega
  have one (z : V) (zh : z∈H.vertices) := single_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H hlo zh
  have hw := one w wh
  have large : 4  ≤  H.vertices.card := by omega
  have pinC := componentPins_card hp.1 H 2 conn
  obtain ⟨r,rm,s,sm,rs⟩ := one_lt_card.mp (show 1<(componentPins H).card by omega)
  obtain ⟨rp,x,xh,xr⟩ := mem_filter.mp rm
  obtain ⟨sp,y,yh,ys⟩ := mem_filter.mp sm
  obtain ⟨i,xi,ir⟩ := pin_of_neighbor_mem hp.1 (H.off _ xh) (List.mem_toFinset.mp rp) xr
  obtain ⟨j,yj,js⟩ := pin_of_neighbor_mem hp.1 (H.off _ yh) (List.mem_toFinset.mp sp) ys
  have ij : i≠j := fun e=>rs (ir.symm.trans ((congrArg p.getVert e).trans js))
  have lens : ∀ x∈H.vertices,∀ y∈H.vertices,∀ i∈Pins p x,∀ j∈Pins p y,i<j → i=4 ∧ j=7 := by
    intro x xh y yh i xi j yj ij
    exact distinct_pins_in_nontrivial_length_eleven_component hc even conn degree hp ah bh len H hlo
      (by omega) xh yh xi yj ij
  have sites : (∃ x∈H.vertices,4∈Pins p x) ∧ (∃ y∈H.vertices,7∈Pins p y) := by
    rcases lt_or_gt_of_ne ij with ij|ji
    · obtain ⟨rfl,rfl⟩ := lens x xh y yh i xi j yj ij
      exact ⟨⟨x,xh,xi⟩,⟨y,yh,yj⟩⟩
    · obtain ⟨rfl,rfl⟩ := lens y yh x xh j yj i xi ji
      exact ⟨⟨y,yh,yj⟩,⟨x,xh,xi⟩⟩
  refine ⟨H,large,by omega,one,?_,sites.1,sites.2⟩
  intro z zh k zk
  simp only [mem_insert,mem_singleton]
  obtain ⟨t,th,t4⟩ := sites.1
  by_cases k4 : k=4
  · exact .inl k4
  rcases lt_or_gt_of_ne k4 with lo|hi
  · have e := lens z zh t th k zk 4 t4 lo
    exact (by omega : False).elim
  · exact .inr (lens t th z zh 4 t4 k zk hi).2

#print axioms length_eleven_five_off_has_central_component

end Graffiti189LongestPath.TwoCut
