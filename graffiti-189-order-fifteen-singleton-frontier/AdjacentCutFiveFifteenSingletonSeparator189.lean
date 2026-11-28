import AdjacentCutFiveFifteenSingletonDepth189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from AdjacentCutFiveActual189
open private classSet from AdjacentCutFiveTopProfiles189
open private no_both_two_of_empty_equal_even from AdjacentCutFiveSixteenSingletonDepth189
open private d2 mem_positive from AdjacentCutFiveBound189
open private foreign_pos_even from AdjacentCutFiveComponents189
open private cannot_fit_four_and_two_more from AdjacentCutFiveSixteenSingletonGeometry189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem disconnected_remove_two_of_dark_exclusive_no_edges
    (hc : G.Connected)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (sc : s∈Shore C)
    (zero : (classSet D 2).card=0)
    {x y v : V} (xd : x∈Shore D) (yd : y∈Shore D)
    (xPort : G.Adj a x ∨ G.Adj b x) (yPort : G.Adj a y ∨ G.Adj b y)
    (vDark : v∈Shore D ∧ ¬G.Adj a v ∧ ¬G.Adj b v)
    (block : ∀ w∈Shore D, w≠x → w≠y →
      ((G.Adj a w ∧ ¬G.Adj b w) ∨ (G.Adj b w ∧ ¬G.Adj a w)) →
      ∀ u∈Shore D, ¬G.Adj a u → ¬G.Adj b u → ¬G.Adj w u) :
    ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected := by
  classical
  have notSD : s∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) sc h
  intro conn'
  let U : Set V := {z : V | z≠x ∧ z≠y}
  have sx : s≠x := fun e=>notSD (e.symm ▸ xd)
  have sy : s≠y := fun e=>notSD (e.symm ▸ yd)
  have vx : v≠x := fun e=>xPort.elim (fun h=>vDark.2.1 (e.symm ▸ h)) (fun h=>vDark.2.2 (e.symm ▸ h))
  have vy : v≠y := fun e=>yPort.elim (fun h=>vDark.2.1 (e.symm ▸ h)) (fun h=>vDark.2.2 (e.symm ▸ h))
  have stay {u w : U} (p : (G.induce U).Walk u w) :
      (u.val∈Shore D ∧ ¬G.Adj a u.val ∧ ¬G.Adj b u.val) →
      (w.val∈Shore D ∧ ¬G.Adj a w.val ∧ ¬G.Adj b w.val) := by
    induction p with
    | nil => exact id
    | @cons u t w edge p ih =>
      intro ⟨ud,au,bu⟩
      apply ih
      have e : G.Adj u.val t.val := edge
      rcases shore_closed D _ ud _ e with ha|hb|td
      · exact (au (by simpa only [ha] using e.symm)).elim
      · exact (bu (by simpa only [hb] using e.symm)).elim
      refine ⟨td,?_⟩
      have both (at' : G.Adj a t.val) (bt : G.Adj b t.val) : False := by
        have ua : u.val≠a := fun f=>(shore_off D).1 (Eq.mp (congrArg (fun h : V => h∈Shore D) f) ud)
        have ub : u.val≠b := fun f=>(shore_off D).2 (Eq.mp (congrArg (fun h : V => h∈Shore D) f) ud)
        have dA := (mem_filter.mp (d2 hc ua.symm au at' e.symm)).2
        have dB := (mem_filter.mp (d2 hc ub.symm bu bt e.symm)).2
        exact no_both_two_of_empty_equal_even zero ud dA dB
      have excl (h : (G.Adj a t.val ∧ ¬G.Adj b t.val) ∨ (G.Adj b t.val ∧ ¬G.Adj a t.val)) : False :=
        block _ td t.property.1 t.property.2 h _ ud au bu e.symm
      exact ⟨fun h=>if j : G.Adj b t.val then both h j else excl (.inl ⟨h,j⟩),
        fun h=>if j : G.Adj a t.val then both j h else excl (.inr ⟨h,j⟩)⟩
  obtain ⟨p⟩ := conn'.preconnected (⟨v,⟨vx,vy⟩⟩ : U) ⟨s,⟨sx,sy⟩⟩
  exact notSD (stay p vDark).1

#print axioms disconnected_remove_two_of_dark_exclusive_no_edges

private theorem nonedge_of_right_port_four_dark_neighbors
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤6)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (sc : s∈Shore C) (sa : G.Adj a s)
    {x y : V} (xd : x∈Shore D) (ax : G.Adj a x) (bx : ¬G.Adj b x)
    (yw : ∀ w∈classSet D 1,G.Adj y w)
    (four : 4≤(classSet D 1).card)
    (da : ∀ w∈classSet D 1,G.dist a w=3) : ¬G.Adj x y := by
  intro xy
  let B := classSet D 1
  have x1 := dist_eq_one_iff_adj.mpr ax
  have bSee : B⊆PositiveEven G x := by
    intro u um
    have p := da u um
    have ne : x≠u := fun e=>by rw [e,p] at x1; omega
    have no : ¬G.Adj x u := by
      intro h
      have t := hc.dist_triangle (u:=a) (v:=x) (w:=u)
      rw [p,x1,dist_eq_one_iff_adj.mpr h] at t
      omega
    have d := (mem_filter.mp (d2 hc ne no xy (yw u um))).2
    exact mem_positive.mpr ⟨ne.symm,by simp [d]⟩
  have xB : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have dxB := (mem_filter.mp (d2 hc xB.symm bx ab.symm ax)).2
  have bPos : b∈PositiveEven G x := mem_positive.mpr ⟨xB.symm,by rw [dist_comm,dxB]; decide⟩
  have sPos := foreign_pos_even hc cd.symm xd sc ax sa
  exact cannot_fit_four_and_two_more even four bSee
    (fun h=>disjoint_left.mp (shore_disjoint cd) sc (mem_filter.mp h).1)
    (fun h=>(shore_off D).2 (mem_filter.mp h).1)
    (fun e=>(shore_off C).2 (e.symm ▸ sc)) sPos bPos

#print axioms nonedge_of_right_port_four_dark_neighbors
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
