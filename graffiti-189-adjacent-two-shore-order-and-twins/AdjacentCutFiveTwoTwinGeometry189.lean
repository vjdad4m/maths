import AdjacentCutFiveComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_nonempty shore_connected
  shore_hit_a shore_hit_b shore_disjoint from AdjacentCutFiveActual189
open private positive_cap from AdjacentCutFiveComponents189
open private mem_positive twins_dist_le d2 cross_dist_of_equal from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent
private abbrev IsTwin (G : SimpleGraph V) (a b : V) :=
  ∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z)

private theorem complete_from_no_local_even (hc : G.Connected)
    {C : Cmp G a b} {x : V} (xc : x∈Shore C)
    (ban : ∀ y∈Shore C, y∉PositiveEven G x) :
    ∀ y∈Shore C, y=x ∨ G.Adj x y := by
  classical
  intro y yc
  let H := G.induce (↑(Shore C) : Set V)
  let s : (↑(Shore C) : Set V) := ⟨x,xc⟩
  let t : (↑(Shore C) : Set V) := ⟨y,yc⟩
  have closed {u v : ↑(↑(Shore C) : Set V)} (uv : H.Adj u v)
      (mark : u.val=x ∨ G.Adj x u.val) : v.val=x ∨ G.Adj x v.val := by
    have ev : G.Adj u.val v.val := uv
    rcases mark with e | e
    · exact .inr (by simpa only [e] using ev)
    · by_cases vx : v.val=x
      · exact .inl vx
      · right
        by_contra no
        have D2 := d2 hc (Ne.symm vx) no e ev
        exact ban v.val v.property (mem_positive.mpr ⟨vx,by simp [(mem_filter.mp D2).2]⟩)
  have prop {u v : ↑(↑(Shore C) : Set V)} (q : H.Walk u v)
      (f : u.val=x ∨ G.Adj x u.val) : v.val=x ∨ G.Adj x v.val := by
    induction q with
    | nil => exact f
    | cons e q ih => exact ih (closed e f)
  obtain ⟨p⟩ := (shore_connected C).preconnected s t
  exact prop p (.inl rfl)

noncomputable def AdjTwinOdd (D : Cmp G a b) : Finset V :=
  (Shore D).filter (fun z => ¬ Even (G.dist a z))

noncomputable def AdjTwinEven (D : Cmp G a b) : Finset V :=
  (Shore D).filter (fun z => Even (G.dist a z))

theorem twin_dist_on_shore (hc : G.Connected) (twin : IsTwin G a b)
    {D : Cmp G a b} {z : V} (zd : z∈Shore D) :
    G.dist a z = G.dist b z := by
  have za : z≠a := fun h=>(shore_off D).1 (by simpa only [h] using zd)
  have zb : z≠b := fun h=>(shore_off D).2 (by simpa only [h] using zd)
  have e1 := twins_dist_le hc za.symm (fun v vb av=> (twin v av.ne.symm vb).mp av)
  have e2 := twins_dist_le hc zb.symm (fun v va bv=> (twin v va bv.ne.symm).mpr bv)
  omega

theorem adj_twin_odd_foreign (hc : G.Connected) (twin : IsTwin G a b)
    {C D : Cmp G a b} (cd : C≠D)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) :
    AdjTwinOdd D ⊆ PositiveEven G x := by
  classical
  intro z zo
  obtain ⟨zz,odd⟩ := mem_filter.mp zo
  have zo' : z∉Shore C := fun e=>disjoint_left.mp (shore_disjoint cd) e zz
  have nz : z≠x := fun h=>zo' (by simpa only [h] using xc)
  have form := cross_dist_of_equal (Shore C) hc xc zo' (shore_closed C) (.inl ax)
    (twin_dist_on_shore hc twin zz)
  refine mem_positive.mpr ⟨nz,?_⟩
  rw [form]
  change ¬ Even (G.dist a z) at odd
  simp only [Nat.even_iff] at odd ⊢
  omega

theorem adj_twin_port_universal_of_odd_five (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6) (twin : IsTwin G a b)
    {C D : Cmp G a b} (cd : C≠D) (five : (AdjTwinOdd D).card = 5)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) :
    ∀ y∈Shore C, y=x ∨ G.Adj x y := by
  classical
  apply complete_from_no_local_even hc xc
  intro z zc ze
  have sub := adj_twin_odd_foreign hc twin cd xc ax
  have zo : z∉AdjTwinOdd D := fun h => disjoint_left.mp (shore_disjoint cd) zc
    (mem_filter.mp h).1
  have allsub : insert z (AdjTwinOdd D) ⊆ PositiveEven G x := by
    intro u hu
    rcases mem_insert.mp hu with rfl|h
    · exact ze
    · exact sub h
  have e := card_le_card allsub
  rw [card_insert_of_not_mem zo, five] at e
  have q := positive_cap x even
  omega

#print axioms adj_twin_port_universal_of_odd_five
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
