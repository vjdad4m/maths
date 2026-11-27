import DegreeFiveFarThree189
import DegreeFiveFarCut189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private abbrev CutGraph (a b : V) := G.induce {z : V | z≠a ∧ z≠b}
variable {a b : V}

private noncomputable def Shore (C : (CutGraph (G:=G) a b).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter fun x=>∃ h : x≠a ∧ x≠b,
    (CutGraph (G:=G) a b).connectedComponentMk ⟨x,h⟩=C

private theorem mem_shore {C : (CutGraph (G:=G) a b).ConnectedComponent} {x : V} :
    x∈Shore C ↔ ∃ h : x≠a ∧ x≠b,(CutGraph (G:=G) a b).connectedComponentMk ⟨x,h⟩=C := by
  classical simp [Shore]

private theorem shore_off (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    a∉Shore C ∧ b∉Shore C :=
  ⟨fun h=>(mem_shore.mp h).choose.1 rfl,fun h=>(mem_shore.mp h).choose.2 rfl⟩

private theorem shore_nonempty (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    (Shore C).Nonempty := by
  obtain ⟨x,hx⟩ := C.exists_rep
  exact ⟨x.val,mem_shore.mpr ⟨x.property,hx⟩⟩

private theorem shore_disjoint {C D : (CutGraph (G:=G) a b).ConnectedComponent} (ne : C≠D) :
    Disjoint (Shore C) (Shore D) := by
  apply disjoint_left.mpr
  intro z zc zd
  obtain ⟨h,e⟩ := mem_shore.mp zc
  obtain ⟨_,f⟩ := mem_shore.mp zd
  exact ne (e.symm.trans f)

private theorem shore_closed (C : (CutGraph (G:=G) a b).ConnectedComponent)
    (x : V) (xc : x∈Shore C) (y : V) (xy : G.Adj x y) :
    y=a ∨ y=b ∨ y∈Shore C := by
  by_cases ya : y=a
  · exact .inl ya
  by_cases yb : y=b
  · exact .inr (.inl yb)
  obtain ⟨hx,e⟩ := mem_shore.mp xc
  have xy' : (CutGraph (G:=G) a b).Adj ⟨x,hx⟩ ⟨y,ya,yb⟩ := xy
  exact .inr (.inr (mem_shore.mpr ⟨⟨ya,yb⟩,(ConnectedComponent.sound xy'.reachable).symm.trans e⟩))

private theorem shore_connected (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    (G.induce (↑(Shore C) : Set V)).Connected := by
  apply induced_connected_of_joined _ (shore_nonempty C)
  intro x xc y yc
  obtain ⟨hx,e⟩ := mem_shore.mp xc
  obtain ⟨hy,f⟩ := mem_shore.mp yc
  obtain ⟨q⟩ := ConnectedComponent.exact (e.trans f.symm)
  let φ : CutGraph (G:=G) a b →g G := {toFun := Subtype.val, map_rel' := fun e=>e}
  refine ⟨q.map φ,?_⟩
  intro z hz
  rw [support_map,List.mem_map] at hz
  obtain ⟨w,wm,rfl⟩ := hz
  have r := ConnectedComponent.sound (q.takeUntil w wm).reachable
  exact mem_shore.mpr ⟨w.property,r.symm.trans e⟩

private theorem shore_hit_a (ab : a≠b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ x∈Shore C,G.Adj a x :=
  side_hits_first_after_deleting_second ab (Shore C) (shore_nonempty C)
    (shore_off C).1 (shore_off C).2 (shore_closed C) (conn {b} (by simp))

private theorem shore_hit_b (ab : a≠b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (C : (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ x∈Shore C,G.Adj b x :=
  side_hits_first_after_deleting_second ab.symm (Shore C) (shore_nonempty C)
    (shore_off C).2 (shore_off C).1
    (fun x xc y e=>by simpa only [or_left_comm] using shore_closed C x xc y e) (conn {a} (by simp))

private theorem ab_ne (far : 3≤G.dist a b) : a≠b := by
  intro h
  rw [h,SimpleGraph.dist_self] at far
  omega

/-- For the degree-five hypotheses, a separating pair at distance at
least three leaves at most two components. -/
theorem component_card_le_two_at_cut_distance_ge_three (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    Nat.card (CutGraph (G:=G) a b).ConnectedComponent≤2 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent ≤2
  rw [Nat.card_eq_fintype_card]
  by_contra! many
  have h3 : 3≤Fintype.card J.ConnectedComponent := by omega
  let C (i : Fin 3) := (Fintype.equivFin J.ConnectedComponent).symm (Fin.castLE h3 i)
  have inj : Function.Injective C := by
    intro i j e
    have h := (Fintype.equivFin J.ConnectedComponent).symm.injective e
    exact Fin.ext (congrArg (fun u : Fin (Fintype.card J.ConnectedComponent)=>u.val) h)
  let S : FarThreeShores G a b :=
    ⟨fun i=>Shore (C i),fun i j ne=>shore_disjoint (fun h=>ne (inj h)),
      fun i=>shore_off (C i),fun i=>shore_closed (C i),fun i=>shore_connected (C i),
      fun i=>shore_hit_a (ab_ne far) conn (C i),fun i=>shore_hit_b (ab_ne far) conn (C i)⟩
  exact S.impossible hc far even degree

private theorem order_ge_three_from_dist (hc : G.Connected) (far : 3≤G.dist a b) :
    3≤Fintype.card V := by
  classical
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist a b
  have ab := ab_ne far
  cases q with
  | nil => exact (ab rfl).elim
  | @cons a x b ax q =>
    have xb : x≠b := by
      intro e
      have h : G.Adj a b := e ▸ ax
      have one := dist_eq_one_iff_adj.mpr h
      omega
    have ax' := ax.ne
    have count := card_le_univ ({a,x,b}:Finset V)
    simp [ax',ab,xb] at count
    omega

/-- No two-vertex cut in the degree-five case can have its cut vertices
at graph distance four or more. Unlike the two-shore lemma, this takes an
arbitrary actual disconnected induced deletion. -/
theorem cut_distance_le_three_at_actual_five_cut (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected) :
    G.dist a b≤3 := by
  classical
  by_contra bad
  have far : 3≤G.dist a b := by omega
  have ab := ab_ne far
  let J := CutGraph (G:=G) a b
  have hi := component_card_le_two_at_cut_distance_ge_three hc far even conn degree
  have lo := component_card_gt_one_of_disconnected a b (order_ge_three_from_dist hc far) cut
  change 1<Nat.card J.ConnectedComponent at lo
  change Nat.card J.ConnectedComponent≤2 at hi
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card Bool=Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_bool,←Nat.card_eq_fintype_card]
    omega
  let C := Fintype.equivOfCardEq n
  let L := Shore (C false)
  let R := Shore (C true)
  have dis : Disjoint L R := shore_disjoint (fun h=>Bool.false_ne_true (C.injective h))
  have cover (x : V) : x=a ∨ x=b ∨ x∈L ∨ x∈R := by
    by_cases xa : x=a
    · exact .inl xa
    by_cases xb : x=b
    · exact .inr (.inl xb)
    obtain ⟨i,e⟩ := C.surjective (J.connectedComponentMk ⟨x,xa,xb⟩)
    cases i
    · exact .inr (.inr (.inl (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
    · exact .inr (.inr (.inr (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
  have cross (x : V) (xl : x∈L) (y : V) (yr : y∈R) : ¬G.Adj x y := by
    intro xy
    have yr' : y∈Shore (C true) := yr
    rcases shore_closed (C false) x xl y xy with p|p|p
    · exact (shore_off (C true)).1 (p ▸ yr')
    · exact (shore_off (C true)).2 (p ▸ yr')
    exact disjoint_left.mp dis p yr
  let S : Split G a b :=
    ⟨L,R,dis,shore_off (C false),shore_off (C true),shore_connected (C false),cross,
      shore_hit_a ab conn (C false),shore_hit_b ab conn (C false),cover⟩
  exact bad (Split.Five.cut_distance_le_three_at_five S hc even conn degree (shore_connected (C true)))

#print axioms component_card_le_two_at_cut_distance_ge_three
#print axioms cut_distance_le_three_at_actual_five_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
