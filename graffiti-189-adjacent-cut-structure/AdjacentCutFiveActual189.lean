import AdjacentCutFiveBound189
import Mathlib.SetTheory.Cardinal.Finite

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem induced_reachable_of_walk_in (A : Finset V)
    {u v : V} (p : G.Walk u v) (stays : ∀ z∈p.support,z∈A)
    (ua : u∈A) (va : v∈A) :
    (G.induce (↑A : Set V)).Reachable ⟨u,ua⟩ ⟨v,va⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons u w z uw p ih =>
    have ps (t : V) (h : t∈p.support) : t∈A := stays t (by simpa only [support_cons,List.mem_cons] using Or.inr h)
    have wa := ps _ p.start_mem_support
    have e : (G.induce (↑A : Set V)).Adj ⟨u,ua⟩ ⟨w,wa⟩ := uw
    exact e.reachable.trans (ih ps wa va)

theorem induced_connected_of_joined (A : Finset V) (ne : A.Nonempty)
    (join : ∀ u∈A, ∀ v∈A, ∃ p : G.Walk u v,∀ z∈p.support,z∈A) :
    (G.induce (↑A : Set V)).Connected := by
  obtain ⟨x,xA⟩ := ne
  letI : Nonempty ↑(↑A : Set V) := ⟨⟨x,xA⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  obtain ⟨p,ps⟩ := join u.val u.property v.val v.property
  exact induced_reachable_of_walk_in A p ps u.property v.property

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

private abbrev CutGraph (a b : V) := G.induce {z : V | z≠a ∧ z≠b}

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

theorem actual_split (ab : a ≠ b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ S : CrossSaturation.Split G a b, (∃ x∈S.R,G.Adj a x) ∧ (∃ x∈S.R,G.Adj b x) := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change 2 ≤ Nat.card J.ConnectedComponent at cut
  rw [Nat.card_eq_fintype_card] at cut
  let F := Fintype.equivFin J.ConnectedComponent
  let C := F.symm ⟨0, by omega⟩
  let D := F.symm ⟨1, by omega⟩
  have CD : C ≠ D := by
    intro h
    have eq := congrArg Fin.val (F.symm.injective h)
    exact Nat.zero_ne_one eq
  let L := Shore C
  let R := (univ : Finset V).filter fun z => z≠a ∧ z≠b ∧ z∉L
  have test {z : V} : z∈R ↔ z≠a ∧ z≠b ∧ z∉L := by simp [R]
  have Dto : Shore D ⊆ R := by
    intro z hz
    obtain ⟨ne,_⟩ := mem_shore.mp hz
    exact test.mpr ⟨ne.1,ne.2,fun l=>disjoint_left.mp (shore_disjoint CD) l hz⟩
  refine ⟨⟨L,R,disjoint_left.mpr (fun _ hz hr=>(test.mp hr).2.2 hz),
    shore_off C,⟨fun h=>(test.mp h).1 rfl,fun h=>(test.mp h).2.1 rfl⟩,
    shore_connected C,?_,shore_hit_a ab conn C, shore_hit_b ab conn C,?_⟩, ?_, ?_⟩
  · intro u um v vm uv
    rcases shore_closed C u um v uv with h|h|h
    · exact (test.mp vm).1 h
    · exact (test.mp vm).2.1 h
    · exact (test.mp vm).2.2 h
  · intro z
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    by_cases zl : z∈L
    · exact .inr (.inr (.inl zl))
    · exact .inr (.inr (.inr (test.mpr ⟨za,zb,zl⟩)))
  · obtain ⟨x,xD,ax⟩ := shore_hit_a ab conn D
    exact ⟨x,Dto xD,ax⟩
  · obtain ⟨x,xD,bx⟩ := shore_hit_b ab conn D
    exact ⟨x,Dto xD,bx⟩

theorem order_le_twenty_one_of_actual_adjacent_cut (hc : G.Connected)
    (ab : G.Adj a b) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V ≤ 21 := by
  obtain ⟨S,ra,rb⟩ := actual_split ab.ne conn cut
  exact Split.order_le_twenty_one_of_adjacent_cut S hc even ab ra rb

theorem order_le_seventeen_of_actual_adjacent_twin_cut (hc : G.Connected)
    (ab : G.Adj a b) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z)) :
    Fintype.card V ≤ 17 := by
  obtain ⟨S,ra,_⟩ := actual_split ab.ne conn cut
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨y,yr,ay⟩ := ra
  exact Split.order_le_seventeen_of_twins S hc even ab xl yr (.inl ax) (.inl ay) twin

#print axioms order_le_twenty_one_of_actual_adjacent_cut
#print axioms order_le_seventeen_of_actual_adjacent_twin_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
