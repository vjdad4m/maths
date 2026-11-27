import CutDistance189
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

theorem exists_cut_pair (hc : G.Connected) (a b : V) (ab : a≠b)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del : ∀ b : V, (G.induce {x : V | x≠b}).Connected)
    (exactly : 2=Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent) :
    Nonempty (CutPair G a b) := by
  classical
  let J := G.induce {x : V | x≠a ∧ x≠b}
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card Bool = Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_bool,←Nat.card_eq_fintype_card]
    exact exactly
  let C := Fintype.equivOfCardEq n
  let H (i : Bool) : Finset V := Finset.univ.filter (fun x =>
    ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i)
  have mem {i : Bool} {x : V} : x∈H i ↔
      ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i := by simp [H]
  have ds (i j : Bool) (ij : i≠j) : Disjoint (H i) (H j) := by
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨hx,hi⟩ := mem.mp xi
    obtain ⟨_,hj⟩ := mem.mp xj
    exact ij (C.injective (hi.symm.trans hj))
  have off (i : Bool) : a∉H i ∧ b∉H i :=
    ⟨fun ha => (mem.mp ha).choose.1 rfl,fun hb => (mem.mp hb).choose.2 rfl⟩
  have closed (i : Bool) (x : V) (hx : x∈H i) (y : V) (xy : G.Adj x y) :
      y=a ∨ y=b ∨ y∈H i := by
    by_cases ya : y=a
    · exact Or.inl ya
    by_cases yb : y=b
    · exact Or.inr (Or.inl yb)
    obtain ⟨hx',hx''⟩ := mem.mp hx
    have edge : J.Adj ⟨x,hx'⟩ ⟨y,⟨ya,yb⟩⟩ := xy
    exact Or.inr (Or.inr (mem.mpr ⟨⟨ya,yb⟩,
      (ConnectedComponent.sound ⟨Walk.cons edge Walk.nil⟩).symm.trans hx''⟩))
  have joins (i : Bool) (x : V) (xi : x∈H i) (y : V) (yi : y∈H i) :
      ∃ q : G.Walk x y, ∀ z∈q.support,z∈H i := by
    obtain ⟨xoff,xc⟩ := mem.mp xi
    obtain ⟨yoff,yc⟩ := mem.mp yi
    obtain ⟨w⟩ := ConnectedComponent.exact (xc.trans yc.symm)
    let f : J →g G := { toFun := Subtype.val, map_rel' := fun a => a }
    refine ⟨w.map f,?_⟩
    intro z zw
    rw [support_map,List.mem_map] at zw
    obtain ⟨u,uw,rfl⟩ := zw
    have e := ConnectedComponent.sound ((show J.Reachable ⟨x,xoff⟩ u from ⟨w.takeUntil u uw⟩).symm)
    exact mem.mpr ⟨u.property,e.trans xc⟩
  have non (i : Bool) : (H i).Nonempty := by
    obtain ⟨x,hx⟩ := (C i).exists_rep
    exact ⟨x.val,mem.mpr ⟨x.property,hx⟩⟩
  have hit (i : Bool) (s t : V) (st : s≠t) (sout : s∉H i) (tout : t∉H i)
      (cl : ∀ x∈H i, ∀ y, G.Adj x y → y=s ∨ y=t ∨ y∈H i) :
      ∃ x∈H i,G.Adj s x := by
    by_cases h : ∃ x∈H i,G.Adj s x
    · exact h
    exfalso
    obtain ⟨x,xi⟩ := non i
    let K := G.induce {x : V | x≠t}
    let u : {x : V // x∈{x : V | x≠t}} := ⟨x,fun e => tout (e ▸ xi)⟩
    let v : {x : V // x∈{x : V | x≠t}} := ⟨s,st⟩
    obtain ⟨w⟩ := (del t) u v
    have stay {u v : {x : V // x∈{x : V | x≠t}}} (q : K.Walk u v)
        (hu : (u : V) ∈ H i) : (v : V) ∈ H i := by
      induction q with
      | nil => exact hu
      | @cons u v w uv q ih =>
        apply ih
        have uv' : G.Adj u.val v.val := uv
        rcases cl u.val hu v.val uv' with vs|vt|vv
        · exact (h ⟨u.val,hu,by simpa only [vs] using uv'.symm⟩).elim
        · exact (v.property vt).elim
        · exact vv
    exact sout (stay w xi)
  have ha (i : Bool) := hit i a b ab (off i).1 (off i).2 (closed i)
  have hb (i : Bool) := hit i b a ab.symm (off i).2 (off i).1
    (fun x hx y xy => (closed i x hx y xy).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))))
  have all (x : V) : x=a ∨ x=b ∨ ∃ i,x∈H i := by
    by_cases xa : x=a
    · exact Or.inl xa
    by_cases xb : x=b
    · exact Or.inr (Or.inl xb)
    let z : {x : V // x≠a ∧ x≠b} := ⟨x,xa,xb⟩
    obtain ⟨i,hi⟩ := C.surjective (J.connectedComponentMk z)
    exact Or.inr (Or.inr ⟨i,mem.mpr ⟨⟨xa,xb⟩,hi.symm⟩⟩)
  exact ⟨⟨hc,ab,even,degree,H,ds false true (by decide),off,all,closed,joins,ha,hb⟩⟩

/-- The cut-vertex pair of any two-component deletion has distance at most three. -/
theorem distance_le_three_at_two_component_cut (hc : G.Connected) (a b : V) (ab : a≠b)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del : ∀ b : V, (G.induce {x : V | x≠b}).Connected)
    (exactly : 2=Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent) :
    G.dist a b≤3 := by
  obtain ⟨S⟩ := exists_cut_pair hc a b ab even degree del exactly
  exact S.cut_distance

#print axioms distance_le_three_at_two_component_cut
end Graffiti189LongestPath.TwoCut
