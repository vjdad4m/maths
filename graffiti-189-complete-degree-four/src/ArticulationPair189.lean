import ArticulationOrder189
import ArticulationThree189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure ArticulationPair (G : SimpleGraph V) (c : V) where
  L : Finset V
  R : Finset V
  dis : Disjoint L R
  offL : c∉L
  offR : c∉R
  cover : ∀ v,v=c ∨ v∈L ∨ v∈R
  cross : ∀ x∈L,∀ y∈R, ¬G.Adj x y
  joinedL : (G.induce (↑L : Set V)).Connected
  joinedR : (G.induce (↑R : Set V)).Connected
  hitL : ∃ x∈L,G.Adj c x
  hitR : ∃ x∈R,G.Adj c x

theorem articulation_pair_of_disconnected (hc : G.Connected) (c : V)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : 2≤Fintype.card V)
    (cut : ¬(G.induce {z : V | z≠c}).Connected) : Nonempty (ArticulationPair G c) := by
  classical
  let J := G.induce {z : V | z≠c}
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun v=>v.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have hi := component_card_le_two_at_articulation hc c even degree
  change Nat.card J.ConnectedComponent≤2 at hi
  have lo : 1<Nat.card J.ConnectedComponent := by
    by_contra! small
    have sm : Fintype.card J.ConnectedComponent≤1 := by rw [←Nat.card_eq_fintype_card]; exact small
    have ss := Fintype.card_le_one_iff_subsingleton.mp sm
    have ex : ∃ x : V,x≠c := by
      by_contra! all
      have sub : univ ⊆ ({c} : Finset V) := fun _ _ => by simp [all]
      have h := card_le_card sub
      rw [card_univ,card_singleton] at h
      omega
    obtain ⟨x,xo⟩ := ex
    letI : Nonempty ↑({z : V | z≠c} : Set V) := ⟨⟨x,xo⟩⟩
    apply cut
    exact Connected.mk (fun s t=>ConnectedComponent.exact
      (ss.elim (J.connectedComponentMk s) (J.connectedComponentMk t)))
  have eq : Fintype.card Bool=Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_bool,←Nat.card_eq_fintype_card]
    exact (by omega : 2=Nat.card J.ConnectedComponent)
  let C := Fintype.equivOfCardEq eq
  let H (i : Bool) : Finset V := univ.filter (fun x=>∃ h : x≠c,J.connectedComponentMk ⟨x,h⟩=C i)
  have mem {i : Bool} {x : V} : x∈H i ↔ ∃ h : x≠c,J.connectedComponentMk ⟨x,h⟩=C i := by simp [H]
  have off (i : Bool) : c∉H i := fun h=>(mem.mp h).choose rfl
  have nonempty (i : Bool) : (H i).Nonempty := by
    obtain ⟨x,hx⟩ := (C i).exists_rep
    exact ⟨x.val,mem.mpr ⟨x.property,hx⟩⟩
  have closed (i : Bool) (x : V) (xi : x∈H i) (y : V) (xy : G.Adj x y) :
      y=c ∨ y∈H i := by
    by_cases yc : y=c
    · exact .inl yc
    obtain ⟨xc,xi⟩ := mem.mp xi
    have e : J.Adj ⟨x,xc⟩ ⟨y,yc⟩ := xy
    exact .inr (mem.mpr ⟨yc,(ConnectedComponent.sound e.reachable).symm.trans xi⟩)
  have joined (i : Bool) : (G.induce (↑(H i) : Set V)).Connected := by
    apply induced_connected_of_joined (H i) (nonempty i)
    intro x xi y yi
    obtain ⟨xc,ci⟩ := mem.mp xi
    obtain ⟨yc,di⟩ := mem.mp yi
    obtain ⟨w⟩ := ConnectedComponent.exact (ci.trans di.symm)
    let f : J →g G := {toFun := Subtype.val, map_rel' := fun e=>e}
    refine ⟨w.map f,?_⟩
    intro z hz
    rw [support_map,List.mem_map] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    have r := ConnectedComponent.sound (w.takeUntil v hv).reachable
    exact mem.mpr ⟨v.property,r.symm.trans ci⟩
  have hit (i : Bool) : ∃ x∈H i,G.Adj c x := by
    apply Classical.byContradiction
    intro no
    obtain ⟨v,vi⟩ := nonempty i
    obtain ⟨w⟩ := hc.preconnected v c
    have stay {x y : V} (p : G.Walk x y) : x∈H i → y∈H i := by
      induction p with
      | nil => exact id
      | @cons x z y xz p ih =>
        intro xi
        apply ih
        rcases closed i x xi z xz with e|h
        · exact (no ⟨x,xi,e ▸ xz.symm⟩).elim
        · exact h
    exact off i (stay w vi)
  have dis : Disjoint (H false) (H true) := by
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨h,hi⟩ := mem.mp xi
    obtain ⟨_,hj⟩ := mem.mp xj
    exact Bool.false_ne_true (C.injective (hi.symm.trans hj))
  have all (x : V) : x=c ∨ x∈H false ∨ x∈H true := by
    by_cases xo : x=c
    · exact .inl xo
    obtain ⟨i,hi⟩ := C.surjective (J.connectedComponentMk ⟨x,xo⟩)
    cases i
    · exact .inr (.inl (mem.mpr ⟨xo,hi.symm⟩))
    · exact .inr (.inr (mem.mpr ⟨xo,hi.symm⟩))
  have cross (x : V) (xi : x∈H false) (y : V) (yj : y∈H true) : ¬G.Adj x y := by
    intro xy
    rcases closed false x xi y xy with yc|yi
    · exact off true (yc ▸ yj)
    exact disjoint_left.mp dis yi yj
  exact ⟨⟨H false,H true,dis,off false,off true,all,cross,joined false,joined true,hit false,hit true⟩⟩

namespace ArticulationPair
variable {c : V} (S : ArticulationPair G c)

include S in
theorem order_le_thirteen (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card≤5) :
    Fintype.card V≤13 := by
  obtain ⟨x,xl,cx⟩ := S.hitL
  obtain ⟨y,yr,cy⟩ := S.hitR
  exact order_le_three_times_budget_plus_one_at_articulation hc 4 even S.L S.R S.dis S.cross S.cover xl yr cx cy

theorem sides_le_eight (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card≤5) :
    S.L.card≤8 ∧ S.R.card≤8 := by
  obtain ⟨x,xl,cx⟩ := S.hitL
  obtain ⟨y,yr,cy⟩ := S.hitR
  have hl := side_and_opposite_even_le_twice_budget hc 4 even S.L S.R S.dis S.offL S.cross S.cover yr cy
  have hr := side_and_opposite_even_le_twice_budget hc 4 even S.R S.L S.dis.symm S.offR
    (fun y yr x xl h=>S.cross _ xl _ yr h.symm)
    (fun z=>by simpa only [or_comm (a:=z∈S.L) (b:=z∈S.R)] using S.cover z) xl cx
  omega


/-- Concatenating paths rooted at the articulation gives a spanning path. -/
theorem splice_rooted (left : ∃ a,∃ p : G.Walk c a,p.IsPath ∧
      ∀ z,z∈p.support ↔ z=c ∨ z∈S.L)
    (right : ∃ b,∃ q : G.Walk c b,q.IsPath ∧
      ∀ z,z∈q.support ↔ z=c ∨ z∈S.R) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  obtain ⟨a,p,pp,ps⟩ := left
  obtain ⟨b,q,qp,qs⟩ := right
  refine ⟨a,b,p.reverse.append q,?_,?_⟩
  · rw [isPath_def,support_append,List.nodup_append]
    refine ⟨pp.reverse.support_nodup,qp.support_nodup.tail,?_⟩
    intro z zp zq
    have z1 : z∈p.support := by simpa using zp
    have z2 : z∈q.support := List.mem_of_mem_tail zq
    have zc : z≠c := by
      intro e
      subst z
      cases q with
      | nil => simp at zq
      | cons e q =>
        exact ((cons_isPath_iff _ _).mp qp).2 (by simpa only [support_cons,List.tail_cons] using zq)
    exact disjoint_left.mp S.dis ((ps z).mp z1 |>.resolve_left zc) ((qs z).mp z2 |>.resolve_left zc)
  · intro z
    rw [mem_support_append_iff]
    rcases S.cover z with zc|zl|zr
    · exact Or.inr ((qs _).mpr (Or.inl zc))
    · exact Or.inl (by simpa using (ps _).mpr (Or.inr zl))
    · exact Or.inr ((qs _).mpr (Or.inr zr))

end ArticulationPair
#print axioms ArticulationPair.splice_rooted
#print axioms articulation_pair_of_disconnected
#print axioms ArticulationPair.order_le_thirteen
#print axioms ArticulationPair.sides_le_eight
end Graffiti189LongestPath.CrossSaturation
