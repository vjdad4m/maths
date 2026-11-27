import RemoteSquareBudgetConditional
import RemoteDegreeTwoEnds

namespace KelmansCactus.AtomicBridge.RemoteSquareStripAuto
open SimpleGraph Finset
open RemoteBudgetComponent (Mate exchangeGraph different_reaches)
open RemoteSquareBudgetConditional (Square Decomposition)
open RemotePairStrip (Strip Closed)
variable {V : Type*} {G : SimpleGraph V} {p : Mate G} (A : Square p) (q : Mate G)

def Outside (x : V) : Prop := ∀ i,x≠A.corner i

theorem outside_contact (i : Fin 4) : Outside A (p.mate (A.corner i)) :=
  A.external i

def H : SimpleGraph V where
  Adj x y := Outside A x ∧ Outside A y ∧ (exchangeGraph p q).Adj x y
  symm := fun _ _ h=>⟨h.2.1,h.1,h.2.2.symm⟩
  loopless := fun x h=>(exchangeGraph p q).loopless x h.2.2

theorem H_le_exchange : H A q≤exchangeGraph p q := fun _ _ h=>h.2.2
theorem H_le_G : H A q≤G := by
  intro x y h
  rcases h.2.2 with l|r
  · exact l ▸ p.edge x
  · exact r ▸ q.edge x

theorem active_contact {i : Fin 4} (openI : A.openPort q i) :
    p.mate (p.mate (A.corner i))≠q.mate (p.mate (A.corner i)) := by
  intro fixed
  apply openI
  apply Mate.reverse
  exact (p.inv _).symm.trans fixed |>.symm

/-- At a vertex where the matchings differ, the target cannot enter the
square from outside: a corner has only its one old outside contact. -/
theorem target_stays {x : V} (out : Outside A x) (active : p.mate x≠q.mate x) :
    Outside A (q.mate x) := by
  intro i e
  have qm := Mate.reverse e
  have adj := q.edge (A.corner i)
  rw [qm] at adj
  rcases A.only i x adj with c|⟨j,_,z⟩
  · exact active ((Mate.reverse (q:=p) c.symm).trans e.symm)
  · exact out j z

theorem out_of_reach {x y : V} (outside : Outside A x) (r : (H A q).Reachable x y) :
    Outside A y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => exact outside
  | tail _ e _ => exact e.2.1

theorem reachable_p {x : V} (out : Outside A x) (nout : Outside A (p.mate x)) :
    (H A q).Adj x (p.mate x) := ⟨out,nout,Or.inl rfl⟩

theorem reachable_q {x : V} (out : Outside A x) (nout : Outside A (q.mate x)) :
    (H A q).Adj x (q.mate x) := ⟨out,nout,Or.inr rfl⟩

section finite
variable [Fintype V]

private noncomputable instance decOutside (x : V) : Decidable (Outside A x) :=
  Classical.propDecidable _

private noncomputable instance decH : DecidableRel (H A q).Adj := by
  classical
  exact fun _ _ => Classical.propDecidable _

theorem degrees {x : V} (out : Outside A x) (active : p.mate x≠q.mate x) :
    (H A q).degree x=(if Outside A (p.mate x) then 2 else 1) := by
  classical
  have qo := target_stays A q out active
  by_cases po : Outside A (p.mate x)
  · have shape : (H A q).neighborFinset x = {p.mate x,q.mate x} := by
      ext y
      rw [SimpleGraph.mem_neighborFinset]
      change (Outside A x ∧ Outside A y ∧ (p.mate x=y ∨ q.mate x=y)) ↔ _
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨_,_,l|r⟩
        · exact Or.inl l.symm
        · exact Or.inr r.symm
      · rintro (rfl|rfl)
        · exact ⟨out,po,Or.inl rfl⟩
        · exact ⟨out,qo,Or.inr rfl⟩
    rw [if_pos po,←SimpleGraph.card_neighborFinset_eq_degree,shape]
    simp [active]
  · have shape : (H A q).neighborFinset x = {q.mate x} := by
      ext y
      rw [SimpleGraph.mem_neighborFinset]
      change (Outside A x ∧ Outside A y ∧ (p.mate x=y ∨ q.mate x=y)) ↔ _
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨_,outside,l|r⟩
        · exact (po (l.symm ▸ outside)).elim
        · exact r.symm
      · rintro rfl
        exact ⟨out,qo,Or.inr rfl⟩
    rw [if_neg po,←SimpleGraph.card_neighborFinset_eq_degree,shape]
    simp

structure LinkedStrip (i : Fin 4) where
  j : Fin 4
  ne : i≠j
  opened : A.openPort q j
  strip : A.OutsideStrip q i j
  exact_region : ∀ x,x∈strip.strip.region ↔
    (H A q).Reachable (p.mate (A.corner i)) x
  only_contacts : ∀ t,p.mate (A.corner t)∈strip.strip.region → t=i∨t=j

/-- Exterior symmetric-difference components meeting an opened port are
finite paths with exactly two opened endpoints. This derives the strip
hypothesis from two genuine perfect matchings to the exact square. -/
noncomputable def linked_strip (i : Fin 4) (openI : A.openPort q i) :
    LinkedStrip A q i := by
  classical
  let start := p.mate (A.corner i)
  let X := H A q
  let C := X.connectedComponentMk start
  let S := C.supp
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  let Y := X.induce S
  have ismem (x : V) : x∈S ↔ X.Reachable start x := by
    simp only [S,C,SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact SimpleGraph.reachable_comm
  have aS : start∈S := (ismem _).mpr (SimpleGraph.Reachable.refl _)
  have inactive (x : V) (hx : x∈S) : p.mate x≠q.mate x :=
    different_reaches p q (active_contact A q openI) (((ismem x).mp hx).mono (H_le_exchange A q))
  have outside (x : V) (hx : x∈S) : Outside A x :=
    out_of_reach A q (outside_contact A i) ((ismem x).mp hx)
  have same_deg (x : S) : Y.degree x = X.degree x := by
    apply X.degree_induce_of_neighborSet_subset
    intro y hy
    exact C.mem_supp_congr_adj ((SimpleGraph.mem_neighborSet _ _ _).mp hy) |>.mp x.property
  have formula (x : S) : Y.degree x=(if Outside A (p.mate x.val) then 2 else 1) := by
    rw [same_deg]
    exact degrees A q (outside x.val x.property) (inactive x.val x.property)
  have yesDeg (x : S) : Y.degree x=1 ∨ Y.degree x=2 := by
    rw [formula]
    split <;> simp
  let u : S := ⟨start,aS⟩
  have oneU : Y.degree u=1 := by
    rw [formula,if_neg]
    intro o
    exact o i (p.inv _)
  have count := RemoteDegreeTwoEnds.count_endpoints (G:=Y) C.connected_induce_supp yesDeg oneU
  let ends : Finset S := Finset.univ.filter fun x=>Y.degree x=1
  have E : ∃ v : S,v≠u ∧ Y.degree v=1 ∧
      ∀ w : S,Y.degree w=1 → w=u∨w=v := by
    obtain ⟨a,b,ab,h⟩ := Finset.card_eq_two.mp count
    have shape : ends={a,b} := h
    have ha : Y.degree a=1 := by
      have e : a∈ends := by simp [shape]
      exact (Finset.mem_filter.mp e).2
    have hb : Y.degree b=1 := by
      have e : b∈ends := by simp [shape]
      exact (Finset.mem_filter.mp e).2
    have all w (hw : Y.degree w=1) : w=a∨w=b := by
      have hmem : w∈ends := by simp [ends,hw]
      simpa [shape] using hmem
    rcases all u oneU with e|e
    · exact ⟨b,fun n=>ab (e.symm.trans n.symm),hb,fun w hw=>(e.symm ▸ all w hw)⟩
    · exact ⟨a,fun n=>ab (n.trans e),ha,fun w hw=>(all w hw).symm |> (e.symm ▸ ·)⟩
  let v := E.choose
  have vNe := E.choose_spec.1
  have vDeg := E.choose_spec.2.1
  have end_unique := E.choose_spec.2.2
  have bad : ¬Outside A (p.mate v.val) := by
    intro out
    have := formula v
    rw [if_pos out,vDeg] at this
    contradiction
  simp only [Outside,not_forall,not_not] at bad
  let j := bad.choose
  have jEq := bad.choose_spec
  have vPort : p.mate (A.corner j)=v.val := Mate.reverse jEq
  have neq : i≠j := by
    intro eq
    exact vNe (Subtype.ext (vPort.symm.trans (congrArg (fun z=>p.mate (A.corner z)) eq.symm)))
  have oj : A.openPort q j := by
    intro eq
    apply inactive v.val v.property
    exact jEq.trans ((Mate.reverse (eq.trans vPort)).symm)
  have only : ∀ t,p.mate (A.corner t)∈S → t=i∨t=j := by
    intro t mt
    let w : S := ⟨p.mate (A.corner t),mt⟩
    have hdeg : Y.degree w=1 := by
      rw [formula,if_neg]
      intro outside
      exact outside t (p.inv _)
    rcases end_unique w hdeg with a|b
    · exact Or.inl (A.distinct (p.inv.injective (congrArg Subtype.val a)))
    · exact Or.inr (A.distinct (p.inv.injective ((congrArg Subtype.val b).trans vPort.symm)))
  have bw : p.mate (A.corner j)∈S := by
    rw [vPort]
    exact v.property
  have corner_out (t : Fin 4) : A.corner t∉S := fun h=>outside _ h t rfl
  let T : Strip p q (A.corner i) (A.corner j) := {
    region := S
    aOut := corner_out i
    bOut := corner_out j
    pa := aS
    pb := bw
    p_internal := by
      intro x mx xi xj
      have stay : Outside A (p.mate x) := by
        intro t ht
        have e := Mate.reverse ht
        rcases only t (e.symm ▸ mx) with rfl|rfl
        · exact xi e.symm
        · exact xj e.symm
      exact (ismem _).mpr (((ismem x).mp mx).trans
        (reachable_p A q (outside x mx) stay).reachable)
    q_internal := by
      intro x mx
      exact (ismem _).mpr (((ismem x).mp mx).trans
        (reachable_q A q (outside x mx) (target_stays A q (outside x mx) (inactive x mx))).reachable)
  }
  let W := Classical.choice ((ismem _).mp bw)
  let YW := W.map (SimpleGraph.Hom.ofLE (H_le_G A q))
  let O : A.OutsideStrip q i j := {
    strip := T
    outside := outside
    link := YW
    link_in := by
      intro x hx
      have wh : x∈W.support := by simpa [YW,SimpleGraph.Walk.support_map] using hx
      exact (ismem x).mpr ((W.takeUntil x wh).reachable)
  }
  exact ⟨j,neq,oj,O,ismem,only⟩

/-- No decomposition oracle is needed for finite graphs. Pairing two contacts
through their outside exchange component gives the exact row class. -/
noncomputable def automatic : Decomposition A q := by
  classical
  by_cases h : ∃ i,A.openPort q i
  · let i := h.choose
    let P := linked_strip A q i h.choose_spec
    by_cases more : ∃ k,A.openPort q k ∧ k≠i ∧ k≠P.j
    · let k := more.choose
      have ko := more.choose_spec.1
      have ki := more.choose_spec.2.1
      have kj := more.choose_spec.2.2
      let Q := linked_strip A q k ko
      have apart : ∀ x∈P.strip.strip.region,x∉Q.strip.strip.region := by
        intro x xp xq
        have hk := ((P.exact_region x).mp xp).trans ((Q.exact_region x).mp xq).symm
        exact (P.only_contacts k ((P.exact_region _).mpr hk)).elim ki kj
      have lneI : Q.j≠i := by
        intro e
        have eq := congrArg (fun z=>p.mate (A.corner z)) e
        exact apart _ P.strip.strip.pa (Eq.subst (motive:=fun x : V=>x∈Q.strip.strip.region) eq Q.strip.strip.pb)
      have lneJ : Q.j≠P.j := by
        intro e
        have eq := congrArg (fun z=>p.mate (A.corner z)) e
        exact apart _ P.strip.strip.pb (Eq.subst (motive:=fun x : V=>x∈Q.strip.strip.region) eq Q.strip.strip.pb)
      have distinct : Square.FourDistinct i P.j k Q.j :=
        ⟨P.ne,Ne.symm ki,Ne.symm lneI,Ne.symm kj,Ne.symm lneJ,Q.ne⟩
      refine .four i P.j k Q.j distinct ?_ P.strip Q.strip apart
      intro t
      rcases Square.four_cover i P.j k Q.j distinct t with rfl|rfl|rfl|rfl
      · exact h.choose_spec
      · exact P.opened
      · exact ko
      · exact Q.opened
    · refine .two i P.j P.ne ?_ P.strip
      intro t
      constructor
      · intro yes
        by_cases e : t=i
        · exact Or.inl e
        by_cases f : t=P.j
        · exact Or.inr f
        exact (more ⟨t,yes,e,f⟩).elim
      · rintro (rfl|rfl)
        · exact h.choose_spec
        · exact P.opened
  · refine .none ?_
    exact fun i hi=>h ⟨i,hi⟩

#print axioms linked_strip
#print axioms automatic
end finite
end KelmansCactus.AtomicBridge.RemoteSquareStripAuto
