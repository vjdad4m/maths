import CubicLeaves
namespace Graffiti384b.OddStars.OriginalPins
open SimpleGraph Finset ReservedWheel WheelCut WheelCubic
open private Repair.isolate from Repair384b
open private CliquePivot33.isolated_degree from ShoreCliquePivot
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Original edges may support every pin and the pivot. An unavoidable
cubic has degree three in both the original graph and its triangle skeleton. -/
theorem actual_blocker (bad : bound G<gamma G) {P Q W : Finset V} (pins : Frame G P Q)
    {x : V} (off : x∉P∪Q) (l : 2≤nbr G x P) (r : 2≤nbr G x Q)
    (quota : (types G).card≤W.card+1) (free : ∀w∈W,w∉P∪Q → w∈high (patch G ∅)) :
    ∃w∈W,w∉P∪Q ∧ G.degree w=3 ∧ (patch G ∅).degree w=3 ∧
      G.neighborFinset w=(patch G ∅).neighborFinset w ∧ (patch G ∅).Adj w x := by
  classical
  let J := patch G ∅
  have push {w : V} : J.neighborFinset w⊆G.neighborFinset w := fun _ wm =>
    (G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp wm).1
  by_contra! no
  have v := weighted_pivot G W pins.dis (fun m => off (mem_union_left _ m)) (fun m => off (mem_union_right _ m))
    l r pins.left pins.right (by
      intro w wm wx wp wq
      have skip : w∉P∪Q := fun h => (mem_union.mp h).elim wp wq
      have hj : 3≤J.degree w := (mem_filter.mp (free w wm skip)).2
      have hg := card_le_card (push (w:=w))
      rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at hg
      rw [CliquePivot33.isolated_degree G wx]
      by_cases ed : G.Adj w x
      · rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr ed),card_neighborFinset_eq_degree]
        have neq : G.degree w≠3 := by
          intro d
          have dj : J.degree w=3 := by omega
          have eqN := eq_of_subset_of_card_le (push (w:=w)) (by rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,d,dj])
          have xm := (G.mem_neighborFinset ..).mpr ed
          rw [← eqN] at xm
          exact no w wm skip d dj eqN.symm ((J.mem_neighborFinset ..).mp xm)
        omega
      · rw [erase_eq_of_not_mem (fun h => ed ((G.mem_neighborFinset ..).mp h)),card_neighborFinset_eq_degree]
        omega)
  unfold bound at bad
  omega

def Usable (x : V) : Prop := ∃P Q : Finset V,Frame G P Q ∧ x∉P∪Q ∧ 2≤nbr G x P ∧ 2≤nbr G x Q

omit [Fintype V] in
theorem usable_of_rim {x a b c d : V} (r : Rim G x a b c d) : Usable G x := by
  refine ⟨{a,b},{c,d},square_frame G r.ab r.cd r.ac r.ad r.bc r.bd,?_,?_,?_⟩
  · simp only [mem_union,mem_insert,mem_singleton,not_or]
    exact ⟨⟨r.xa.ne,r.xb.ne⟩,r.xc.ne,r.xd.ne⟩
  · exact PinnedColor34.two G r.ab r.xa r.xb (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  · exact PinnedColor34.two G r.cd r.xc r.xd (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))

private theorem upper_hit (bad : bound G<gamma G) (one : 1∉types G) {x : V} (ok : Usable G x) :
    ∃w,G.degree w=3 ∧ (patch G ∅).degree w=3 ∧ (patch G ∅).Adj w x := by
  obtain ⟨P,Q,f,off,l,r⟩ := ok
  have size := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  obtain ⟨w,_,_,dw,dj,_,e⟩ := actual_blocker G bad f off l r size.ge (fun _ wm _ => wm)
  exact ⟨w,dw,dj,e⟩

/-- Four original-graph pivots suffice whenever an extra edge raises
one skeletal cubic above original degree three. -/
theorem exact_four_with_extra (conn : G.Connected) (order : 2<Fintype.card V) (one : 1∉types G)
    {v : V} (dv : (patch G ∅).degree v=3) (extra : 4≤G.degree v)
    (C : Finset V) (usable : ∀x∈C,Usable G x) (four : 4≤C.card) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  let J := patch G ∅
  obtain ⟨_,u,z,_,_,_,_,char,_⟩ := PaletteCorollaries.missing_one_failure G conn order bad one
  have other {p q : V} (cls : ∀w,J.degree w=3 → w=p ∨ w=q) (vp : v=p) (dq : J.degree q=3) : False := by
    have inc : C⊆J.neighborFinset q := by
      intro x xm
      obtain ⟨w,dw,dj,e⟩ := upper_hit G bad one (usable _ xm)
      have ne : w≠p := fun eq => by rw [vp,← eq] at extra; omega
      exact (J.mem_neighborFinset ..).mpr (((cls _ dj).resolve_left ne) ▸ e)
    have cnt := card_le_card inc
    rw [card_neighborFinset_eq_degree,dq] at cnt
    omega
  rcases (char _).mp dv with vu|vz
  · exact other (fun w d => (char w).mp d) vu ((char _).mpr (Or.inr rfl))
  · exact other (fun w d => ((char w).mp d).symm) vz ((char _).mpr (Or.inl rfl))

end Graffiti384b.OddStars.OriginalPins
#print axioms Graffiti384b.OddStars.OriginalPins.actual_blocker
#print axioms Graffiti384b.OddStars.OriginalPins.usable_of_rim
#print axioms Graffiti384b.OddStars.OriginalPins.exact_four_with_extra
