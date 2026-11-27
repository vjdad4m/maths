import ActualTwoCut189
namespace Graffiti189LongestPath.TwoCut.CutPair
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {a b : V} (S : CutPair G a b)

private theorem no_ab (atleast : 3≤G.dist a b) : ¬G.Adj a b := fun e => by
  have eq := dist_eq_one_iff_adj.mpr e
  omega

private theorem not_common (atleast : 3≤G.dist a b) {x : V}
    (ax : G.Adj a x) (bx : G.Adj b x) : False := by
  have d := G.dist_le (Walk.cons ax (Walk.cons bx.symm Walk.nil))
  simp at d
  omega

theorem extra_d2 (atleast : 3≤G.dist a b) {i : Bool} {x : V}
    (xi : x∈S.H i) (ax : G.Adj a x) :
    ∃ y, y∈DistanceTwo G x ∧ (y=b ∨ y∈S.H i) := by
  by_cases via : ∃ z∈S.H i, G.Adj x z ∧ G.Adj b z
  · obtain ⟨z,_,xz,bz⟩ := via
    have xb : x≠b := fun e => (S.off i).2 (e ▸ xi)
    have nxb : ¬G.Adj x b := fun e => not_common atleast ax e.symm
    exact ⟨b,Sides.mem_d2.mpr (Sides.dist_two S.con xb nxb xz bz.symm),Or.inl rfl⟩
  obtain ⟨z,zi,bz⟩ := S.hitb i
  have no : ¬(x=z ∨ G.Adj x z) := by
    rintro (rfl|xz)
    · exact not_common atleast ax bz
    · exact via ⟨z,zi,xz,bz⟩
  by_cases ex : ∃ y∈S.H i,y∈DistanceTwo G x
  · obtain ⟨y,yi,yd⟩ := ex
    exact ⟨y,yd,Or.inr yi⟩
  exfalso
  obtain ⟨q,qs⟩ := S.joined i x xi z zi
  have prop {u v : V} (w : G.Walk u v) (ws : ∀ y∈w.support,y∈S.H i)
      (xu : x=u ∨ G.Adj x u) : x=v ∨ G.Adj x v := by
    induction w with
    | nil => exact xu
    | @cons u y v uy w ih =>
      apply ih (fun y hy => ws y (by simp [hy]))
      rcases xu with eq|xu
      · exact Or.inr (eq.symm ▸ uy)
      by_cases xy : x=y
      · exact Or.inl xy
      by_cases ad : G.Adj x y
      · exact Or.inr ad
      exact (ex ⟨y,ws y (by simp),Sides.mem_d2.mpr (Sides.dist_two S.con xy ad xu uy)⟩).elim
  exact no (prop q qs (Or.inl rfl))

theorem at_most_three_a_ports (atleast : 3≤G.dist a b) (i : Bool) :
    (S.A i).card≤3 := by
  obtain ⟨x,xi,ax⟩ := S.hita (!i)
  have ne : (!i)≠i := by cases i <;> decide
  have dis := S.disjoint_sides ne
  obtain ⟨z,z2,own⟩ := S.extra_d2 atleast xi ax
  have zno : z∉S.A i := by
    intro zp
    have zh := (mem_filter.mp zp).1
    rcases own with rfl|own
    · exact (S.off i).2 zh
    · exact disjoint_left.mp dis own zh
  have sub : insert z (S.A i) ⊆ DistanceTwo G x := by
    intro t ht
    rcases mem_insert.mp ht with rfl|th
    · exact z2
    obtain ⟨ti,at'⟩ := mem_filter.mp th
    have tout : t∉S.H (!i) := fun h => disjoint_left.mp dis h ti
    have xt : x≠t := fun e => tout (e ▸ xi)
    have no : ¬G.Adj x t := fun e => (S.closed (!i) x xi t e).elim
      (fun e => (S.off i).1 (e ▸ ti)) (fun h => h.elim (fun e => (S.off i).2 (e ▸ ti)) tout)
    exact Sides.mem_d2.mpr (Sides.dist_two S.con xt no ax.symm at')
  have s := card_le_card sub
  rw [card_insert_of_not_mem zno] at s
  have d := distanceTwo_le_of_even 4 x (S.even x)
  omega

private theorem degree_within_side_bound (atleast : 3≤G.dist a b) {i : Bool} {x : V} (xi : x∈S.H i) :
    G.degree x≤(S.H i).card := by
  classical
  let R := ({a,b} : Finset V).filter (G.Adj x)
  have rone : R.card≤1 := by
    apply card_le_one.mpr
    intro u ur v vr
    obtain ⟨uq,xu⟩ := mem_filter.mp ur
    obtain ⟨vq,xv⟩ := mem_filter.mp vr
    simp only [mem_insert,mem_singleton] at uq vq
    rcases uq with rfl|rfl <;> rcases vq with rfl|rfl
    · rfl
    · exact (not_common atleast xu.symm xv.symm).elim
    · exact (not_common atleast xv.symm xu.symm).elim
    · rfl
  have sub : G.neighborFinset x ⊆ R ∪ (S.H i).erase x := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xi y xy with rfl|rfl|yh
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xy⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xy⟩))
    · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨xy.ne.symm,yh⟩))
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have q := card_union_le R ((S.H i).erase x)
  rw [card_erase_of_mem xi] at q
  have pos := card_pos.mpr (show (S.H i).Nonempty from ⟨x,xi⟩)
  omega

theorem sides_ge_four (atleast : 3≤G.dist a b) (i : Bool) : 4≤(S.H i).card := by
  obtain ⟨x,xi,ax⟩ := S.hita i
  obtain ⟨y,yi,by'⟩ := S.hitb i
  have ne : x≠y := fun e => not_common atleast ax (e.symm ▸ by')
  have dx := S.degree_within_side_bound atleast xi
  have dy := S.degree_within_side_bound atleast yi
  exact (S.degree x y ne).elim (by omega) (by omega)

private theorem high_universal_in_four (atleast : 3≤G.dist a b) {i : Bool}
    (small : (S.H i).card=4) {x y : V} (xi : x∈S.H i) (yi : y∈S.H i)
    (xy : x≠y) (high : 4≤G.degree x) : G.Adj x y := by
  by_cases yes : G.Adj x y
  · exact yes
  exfalso
  let R := ({a,b} : Finset V).filter (G.Adj x)
  have rone : R.card≤1 := by
    apply card_le_one.mpr
    intro u ur v vr
    obtain ⟨uq,xu⟩ := mem_filter.mp ur
    obtain ⟨vq,xv⟩ := mem_filter.mp vr
    simp only [mem_insert,mem_singleton] at uq vq
    rcases uq with rfl|rfl <;> rcases vq with rfl|rfl
    · rfl
    · exact (not_common atleast xu.symm xv.symm).elim
    · exact (not_common atleast xv.symm xu.symm).elim
    · rfl
  have sub : G.neighborFinset x ⊆ R ∪ ((S.H i).erase x).erase y := by
    intro z hz
    have xz := (mem_neighborFinset G x z).mp hz
    rcases S.closed i x xi z xz with rfl|rfl|yh
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xz⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xz⟩))
    · have yz : z≠y := fun eq => yes (eq ▸ xz)
      exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨yz,mem_erase.mpr ⟨xz.ne.symm,yh⟩⟩))
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have q := card_union_le R (((S.H i).erase x).erase y)
  rw [card_erase_of_mem (mem_erase.mpr ⟨xy.symm,yi⟩),card_erase_of_mem xi] at q
  omega

theorem side_four_clique (atleast : 3≤G.dist a b) {i : Bool}
    (small : (S.H i).card=4) {x y : V} (xi : x∈S.H i) (yi : y∈S.H i)
    (xy : x≠y) : G.Adj x y :=
  (S.degree x y xy).elim (S.high_universal_in_four atleast small xi yi xy)
    (fun e => (S.high_universal_in_four atleast small yi xi xy.symm e).symm)

#print axioms at_most_three_a_ports
#print axioms sides_ge_four
#print axioms side_four_clique
end Graffiti189LongestPath.TwoCut.CutPair
