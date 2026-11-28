import AdjacentCutFiveTwinBothFour189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint shore_hit_a shore_nonempty from AdjacentCutFiveActual189
open private positive_cap foreign_pos_even from AdjacentCutFiveComponents189
open private mem_positive d2 from AdjacentCutFiveBound189
open private complete_from_no_local_even from AdjacentCutFiveTwoTwinGeometry189
open private twin_partition twin_even_budget from AdjacentCutFiveTwinBothFour189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

theorem order_le_sixteen_of_adjacent_four_common_shore
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (four : (Shore C).card=4) (common : ∀ z∈Shore C,G.Adj a z ∧ G.Adj b z) :
    Fintype.card V≤16 := by
  classical
  obtain ⟨p,pc⟩ := shore_nonempty C
  have sub : (univ.erase a |>.erase b : Finset V)⊆Shore C ∪ Shore D := by
    intro z zc
    exact mem_union.mpr (cover (mem_erase.mp (mem_erase.mp zc).2).1 (mem_erase.mp zc).1)
  have n := card_le_card sub
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),
    card_univ,card_union_of_disjoint (shore_disjoint cd)] at n
  have work {s t : V} (st : G.Adj s t)
      (scommon : ∀ z∈Shore C,G.Adj s z)
      (cross : ∀ {x z}, x∈Shore D → z∈Shore C → G.Adj s x → G.Adj s z →
        z∈PositiveEven G x)
      (crossRev : ∀ {x z}, x∈Shore C → z∈Shore D → G.Adj s x → G.Adj s z →
        z∈PositiveEven G x)
      (toffC : t∉Shore C) (toffD : t∉Shore D)
      (soffD : s∉Shore D)
      {x : V} (xd : x∈Shore D) (sx : G.Adj s x) (tx : ¬G.Adj t x) :
      (Shore D).card≤10 := by
    have xt : x≠t := fun e=>toffD (e ▸ xd)
    have hit := (mem_filter.mp (d2 hc xt.symm tx st.symm sx)).2
    have tPos : t∈PositiveEven G x := mem_positive.mpr ⟨xt.symm,by rw [dist_comm,hit]; decide⟩
    have csub : Shore C ⊆ PositiveEven G x :=
      fun z zc=>cross xd zc sx (scommon z zc)
    have unr : ∀ z∈Shore D,z=x ∨ G.Adj x z := by
      apply complete_from_no_local_even hc xd
      intro z zd zPos
      have nz : z∉Shore C := fun h=>disjoint_left.mp (shore_disjoint cd) h zd
      have zt : z≠t := fun e=>toffD (e ▸ zd)
      have off : z∉insert t (Shore C) := by simp [zt,nz]
      have subset : insert z (insert t (Shore C)) ⊆ PositiveEven G x := by
        intro w wm
        rcases mem_insert.mp wm with rfl|wm
        · exact zPos
        rcases mem_insert.mp wm with rfl|wm
        · exact tPos
        · exact csub wm
      have ct := card_le_card subset
      rw [card_insert_of_not_mem off,card_insert_of_not_mem toffC,four] at ct
      have mx := positive_cap x even
      omega
    let A := (Shore D).filter (G.Adj s)
    have Ac : A.card≤5 := by
      have asub : A⊆PositiveEven G p := by
        intro w wa
        obtain ⟨wd,sw⟩ := mem_filter.mp wa
        exact crossRev pc wd (scommon p pc) sw
      exact (card_le_card asub).trans (positive_cap p even)
    have Dsub : Shore D⊆A∪PositiveEven G s := by
      intro w wd
      by_cases sw : G.Adj s w
      · exact mem_union_left _ (mem_filter.mpr ⟨wd,sw⟩)
      have wx : G.Adj x w := (unr w wd).resolve_left (fun e=>sw (e.symm ▸ sx))
      have ws : w≠s := fun e=>soffD (e ▸ wd)
      have sec := (mem_filter.mp (d2 hc ws.symm sw sx wx)).2
      exact mem_union_right _ (mem_positive.mpr ⟨ws,by rw [sec]; decide⟩)
    have h := (card_le_card Dsub).trans (card_union_le A (PositiveEven G s))
    have k := positive_cap s even
    omega
  by_cases diff : ∃ x∈Shore D, (G.Adj a x ∧ ¬G.Adj b x) ∨ (G.Adj b x ∧ ¬G.Adj a x)
  · obtain ⟨x,xd,xab|xba⟩ := diff
    · have h := work ab (fun z zc=>(common z zc).1)
        (fun xc zc ax az=>foreign_pos_even hc cd.symm xc zc ax az)
        (fun xc zc ax az=>foreign_pos_even hc cd xc zc ax az)
        (shore_off C).2 (shore_off D).2 (shore_off D).1 xd xab.1 xab.2
      omega
    · have h := work ab.symm (fun z zc=>(common z zc).2)
        (fun xc zc bx bz=>foreign_pos_even hc cd.symm xc zc bx bz)
        (fun xc zc bx bz=>foreign_pos_even hc cd xc zc bx bz)
        (shore_off C).1 (shore_off D).1 (shore_off D).2 xd xba.1 xba.2
      omega
  have twin (z : V) (za : z≠a) (zb : z≠b) : G.Adj a z ↔ G.Adj b z := by
    rcases cover za zb with zc|zd
    · exact iff_of_true (common z zc).1 (common z zc).2
    constructor
    · intro az
      by_contra bz
      exact diff ⟨z,zd,.inl ⟨az,bz⟩⟩
    · intro bz
      by_contra az
      exact diff ⟨z,zd,.inr ⟨bz,az⟩⟩
  have oc := (card_le_card (adj_twin_odd_foreign hc twin cd pc (common p pc).1)).trans (positive_cap p even)
  have ce := twin_even_budget even cd
  have dp : (AdjTwinOdd D).card+(AdjTwinEven D).card=(Shore D).card := twin_partition
  omega

#print axioms order_le_sixteen_of_adjacent_four_common_shore
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
