import SixThree19Thirteen189

namespace Graffiti189LongestPath.SixThreeNineteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def Omitted {a b : V} (p : G.Walk a b) : Finset V := univ \ p.support.toFinset

private theorem mem_omitted {a b : V} {p : G.Walk a b} {x : V} :
    x∈Omitted p ↔ x∉p.support := by simp [Omitted]

theorem high_pin_shape_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (len : 14≤p.length) {x : V} (hx : x∉p.support) (dx : 6≤G.degree x) :
    p.length=14 ∧ (Omitted p).card=4 ∧ (Pins p x).card=3 ∧
      ∀ y,y∉p.support → x≠y → G.Adj x y := by
  classical
  let O := Omitted p
  have sum := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
  change O.card+p.support.toFinset.card=Fintype.card V at sum
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at sum
  have xo : x∈O := mem_omitted.mpr hx
  have few : (Pins p x).card≤3 := by
    by_cases h : (Pins p x).Nonempty
    · obtain ⟨i,hi⟩ := h
      have b := PinRun.high_omitted_pin_budget hc 6 3 cap conn hp hx
        (Graffiti189LongestPath.pin_data hi).2 dx
      omega
    rw [not_nonempty_iff_eq_empty.mp h,card_empty]
    decide
  let C := (O.erase x).filter (G.Adj x)
  have sub : G.neighborFinset x ⊆ PinVertices p x∪C := by
    intro y ym
    have adj := (mem_neighborFinset _ _ _).mp ym
    by_cases on : y∈p.support
    · obtain ⟨i,hi,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx on adj
      exact mem_union_left _ (mem_image.mpr ⟨i,hi,he⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨mem_erase.mpr ⟨adj.ne.symm,mem_omitted.mpr on⟩,adj⟩)
  have ca := card_le_card sub
  have cb := card_union_le (PinVertices p x) C
  rw [card_neighborFinset_eq_degree] at ca
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices (x:=x) hp] at cb
  have cc : C.card≤O.card-1 := by
    rw [←card_erase_of_mem xo]
    exact card_le_card (filter_subset _ _)
  have e : C=O.erase x := by
    apply eq_of_subset_of_card_le (show C ⊆ O.erase x from filter_subset _ _)
    rw [card_erase_of_mem xo]
    omega
  change p.length=14 ∧ O.card=4 ∧ (Pins p x).card=3 ∧ _
  refine ⟨by omega,by omega,by omega,?_⟩
  intro y hy xy
  have m : y∈C := e.symm ▸ mem_erase.mpr ⟨xy.symm,mem_omitted.mpr hy⟩
  exact (mem_filter.mp m).2

theorem other_high_omitted (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} {x : V} (hx : x∉p.support) (four : (Omitted p).card=4) :
    ∃ y,y∉p.support ∧ x≠y ∧ 6≤G.degree y := by
  classical
  by_contra no
  have c : ((Omitted p).erase x).card=3 := by
    rw [card_erase_of_mem (mem_omitted.mpr hx),four]
  have h : ((Omitted p).erase x).card≤1 := card_le_one.mpr (fun y ym z zm=>by
    by_contra ne
    obtain ⟨yx,yo⟩ := mem_erase.mp ym
    obtain ⟨zx,zo⟩ := mem_erase.mp zm
    have ly : ¬6≤G.degree y := fun h=>no ⟨y,mem_omitted.mp yo,yx.symm,h⟩
    have lz : ¬6≤G.degree z := fun h=>no ⟨z,mem_omitted.mp zo,zx.symm,h⟩
    exact (degree y z ne).elim ly lz)
  omega

#print axioms high_pin_shape_long
end Graffiti189LongestPath.SixThreeNineteen
