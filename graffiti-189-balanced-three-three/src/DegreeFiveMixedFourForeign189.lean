import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget foreign_exclusive_subset_at_port universal_if_no_own_second
  from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem exclusive_shore_le_seven_of_mixed_with_four_foreign
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {u v c d : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u)
    (_vD : v∈Shore D) (dv : G.Adj d v) (uv : G.Adj u v)
    (three : (portColor D c).card≤3) (four : (portColor C c).card=4) :
    (Shore D).card≤7 := by
  classical
  let F := portColor C c
  let Q := secondShore D u
  have dOff : d∉Shore C ∧ d∉Shore D := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have bg : d∈DistanceTwo G u :=
    d2 hc (fun e=>dOff.2 (e ▸ uD)) (fun e=>du e.symm) uv dv.symm
  have f := foreign_exclusive_subset_at_port hc cd ct uD cu
  change F⊆DistanceTwo G u at f
  have offs : d∉Q∪F := fun h=>(mem_union.mp h).elim (fun h=>dOff.2 (mem_inter.mp h).1)
    (fun h=>dOff.1 (mem_filter.mp h).1)
  have dis : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have sub : insert d (Q∪F)⊆DistanceTwo G u := by
    intro z h
    rcases mem_insert.mp h with rfl|h
    · exact bg
    exact (mem_union.mp h).elim (fun q=>(mem_inter.mp q).2) (fun q=>f q)
  have k := card_le_card sub
  rw [card_insert_of_not_mem offs,card_union_of_disjoint dis] at k
  have cap := distanceTwo_le_of_even 5 u (even u)
  change F.card=4 at four
  have zero : Q.card=0 := by omega
  have all := universal_if_no_own_second hc uD zero
  have cOff : c∉Shore D := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact (shore_off D).1
    exact (shore_off D).2
  have cover : Shore D⊆portColor D c∪secondShore D c := by
    intro z zD
    by_cases cz : G.Adj c z
    · exact mem_union_left _ (mem_filter.mpr ⟨zD,cz⟩)
    have h := (all z zD).resolve_left (fun e=>cz (e.symm ▸ cu))
    exact mem_union_right _ (mem_inter.mpr ⟨zD,d2 hc (fun e=>cOff (e.symm ▸ zD)) cz cu h⟩)
  have cnt := (card_le_card cover).trans (card_union_le _ _)
  have budget := two_shore_budget cd dOff dist even
  omega

#print axioms exclusive_shore_le_seven_of_mixed_with_four_foreign
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
