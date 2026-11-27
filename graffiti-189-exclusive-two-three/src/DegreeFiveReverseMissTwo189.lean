import DegreeFiveReverseSupport189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem high_b_cannot_miss_two_shell
    (hc : G.Connected) {D : Cmp (G:=G) (a:=a) (b:=b)} {r s t : V}
    (pB : (portColor D b).card=3) (fB : (secondShore D b).card≤3)
    (rb : r∈portColor D b) (no : ¬G.Adj a r) (high : 5≤G.degree r)
    (sf : s∈secondShore D b) (tf : t∈secondShore D b) (st : s≠t)
    (rs : ¬G.Adj r s) (rt : ¬G.Adj r t) : False := by
  classical
  let B := portColor D b
  let F := secondShore D b
  obtain ⟨rd,br⟩ := mem_filter.mp rb
  have sub : G.neighborFinset r ⊆ insert b (B.erase r ∪ ((F.erase s).erase t)) := by
    intro w wn
    have rw' := (mem_neighborFinset G _ _).mp wn
    rcases shore_closed D r rd w rw' with rfl|rfl|wd
    · exact (no rw'.symm).elim
    · exact mem_insert_self _ _
    apply mem_insert_of_mem
    by_cases bw : G.Adj b w
    · exact mem_union_left _ (mem_erase.mpr ⟨rw'.ne.symm,mem_filter.mpr ⟨wd,bw⟩⟩)
    have bs : b≠w := fun e=>(shore_off D).2 (e.symm ▸ wd)
    have nf : w∈F := mem_inter.mpr ⟨wd,d2 hc bs bw br rw'⟩
    have ns : w≠s := fun e=>rs (e ▸ rw')
    have nt : w≠t := fun e=>rt (e ▸ rw')
    exact mem_union_right _ (mem_erase.mpr ⟨nt,mem_erase.mpr ⟨ns,nf⟩⟩)
  have k := (card_le_card sub).trans (card_insert_le _ _)
  have q := card_union_le (B.erase r) ((F.erase s).erase t)
  have bcnt : (B.erase r).card=2 := by
    rw [card_erase_of_mem (show r∈B from rb)]
    change (portColor D b).card-1=2
    omega
  have fcnt : ((F.erase s).erase t).card≤1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨st.symm,show t∈F from tf⟩),
      card_erase_of_mem (show s∈F from sf)]
    change (secondShore D b).card-1-1≤1
    omega
  rw [card_neighborFinset_eq_degree] at k
  omega

#print axioms high_b_cannot_miss_two_shell
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
