import DegreeFiveCommonTwoCut189
import DegreeFiveOneExclusiveShore189
import DegreeFiveDistanceTwoThreeClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- All degree-five distance-two two-vertex cuts leaving exactly two components. -/
theorem traceable_of_actual_five_distance_two_two_components
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2) :
    ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases ex : ∃ D : Cmp (G:=G) (a:=a) (b:=b),
      ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z)
  · exact traceable_of_actual_five_distance_two_with_exclusive_shore hc two even conn comp degree ex
  have both (D : Cmp (G:=G) (a:=a) (b:=b)) :
      ∃ z∈Shore D,G.Adj a z ∧ G.Adj b z := by
    apply Classical.byContradiction
    intro no
    exact ex ⟨D,fun z zd h=>no ⟨z,zd,h⟩⟩
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  let U := (univ : Finset J.ConnectedComponent)
  have twoComp : U.card=2 := by
    change Nat.card J.ConnectedComponent=2 at comp
    rw [Nat.card_eq_fintype_card] at comp
    simpa [U] using comp
  obtain ⟨C,D,cd,eq⟩ := card_eq_two.mp twoComp
  have cover (z : V) : z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D := by
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    let Z := J.connectedComponentMk ⟨z,za,zb⟩
    have zu : Z∈U := mem_univ _
    rw [eq] at zu
    have zz : Z=C ∨ Z=D := by simpa using zu
    exact .inr (.inr (zz.imp (fun zc=>mem_shore.mpr ⟨⟨za,zb⟩,zc⟩)
      (fun zd=>mem_shore.mpr ⟨⟨za,zb⟩,zd⟩)))
  obtain ⟨x,xc,ax,bx⟩ := both C
  obtain ⟨y,yd,ay,by'⟩ := both D
  exact traceable_of_actual_five_distance_two_both_common_shores hc two even conn degree cd cover xc ax bx yd ay by'

/-- Any distance-two separating pair is enough for traceability in the degree-five case. -/
theorem traceable_of_actual_five_distance_two_cut
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support := by
  by_cases twoS : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2
  · exact traceable_of_actual_five_distance_two_two_components hc two even conn degree twoS
  exact traceable_of_three_shores_at_five_distance_two hc two even conn degree (by omega)

#print axioms traceable_of_actual_five_distance_two_two_components
#print axioms traceable_of_actual_five_distance_two_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
