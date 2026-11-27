import P5CliqueSmallCoreSignedSlack133
import P5CliqueSingleEdgeSingletonBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem single_edge_singleton_palette_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (edge12 : G.Adj (p 1) (p 2))
    (n10 : ¬G.Adj (p 1) (p 0)) (n20 : ¬G.Adj (p 2) (p 0))
    (n13 : ¬G.Adj (p 1) (p 3)) (n23 : ¬G.Adj (p 2) (p 3))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ x∈D,G.Adj q x↔x=p i)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  by_cases large : 10≤D.card
  · exact single_edge_singleton_palette_ambient_mean_four_large_core h4 h9 D p pm pi
      edge12 n10 n20 n13 n23 attach palette single Dconn h7 large
  let P := (Finset.univ : Finset (Fin 4)).image p
  have pc : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have sub : P⊆D := by
    intro x xm
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have d4 := Finset.card_le_card sub
  let J := G.induce (D : Set V)
  have j4 : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have ce : Fintype.card (D : Set V)=D.card := Fintype.card_coe D
  letI : DecidableRel J.Adj := Classical.decRel _
  have slack := small_core_ten_signed_slack (G:=J) (by omega) (by omega) j4
  rw [ce] at slack
  exact single_edge_singleton_palette_ambient_mean_four_of_slack h4 h9 D p pm pi
    edge12 n10 n20 n13 n23 attach palette single slack

#print axioms single_edge_singleton_palette_ambient_mean_four
end Graffiti133P5CliqueArms
