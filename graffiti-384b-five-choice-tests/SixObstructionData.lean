import ChoiceTight
import FiveData
namespace Graffiti384b.FiveChoice.Obstruction
open Finset SimpleGraph Four29 LowSample
abbrev V := Fin 29

/-- Row i of the symmetric adjacency matrix, with the least significant
bit representing vertex 0. Vertices 27 and 28 are the two ears. -/
private def rows : V → ℕ := ![134217778,134218701,268436418,268436162,5007393,87338001,39156622,132607566,64349766,28515790,99564448,29001456,51578432,79332848,86835664,102312224,130340800,8666752,131810800,90500112,25475936,4746912,70059472,102182784,35479456,92639680,47047840,3,12]
private def adj (i j : V) : Prop := (rows i).testBit j.val=true
instance : DecidableRel adj := fun i j => inferInstanceAs (Decidable ((rows i).testBit j.val=true))
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def graph : SimpleGraph V where
  Adj := adj
  symm := fun {i j} h => (show ∀a b:V,adj a b → adj b a by decide) i j h
  loopless := by exact (show ∀i:V,¬adj i i by decide)
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adj)

def localVertices : Finset V := roots graph 27 28 ∪ triangleContacts graph 27 28 ∪ {27,28}
def seed : Finset V := {2,3,5,6,9,10,11,13,16,17,23,24,25,27}

def scores : V → ℕ := ![2,13,9,6,11,24,43,65,47,49,63,34,16,32,23,17,53,18,59,28,29,19,25,40,41,27,37,1,0]

theorem score_table (v : V) : trianglesAt graph v=scores v := by
  rw [←Four29.FiveWitness.ordered_card graph]
  exact (show ∀i:V,(Four29.FiveWitness.ordered graph i).card=scores i by decide) v

theorem connected : graph.Connected := by
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨6,fun v => ?_⟩
  have walk : ∀w:V,w=6 ∨ graph.Adj 6 w ∨ ∃u:V,graph.Adj 6 u ∧ graph.Adj u w := by decide
  rcases walk v with rfl|edge|⟨u,e1,e2⟩
  · exact Reachable.refl _
  · exact edge.reachable
  · exact e1.reachable.trans e2.reachable

theorem diversity : (types graph).card=29 := by rw [types,funext score_table]; decide
theorem degrees : (nonleaves graph).card=29 ∧ (high graph).card=27 ∧ twos graph={27,28} ∧
    graph.neighborFinset 27={0,1} ∧ graph.neighborFinset 28={2,3} := by decide
theorem roots_eq : roots graph 27 28={0,1,2,3} := by rw [roots,degrees.2.2.2.1,degrees.2.2.2.2]; decide

def contacts : Finset V := {4,5,6,7,8,9}
theorem contacts_eq : triangleContacts graph 27 28=contacts := by unfold triangleContacts; rw [roots_eq]; decide
theorem exposures : (Donor.exposed graph (pool graph 27 28)).card=6 ∧ (twice graph (pool graph 27 28)).card≤6 := by decide

theorem fixed_partners :
    Repair.linkSupport graph 0\base graph 27 28={4,5} ∧
    Repair.linkSupport graph 1\base graph 27 28={6,7,8,9} := by decide

theorem feasible : gamma graph≤14 ∧ gamma graph≤bound graph := by
  have good : TwoDominates graph seed := by unfold TwoDominates; decide
  have le : gamma graph≤seed.card := Nat.sInf_le ⟨seed,good,rfl⟩
  have cnt : seed.card=14 := by decide
  rw [cnt] at le
  exact ⟨le,by rw [bound,diversity]; exact le⟩
end Graffiti384b.FiveChoice.Obstruction
#print axioms Graffiti384b.FiveChoice.Obstruction.connected
#print axioms Graffiti384b.FiveChoice.Obstruction.score_table
#print axioms Graffiti384b.FiveChoice.Obstruction.contacts_eq
#print axioms Graffiti384b.FiveChoice.Obstruction.fixed_partners
#print axioms Graffiti384b.FiveChoice.Obstruction.feasible
