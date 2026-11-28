import ChoiceTight
import ForkPatch
import PrivateLower
import FiveData
namespace Graffiti384b.Exterior.Positive
open Finset SimpleGraph Four29 LowSample FiveChoice
abbrev V := Fin 30

/-- Row i of the symmetric adjacency matrix, with the least significant
bit representing vertex 0. Vertices 27 and 28 are the two ears. -/
private def rows : V → ℕ := ![134217778,134218701,268436362,268436166,7201,122897,536871818,75498062,25166406,117440974,8132624,7214096,8260624,8208416,7053344,606240,8052768,125392896,66599936,83360768,124728320,132086784,79657984,124518784,79037184,79036928,66716288,3,12,64]
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
def seed : Finset V := {4,6,9,16,19,21,27,28,29}

def scores : V → ℕ := ![2,13,9,10,4,6,8,11,7,16,22,21,27,20,19,5,24,32,33,49,40,57,47,17,14,12,25,1,1,0]

theorem score_table (v : V) : trianglesAt graph v=scores v := by
  rw [←Four29.FiveWitness.ordered_card graph]
  exact (show ∀i:V,(Four29.FiveWitness.ordered graph i).card=scores i by decide) v

private def parent : V → V := ![0,0,1,1,0,0,1,1,1,1,4,4,4,5,5,5,5,11,10,10,10,10,10,7,8,9,7,0,2,6]

theorem connected : graph.Connected := by
  have tree : ∀i:V,i=parent i ∨ graph.Adj i (parent i) := by decide
  have root : ∀i:V,parent (parent (parent i))=0 := by decide
  have step (v : V) : graph.Reachable v (parent v) :=
    (tree v).elim (fun eq => eq ▸ Reachable.refl _) (fun edge => edge.reachable)
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0,fun v => ?_⟩
  have path := (step v).trans ((step (parent v)).trans (step (parent (parent v))))
  rw [root v] at path
  exact path.symm

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

theorem feasible : gamma graph≤9 ∧ gamma graph≤bound graph := by
  have good : TwoDominates graph seed := by unfold TwoDominates; decide
  have le : gamma graph≤seed.card := Nat.sInf_le ⟨seed,good,rfl⟩
  have cnt : seed.card=9 := by decide
  rw [cnt] at le
  exact ⟨le,by rw [bound,diversity]; change _≤15; omega⟩
theorem three_pins_exist :
    Protected graph ({0,1,28,10,13}:Finset V) {27,2,3,4,5,18} ∧
    ((({0,1,28,10,13}:Finset V) ∪ {27,2,3,4,5,18}) \ localVertices).card=3 := by
  rw [localVertices,roots_eq,contacts_eq]
  unfold Protected
  decide

theorem positive_core : ∀v∈nonleaves graph,0<trianglesAt graph v := by
  intro v vm; rw [score_table]; exact (show ∀i∈nonleaves graph,0<scores i by decide) v vm

/-- All original high-degree and distance-free data, with a single pendant
vertex providing the only zero triangle score in the full graph. -/
theorem exact_profile : graph.Connected ∧ (types graph).card=29 ∧ (nonleaves graph).card=29 ∧
    (high graph).card=27 ∧ (triangleContacts graph 27 28).card=6 ∧
    (Donor.exposed graph (pool graph 27 28)).card=6 ∧
    graph.degree 29=1 ∧ (∀v∈nonleaves graph,0<trianglesAt graph v) ∧ gamma graph≤9 := by
  refine ⟨connected,diversity,degrees.1,degrees.2.1,?_,exposures.1,by decide,positive_core,feasible.1⟩
  rw [contacts_eq]; decide

private theorem thin : ThinTriangle graph localVertices 27 0 1 4 5 := by
  rw [localVertices,roots_eq,contacts_eq]
  constructor <;> decide

theorem minimum_outside : IsLeast {n : ℕ | ∃P Q:Finset V,((P∪Q)\localVertices).card=n ∧
    Protected graph P Q ∧ twos graph⊆P∪Q} 3 := by
  constructor
  · refine ⟨{0,1,28,10,13},{27,2,3,4,5,18},three_pins_exist.2,three_pins_exist.1,?_⟩
    rw [degrees.2.2.1]; decide
  · rintro n ⟨L,R,count,cut,ears⟩
    rw [←count]; exact at_least_three graph thin cut (ears (degrees.2.2.1 ▸ mem_insert_self (27:V) {28}))

private def points : Fin 6 ↪ V := ⟨![0,1,2,3,27,28],by decide⟩
theorem fork_solution : gamma graph≤bound graph := by
  apply fork_patch graph diversity degrees.1 degrees.2.1 points (x:=4) (y:=5)
  · decide
  · decide
  · decide
  · decide
  all_goals first | rw [show points 4=(27:V) from rfl,show points 5=(28:V) from rfl,roots_eq]; decide
                  | rw [show points 4=(27:V) from rfl,show points 5=(28:V) from rfl,contacts_eq]; decide
                  | decide

theorem six_required (X : Finset V) (ok : supports graph 27 28 X) : 6≤X.card := by
  obtain ⟨i,ir,big,comp⟩ := compulsory graph 27 28 X ok
  have only : ∀j∈({0,1,2,3}:Finset V),13≤scores j → j=1 := by decide
  have eq : i=1 := only i (roots_eq ▸ ir) (score_table _ ▸ big)
  subst i
  have ar (j : V) (jm : j∈({0,1,2,3}:Finset V)) : j∈roots graph 27 28 := roots_eq ▸ jm
  have first := comp 0 (ar 0 (by decide)) (by rw [score_table]; decide)
  have second := comp 1 (ar 1 (by decide)) (by rw [score_table]; decide)
  rw [fixed_partners.1] at first
  rw [fixed_partners.2] at second
  exact (by decide : 6≤(({4,5}:Finset V)∪{6,7,8,9}).card).trans (card_le_card (union_subset first second))
end Graffiti384b.Exterior.Positive
#print axioms Graffiti384b.Exterior.Positive.exact_profile
#print axioms Graffiti384b.Exterior.Positive.minimum_outside
#print axioms Graffiti384b.Exterior.Positive.fork_solution
#print axioms Graffiti384b.Exterior.Positive.six_required
