import CentralLeafObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.CentralLeafObstruction
open Substitute
abbrev P := Fin 10

def core : Finset P := univ \ {0,2,8}

def mate (i : P) : P := if i=3 then 4 else if i=5 then 7 else 1

def third (i j : P) : P :=
  if i≠3 ∧ j≠3 then 3 else if i≠5 ∧ j≠5 then 5 else 6

private def kit (i j : P) : Prop :=
  let w := third i j
  ({i,mate i}:Finset P)⊆core ∧ ({j,mate j}:Finset P)⊆core ∧
  Disjoint ({i,mate i}:Finset P) {j,mate j} ∧
  pet.Adj i (mate i) ∧ pet.Adj j (mate j) ∧
  (pet.Adj 9 w ∨ pet.Adj 9 (mate w)) ∧ pet.Adj w (mate w) ∧
  (9:P)≠w ∧ (9:P)≠mate w ∧
  core \ ({i,mate i} ∪ {j,mate j}) = {9,w,mate w}

private instance (i j : P) : Decidable (kit i j) := by
  unfold kit
  infer_instance

private theorem kits :
    ∀ i j : P, pet.Adj 8 i → pet.Adj 8 j → i≠j → kit i j := by decide

/-- Two adjacent core vertices may be allocated to each of any two
distinct ports of the third atom. This always leaves one valid core
tile, even though every one-core-vertex template fails. -/
theorem pet_repairs_with_center_port {i j : P}
    (ei : pet.Adj 8 i) (ej : pet.Adj 8 j) (ij : i≠j) :
    ({i,mate i}:Finset P)⊆core ∧ ({j,mate j}:Finset P)⊆core ∧
    Disjoint ({i,mate i}:Finset P) {j,mate j} ∧
    pet.Adj i (mate i) ∧ pet.Adj j (mate j) ∧
    Closed pet (core \ ({i,mate i} ∪ {j,mate j})) := by
  obtain ⟨s1,s2,ds,e1,e2,e3,e4,ne1,ne2,eq⟩ := kits i j ei ej ij
  let w := third i j
  change pet.Adj 9 w ∨ pet.Adj 9 (mate w) at e3
  change pet.Adj w (mate w) at e4
  change (9:P)≠w at ne1
  change (9:P)≠mate w at ne2
  have h : ({9,w,mate w}:Finset P).card=3 := by simp [ne1,e4.ne,ne2]
  have tile : KelmansStarter.IsTile pet ({9,w,mate w}:Finset P) := by
    refine ⟨h,(Kelmans.tile_iff_path pet _ h).mpr ?_⟩
    rcases e3 with e|e
    · exact ⟨9,w,mate w,ne1,ne2,e4.ne,e,e4,rfl⟩
    · exact ⟨9,mate w,w,ne2,ne1,e4.ne.symm,e,e4.symm,by ext v; simp [or_comm,or_left_comm]⟩
  exact ⟨s1,s2,ds,e1,e2,eq.symm ▸ tile_closed tile⟩

#print axioms pet_repairs_with_center_port
end KelmansCactus.AtomicBridge.CentralLeafObstruction
