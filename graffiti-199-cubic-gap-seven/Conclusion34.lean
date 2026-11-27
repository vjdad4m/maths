import Rows34
import EmbedPlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

set_option maxHeartbeats 3000000
set_option maxRecDepth 6500

private def coreRoutes34 (m : Fin 3) : List (ℕ × List (Fin 11)) :=
  ![[(1045075,[0,1,10,4,5,6,7,8,2,3,9]),(1045106,[0,1,10,4,5,6,7,8,2,3,9]),(1045107,[0,1,10,4,5,6,7,8,2,3,9]),(1047251,[0,1,2,3,6,5,7,4,10,8,9])],
    [(958456,[0,1,3,2,6,7,5,4,10,8,9]),(974840,[0,1,2,3,6,7,5,4,10,8,9]),(835576,[0,1,2,7,6,5,3,4,10,8,9]),(966648,[0,1,2,6,7,5,3,4,10,8,9]),(851960,[0,1,2,7,6,3,5,4,10,8,9]),(983032,[0,1,2,3,6,7,5,4,10,8,9])],
    [(2557934,[0,5,6,1,2,3,4,10,8,7,9]),(3082222,[0,5,6,1,2,3,4,10,8,7,9]),(3606510,[0,5,1,2,3,4,10,8,7,6,9]),(4130798,[0,1,2,3,4,10,8,7,5,6,9]),(2557950,[0,5,6,1,2,3,4,10,8,7,9]),(3606526,[0,5,1,2,3,4,10,8,7,6,9]),(985086,[0,5,6,7,1,2,3,4,10,8,9]),(3082238,[0,5,6,1,2,3,4,10,8,7,9]),(2033662,[0,1,2,3,4,10,8,7,5,6,9]),(4130814,[0,1,2,3,4,10,8,7,5,6,9]),(2564078,[0,1,3,2,6,5,4,10,8,7,9]),(3100646,[0,1,2,3,6,5,4,10,8,7,9])]] m

private def coreRoute34 (m : Fin 3) (tag : ℕ) : List (Fin 11) :=
  ((coreRoutes34 m).lookup tag).getD []

private def RoutesValid34 (m : Fin 3) : Prop :=
  ∀ i : Fin (residues34 m).length,
    let tag := (residues34 m).get i
    CoreRoute (edge34 m tag) (coreRoute34 m tag)

instance decidableRoutesValid34 (m : Fin 3) : Decidable (RoutesValid34 m) := by
  unfold RoutesValid34
  infer_instance

private theorem valid34_0 : RoutesValid34 0 := by decide
private theorem valid34_1 : RoutesValid34 1 := by decide
private theorem valid34_2 : RoutesValid34 2 := by decide

private theorem valid34 (m : Fin 3) : RoutesValid34 m := by
  fin_cases m
  · exact valid34_0
  · exact valid34_1
  · exact valid34_2

private theorem finish34 (m : Fin 3) {tag : ℕ} (hm : tag ∈ residues34 m) :
    CoreRoute (edge34 m tag) (coreRoute34 m tag) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
  exact valid34 m i

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem traceable_of_layout34 (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 11 ↪ V)
    (p : PathOn G {v | v ≠ f (Fin.last 10)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 10)) (f (layout34.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout34.port i)) (f (layout34.port j)))
    (dz : G.degree (f (Fin.last 10)) = 3)
    (cubic : ∃ i, G.degree (f (layout34.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  exact traceable_of_layout_classified layout34 m (family34 m) (family34_consistent m)
    (residues34 m) (classification34 m)
    (fun tag ht => Or.inl ⟨coreRoute34 m tag,finish34 m ht⟩)
    (by decide) (by decide) budget p split ports ind dz dm

#print axioms traceable_of_layout34

end Graffiti199Depleted.WiderOmission
