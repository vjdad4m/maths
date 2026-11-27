import TwinTransfer25
import EmbedPlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

set_option maxHeartbeats 3000000
set_option maxRecDepth 6500

private def coreRoutes25 (m : Fin 3) : List (ℕ × List (Fin 11)) :=
  ![[],
    [(784376,[0,1,2,5,6,7,4,3,10,8,9]),(777208,[0,1,2,6,5,7,4,3,10,8,9]),(785400,[0,1,2,6,5,7,4,3,10,8,9]),(778232,[0,1,2,5,6,7,4,3,10,8,9]),(786424,[0,1,2,5,6,7,4,3,10,8,9])],
    [(783359,[0,1,2,3,10,8,7,4,6,5,9]),(1831935,[0,1,2,3,10,8,7,4,5,6,9]),(521215,[0,4,5,6,7,1,2,3,10,8,9]),(1569791,[0,1,2,3,10,8,7,4,5,6,9]),(1045503,[0,1,2,3,10,8,7,4,6,5,9]),(2094079,[0,1,2,3,10,8,7,4,5,6,9]),(2225135,[0,4,5,6,1,2,3,10,8,7,9]),(3273711,[0,4,5,1,2,3,10,8,7,6,9]),(2749423,[0,1,2,3,10,8,7,6,4,5,9]),(3797999,[0,1,2,3,10,8,7,6,4,5,9]),(2487279,[0,4,5,6,1,2,3,10,8,7,9]),(3535855,[0,1,2,3,10,8,7,5,4,6,9]),(3011567,[0,1,2,3,10,8,7,6,4,5,9]),(4060143,[0,1,2,3,10,8,7,5,4,6,9]),(2356207,[0,4,5,6,1,2,3,10,8,7,9]),(3404783,[0,1,2,3,10,8,7,4,5,6,9]),(2880495,[0,1,2,3,10,8,7,4,6,5,9]),(3929071,[0,1,2,3,10,8,7,4,5,6,9]),(2618351,[0,4,5,6,1,2,3,10,8,7,9]),(3666927,[0,1,2,3,10,8,7,4,5,6,9]),(3142639,[0,1,2,3,10,8,7,4,6,5,9]),(4191215,[0,1,2,3,10,8,7,4,5,6,9]),(2225151,[0,4,5,6,1,2,3,10,8,7,9]),(3273727,[0,4,5,1,2,3,10,8,7,6,9]),(2749439,[0,1,2,3,10,8,7,6,4,5,9]),(3798015,[0,1,2,3,10,8,7,6,4,5,9]),(2487295,[0,4,5,6,1,2,3,10,8,7,9]),(3535871,[0,1,2,3,10,8,7,5,4,6,9]),(3011583,[0,1,2,3,10,8,7,6,4,5,9]),(4060159,[0,1,2,3,10,8,7,5,4,6,9]),(2356223,[0,4,5,6,1,2,3,10,8,7,9]),(3404799,[0,1,2,3,10,8,7,4,5,6,9]),(2880511,[0,1,2,3,10,8,7,4,6,5,9]),(3929087,[0,1,2,3,10,8,7,4,5,6,9]),(2618367,[0,4,5,6,1,2,3,10,8,7,9]),(3666943,[0,1,2,3,10,8,7,4,5,6,9]),(3142655,[0,1,2,3,10,8,7,4,6,5,9]),(4191231,[0,1,2,3,10,8,7,4,5,6,9]),(2619371,[0,1,2,5,4,6,3,10,8,7,9]),(2423783,[0,1,2,6,5,4,3,10,8,7,9]),(3996647,[0,1,2,6,5,4,3,10,8,7,9]),(2621411,[0,1,2,5,4,6,3,10,8,7,9]),(2620391,[0,1,2,6,4,5,3,10,8,7,9])]] m

private def coreRoute25 (m : Fin 3) (tag : ℕ) : List (Fin 11) :=
  ((coreRoutes25 m).lookup tag).getD []

private def TwinCase25 (m : Fin 3) (tag : ℕ) : Prop :=
  (m = 0 ∧ tag = 786225) ∨ (m = 1 ∧ tag = 783352)

instance decidableTwinCase25 (m : Fin 3) (tag : ℕ) : Decidable (TwinCase25 m tag) := by
  unfold TwinCase25
  infer_instance

private def RoutesValid25 (m : Fin 3) : Prop :=
  ∀ i : Fin (residues25 m).length,
    let tag := (residues25 m).get i
    TwinCase25 m tag ∨ CoreRoute (edge25 m tag) (coreRoute25 m tag)

instance decidableRoutesValid25 (m : Fin 3) : Decidable (RoutesValid25 m) := by
  unfold RoutesValid25
  infer_instance

private theorem valid25_0 : RoutesValid25 0 := by decide
private theorem valid25_1 : RoutesValid25 1 := by decide
private theorem valid25_2 : RoutesValid25 2 := by decide

private theorem valid25 (m : Fin 3) : RoutesValid25 m := by
  fin_cases m
  · exact valid25_0
  · exact valid25_1
  · exact valid25_2

private theorem finish25 (m : Fin 3) {tag : ℕ} (hm : tag ∈ residues25 m) :
    TwinCase25 m tag ∨ CoreRoute (edge25 m tag) (coreRoute25 m tag) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
  exact valid25 m i

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem traceable_of_layout25 (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 11 ↪ V)
    (p : PathOn G {v | v ≠ f (Fin.last 10)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 10)) (f (layout25.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout25.port i)) (f (layout25.port j)))
    (dz : G.degree (f (Fin.last 10)) = 3)
    (cubic : ∃ i, G.degree (f (layout25.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  classical
  by_contra noTrace
  have placed := placement layout25 m p split noTrace ports ind dz dm
  obtain ⟨row,hrow⟩ := actual_row placed (family25_consistent m)
  rcases classification25 m row with ⟨T,tree⟩|⟨tag,ok,eq⟩
  · exact CompactOmission.six_tree_absurd budget hrow tree
  · have htag (i j) : G.Adj (f i) (f j) ↔ edge25 m tag i j = true :=
      (hrow i j).trans (by rw [eq i j]; rfl)
    rcases finish25 m ok with t|hPath
    · rcases t with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · apply noTrace (traceable_of_twins25 budget f 0 p split
          (twins_of_first25 f budget htag dz dm) ports ind dz dm ?_ ?_)
        · intro e
          exact (by decide : edge25 0 786225 10 6 ≠ true) ((htag _ _).mp e)
        · intro e
          exact (by decide : edge25 0 786225 1 6 ≠ true) ((htag _ _).mp e)
      · apply noTrace (traceable_of_twins25 budget f 1 p split
          (twins_of_second25 f budget htag dz dm) ports ind dz dm ?_ ?_)
        · intro e
          exact (by decide : edge25 1 783352 10 6 ≠ true) ((htag _ _).mp e)
        · intro e
          exact (by decide : edge25 1 783352 3 6 ≠ true) ((htag _ _).mp e)
    · exact noTrace (traceable_of_core_route (by decide) p split htag hPath)

#print axioms traceable_of_layout25

end Graffiti199Depleted.WiderOmission
