import FlexibleExit
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X H : Set V} {z r a b s t : V}

/-- A cycle on the reserved vertices handles one or two neighbor components.
If it also admits a spanning path between two shore contacts, the three-clique
obstruction is excluded whenever the first contact is an ordinary nonneighbor. -/
theorem SingletonCut.traceable_of_two_boundary_routes (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (sX : s ∈ X) (rs : ¬ G.Adj r s)
    (S : ∃ h ∈ H, G.Adj s h) (T : ∃ h ∈ H, G.Adj t h)
    (Q : PathOn G (insert r H)ᶜ) (close : G.Adj Q.last Q.first)
    (route : Traverses G (insert r H)ᶜ s t) : Traceable G := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨v,vH,sv⟩ := S
  obtain ⟨w,wH,tw⟩ := T
  obtain ⟨C⟩ := F.three_cliques_of_cycle sub on ⟨v,vH⟩ Q close no
  obtain ⟨i,vi⟩ := (C.cover v).mp vH
  obtain ⟨j,wj⟩ := (C.cover w).mp wH
  by_cases same : i = j
  · obtain ⟨k,ki,all⟩ := C.complete_to_another F sub on sX rs vi sv
    obtain ⟨u,uk⟩ := C.nonempty k
    exact no (C.splice F sub on route (fun eq => ki (eq.trans same.symm)) uk wj (all _ uk).symm tw)
  · exact no (C.splice F sub on route same vi wj sv.symm tw)

end Graffiti199Depleted.Catalogue.Incomplete
