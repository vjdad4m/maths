import Graffiti189TraceableOre189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset Graffiti189Ore
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

noncomputable def fillAcross (J : SimpleGraph V) (K E : Finset V) : SimpleGraph V :=
  ⟨fun u v => J.Adj u v ∨ (u≠v ∧ ((u∈K ∧ v∈E) ∨ (v∈K ∧ u∈E))),
   by intro u v; rintro (h|⟨n,p⟩); exact .inl h.symm; exact .inr ⟨n.symm,p.symm⟩,
   by intro u; rintro (h|⟨n,_⟩); exact J.loopless _ h; exact n rfl⟩

theorem fillAcross_mono (J : SimpleGraph V) (K E : Finset V) : J≤fillAcross J K E :=
  fun _ _ h=>.inl h

private theorem degree_add_cap (P : Finset V) (u : V) :
    (cap J (fun x=>x∈P)).degree (some u) = J.degree u + if u∈P then 1 else 0 := by
  classical
  let H := cap J (fun x=>x∈P)
  let I : V ↪ Option V := ⟨some,Option.some_injective V⟩
  let N := (J.neighborFinset u).map I
  by_cases hp : u∈P
  · have eq : H.neighborFinset (some u)=insert none N := by
      ext v
      cases v with
      | none => simp [H,N,cap,hp,mem_neighborFinset]
      | some v => simp [H,N,cap,mem_neighborFinset,I]
    change (H.neighborFinset (some u)).card=_
    rw [eq,card_insert_of_not_mem (by simp [N,I])]
    simp [N,hp,card_neighborFinset_eq_degree]
  have eq : H.neighborFinset (some u)=N := by
    ext v
    cases v with
    | none => simp [H,N,I,cap,hp,mem_neighborFinset]
    | some v => simp [H,N,cap,mem_neighborFinset,I]
  change (H.neighborFinset (some u)).card=_
  rw [eq]
  simp [N,hp,card_neighborFinset_eq_degree]

theorem traceable_cap_fillAcross (P K E : Finset V)
    (bound : ∀ x∈K,∀ y∈E,
      Fintype.card V ≤ J.degree x + (if x∈P then 1 else 0) +
        (J.degree y + (if y∈P then 1 else 0)))
    (route : Graffiti189Ore.Traceable (cap (fillAcross J K E) (fun x=>x∈P))) :
    Graffiti189Ore.Traceable (cap J (fun x=>x∈P)) := by
  classical
  let A := cap J (fun x=>x∈P)
  let B := cap (fillAcross J K E) (fun x=>x∈P)
  have sub : A≤B := by
    intro u v e
    cases u <;> cases v <;> first | exact e | exact .inl e
  apply Graffiti189Ore.traceable_closure sub _ route
  intro u v edge no
  cases u <;> cases v
  · exact (no edge).elim
  · exact (no edge).elim
  · exact (no edge).elim
  rename_i u v
  have edge' : (fillAcross J K E).Adj u v := edge
  have no' : ¬J.Adj u v := no
  obtain ⟨_,h⟩ := edge'.resolve_left no'
  change Fintype.card (Option V)≤(cap J (fun x=>x∈P)).degree (some u)+
    (cap J (fun x=>x∈P)).degree (some v)+1
  rw [Fintype.card_option,degree_add_cap P u,degree_add_cap P v]
  rcases h with ⟨uk,ve⟩|⟨vk,ue⟩
  · have q := bound u uk v ve
    omega
  have q := bound v vk u ue
  omega

#print axioms traceable_cap_fillAcross
end Graffiti189LongestPath.CrossSaturation
