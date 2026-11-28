import RootedOreMissingPair189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- A prescribed vertex z is placed at the start before completing the
remaining high clique minus its protected pair. -/
theorem low_root_route_of_one_protected_pair
    (root e f : V) (ef : e≠f) (ez : e≠root) (fz : f≠root)
    (large : 6≤Fintype.card V) (start : J.Adj root e)
    (ore : ∀ u v,u≠v → u≠root → v≠root → ¬((u=e ∧ v=f) ∨ (u=f ∧ v=e)) →
      ¬J.Adj u v → Fintype.card V≤J.degree u+J.degree v) :
    RootedSpan J root := by
  classical
  let A := (univ : Finset V).erase root
  let H : SimpleGraph V :=
    ⟨fun u v=>J.Adj u v ∨
      (u∈A ∧ v∈A ∧ u≠v ∧ ¬((u=e ∧ v=f) ∨ (u=f ∧ v=e))),
      by
        intro u v
        rintro (h|⟨uA,vA,ne,safe⟩)
        · exact .inl h.symm
        exact .inr ⟨vA,uA,ne.symm,fun h=>safe (h.elim (fun q=>.inr ⟨q.2,q.1⟩) (fun q=>.inl ⟨q.2,q.1⟩))⟩,
      by intro u; rintro (h|⟨_,_,ne,_⟩); exact J.loopless _ h; exact ne rfl⟩
  have sub : J≤H := fun _ _ h=>.inl h
  have sz : 5≤A.card := by
    change 5≤((univ : Finset V).erase root).card
    rw [card_erase_of_mem (mem_univ _),card_univ]
    omega
  have eo : e∈A := mem_erase.mpr ⟨ez,mem_univ _⟩
  have fo : f∈A := mem_erase.mpr ⟨fz,mem_univ _⟩
  have kem : ∀ u∈A,∀ v∈A,u≠v → ¬((u=e ∧ v=f) ∨ (u=f ∧ v=e)) → H.Adj u v := by
    intro u ua v va uv h
    exact .inr ⟨ua,va,uv,h⟩
  have p := route_between_in_clique_except_pair (G:=H) A sz (e:=e) (f:=f) kem eo fo ef
  have nz : root∉A := by simp [A]
  have all : insert root A=univ := insert_erase (mem_univ _)
  have q : RouteOn H univ root f := all ▸ p.prefix (sub start) nz
  obtain ⟨w,wp,ws⟩ := q
  apply Graffiti189Ore.rooted_closure sub root _ ⟨f,w,wp,fun v=>(ws v).mpr (mem_univ _)⟩
  intro u v h no
  have h' : J.Adj u v ∨ (u∈A ∧ v∈A ∧ u≠v ∧ ¬((u=e ∧ v=f) ∨ (u=f ∧ v=e))) := h
  obtain ⟨ua,va,uv,safe⟩ := h'.resolve_left no
  exact ore u v uv (mem_erase.mp ua).1 (mem_erase.mp va).1 safe no

#print axioms low_root_route_of_one_protected_pair
end Graffiti189LongestPath.CrossSaturation
