import CliqueForced28

namespace Graffiti384b.Sparse28
open Finset SimpleGraph Core28
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Five-cliques survive both the restriction to nonleaves and the deletion
of nontriangle edges. Any clique in the resulting graph also lifts to G. -/
theorem core_five_iff :
    (∃ D,(triangleEdges (G.induce (nonleaves G:Set V))).IsNClique 5 D) ↔ ∃ C,G.IsNClique 5 C := by
  classical
  let P := nonleaves G
  let J := triangleEdges (G.induce (P:Set V))
  constructor
  · rintro ⟨D,cl⟩
    let f := Function.Embedding.subtype (fun x => x∈(P:Set V))
    refine ⟨D.map f,?_,(card_map _).trans cl.2⟩
    intro x xm y ym ne
    obtain ⟨i,im,rfl⟩ := mem_map.mp xm
    obtain ⟨j,jm,rfl⟩ := mem_map.mp ym
    exact (cl.1 im jm (fun h => ne (congrArg f h))).1
  · rintro ⟨C,cl⟩
    have core {x : V} (xc : x∈C) : x∈P := by
      have sub : C.erase x⊆G.neighborFinset x := fun w wm =>
        (G.mem_neighborFinset ..).mpr (cl.1 xc (mem_erase.mp wm).2 (mem_erase.mp wm).1.symm)
      have d := card_le_card sub
      rw [card_erase_of_mem xc,cl.2,card_neighborFinset_eq_degree] at d
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    let f : ↥C ↪ ↥(P:Set V) := ⟨fun x => ⟨x.val,core x.property⟩,fun _ _ h => Subtype.ext (congrArg (fun z : ↥(P:Set V) => z.val) h)⟩
    refine ⟨C.attach.map f,?_,(card_map _).trans ((Finset.card_attach (s:=C)).trans cl.2)⟩
    intro x xm y ym ne
    obtain ⟨a,_,rfl⟩ := mem_map.mp xm
    obtain ⟨b,_,rfl⟩ := mem_map.mp ym
    have ab : a.val≠b.val := fun eq => ne (congrArg f (Subtype.ext eq))
    obtain ⟨z,zc,zo⟩ := exists_mem_not_mem_of_card_lt_card (s:=({a.val,b.val}:Finset V)) (t:=C)
      (by rw [card_pair ab,cl.2]; decide)
    have za : z≠a.val := fun h => zo (h ▸ mem_insert_self ..)
    have zb : z≠b.val := fun h => zo (h ▸ mem_insert_of_mem (mem_singleton_self _))
    exact ⟨cl.1 a.property b.property ab,Or.inl ⟨f ⟨z,zc⟩,cl.1 a.property zc za.symm,cl.1 b.property zc zb.symm⟩⟩

/-- Direct catalogue bound on the original five-clique-free graph. -/
theorem original_five_free (ty : (types G).card=29) (nl : (nonleaves G).card=28)
    (free : G.CliqueFree 5) : gamma G≤bound G := by
  apply five_free_bound G ty nl
  intro D d
  obtain ⟨C,c⟩ := (core_five_iff G).mp ⟨D,d⟩
  exact free C c

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.core_five_iff
#print axioms Graffiti384b.Sparse28.original_five_free
