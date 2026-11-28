import ScoreFreePatch
namespace Graffiti384b.Exterior
open Finset SimpleGraph Four29 LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices 4 and 5 are the ears, attached to 0,1 and 2,3. Vertex 1 sees
both 2 and 3. The two private ports of 0 can then be repaired on a cut. -/
theorem fork_patch (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    (l : Fin 6 ↪ V)
    (first : G.neighborFinset (l 4)={l 0,l 1}) (second : G.neighborFinset (l 5)={l 2,l 3})
    (bc : G.Adj (l 1) (l 2)) (bd : G.Adj (l 1) (l 3))
    {x y : V} (xy : x≠y) (xp : x∈pool G (l 4) (l 5)) (yp : y∈pool G (l 4) (l 5))
    (ax : G.Adj (l 0) x) (ay : G.Adj (l 0) y)
    (uniqueRoot : ∀p∈({x,y}:Finset V),∀r∈roots G (l 4) (l 5),G.Adj p r → r=l 0)
    (privatePort : ∀p∈({x,y}:Finset V),∀r∈triangleContacts G (l 4) (l 5),G.Adj p r → r∈({x,y}:Finset V)) :
    gamma G≤bound G := by
  let P : Finset V := {l 0,l 1,l 5}
  let Q : Finset V := {l 4,l 2,l 3}
  let S : Finset V := {x,y}
  let X := pool G (l 4) (l 5)
  let W := X\S
  have ni {i j : Fin 6} (ne : i≠j) : l i≠l j := l.injective.ne ne
  have de : G.degree (l 4)=2 := by rw [←card_neighborFinset_eq_degree,first,card_pair (ni (by decide))]
  have df : G.degree (l 5)=2 := by rw [←card_neighborFinset_eq_degree,second,card_pair (ni (by decide))]
  have rootsEq : roots G (l 4) (l 5)={l 0,l 1}∪{l 2,l 3} := by rw [roots,first,second]
  have ea : G.Adj (l 4) (l 0) := (G.mem_neighborFinset ..).mp (first ▸ mem_insert_self ..)
  have eb : G.Adj (l 4) (l 1) := (G.mem_neighborFinset ..).mp (first ▸ mem_insert_of_mem (mem_singleton_self _))
  have fc : G.Adj (l 5) (l 2) := (G.mem_neighborFinset ..).mp (second ▸ mem_insert_self ..)
  have fd : G.Adj (l 5) (l 3) := (G.mem_neighborFinset ..).mp (second ▸ mem_insert_of_mem (mem_singleton_self _))
  have gap : Gap G P Q (l 0) := by
    constructor
    · simp [P,Q,l.injective.eq_iff]
    · simp [P]
    · exact card_pos.mpr ⟨l 4,mem_filter.mpr ⟨mem_insert_self ..,ea.symm⟩⟩
    · intro v vm ne
      rcases mem_insert.mp vm with rfl|m
      · exact (ne rfl).elim
      rcases mem_insert.mp m with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (2:Fin 6)≠3)) bc bd (by simp [Q]) (by simp [Q])
      · obtain rfl := mem_singleton.mp m
        exact PinnedColor34.two G (ni (by decide : (2:Fin 6)≠3)) fc fd (by simp [Q]) (by simp [Q])
    · intro v vm
      rcases mem_insert.mp vm with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (0:Fin 6)≠1)) ea eb (by simp [P]) (by simp [P])
      rcases mem_insert.mp m with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (1:Fin 6)≠5)) bc.symm fc.symm (by simp [P]) (by simp [P])
      · obtain rfl := mem_singleton.mp m
        exact PinnedColor34.two G (ni (by decide : (1:Fin 6)≠5)) bd.symm fd.symm (by simp [P]) (by simp [P])
  have dis : Disjoint (P∪Q) X := disjoint_left.mpr (by
    intro u um ux
    obtain ⟨hi,nr⟩ := mem_sdiff.mp ux
    rw [rootsEq] at nr
    have highU := (mem_filter.mp hi).2
    simp only [P,Q,mem_union,mem_insert,mem_singleton] at um nr
    rcases um with (rfl|rfl|rfl)|(rfl|rfl|rfl)
    all_goals first | omega | exact nr (by simp))
  have sp : S⊆X := insert_subset xp (singleton_subset_iff.mpr yp)
  have ports : Ports G P Q S W (l 0) := by
    refine ⟨gap,?_,disjoint_sdiff,?_⟩
    · exact dis.mono_right (union_subset sp sdiff_subset)
    · intro v vm
      exact (mem_insert.mp vm).elim (fun eq => eq ▸ ax) (fun eq => mem_singleton.mp eq ▸ ay)
  exact score_free_solution G t q h de df (ni (by decide)) P Q xy xp yp
    (rootsEq ▸ mem_union_left _ (mem_insert_self ..)) ports
    (mem_union_right _ (mem_insert_self ..)) (mem_union_left _ (by simp [P])) uniqueRoot privatePort
end Graffiti384b.Exterior
#print axioms Graffiti384b.Exterior.fork_patch
