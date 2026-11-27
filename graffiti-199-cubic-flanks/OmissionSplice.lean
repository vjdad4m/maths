import OmissionObstruction

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}

private theorem traceable_of_omission_permutation [DecidableEq V]
    (p : PathOn G {v | v ≠ z}) {L : List V}
    (perm : L.Perm (z :: p.vertices)) (chain : L.Chain' G.Adj) :
    Catalogue.Traceable G := by
  have off : z ∉ p.vertices := fun h => (p.covers z).mp h rfl
  have nd : L.Nodup := (List.Perm.nodup_iff perm).mpr (List.nodup_cons.mpr ⟨off,p.nodup⟩)
  have all (v : V) : v ∈ L := by
    apply perm.mem_iff.mpr
    by_cases eq : v = z
    · simp [eq]
    · exact List.mem_cons_of_mem _ ((p.covers v).mpr eq)
  have ne : L ≠ [] := by
    intro h
    have mem := all z
    rw [h] at mem
    exact List.not_mem_nil mem
  apply Catalogue.traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  exact ⟨⟨L,ne,chain,nd,fun v => iff_of_true (all v) trivial⟩⟩

/-- A chord between the predecessors of two neighbors of an omitted
vertex permits the middle block to be reversed and the vertex inserted. -/
theorem traceable_of_predecessor_chord [DecidableEq V]
    (p : PathOn G {v | v ≠ z}) {L M R : List V} {a x b y : V}
    (split : p.vertices = (L ++ [a]) ++ ((x :: M) ++ [b]) ++ (y :: R))
    (xz : G.Adj x z) (zy : G.Adj z y) (ab : G.Adj a b) :
    Catalogue.Traceable G := by
  let A := L ++ [a]
  let B := (x :: M) ++ [b]
  let C := y :: R
  have old : (A ++ (B ++ C)).Chain' G.Adj := by
    simpa only [split,A,B,C,List.append_assoc] using p.chain
  have Achain := old.left_of_append
  have Bchain := old.right_of_append.left_of_append
  have Cchain := old.right_of_append.right_of_append
  have rev := (List.chain'_reverse).mpr
    (Bchain.imp (R := G.Adj) (S := flip G.Adj) (fun _ _ adj => adj.symm))
  have hbc : (B.reverse ++ z :: C).Chain' G.Adj := by
    apply rev.append (List.chain'_cons.mpr ⟨zy,Cchain⟩)
    intro u hu v hv
    have ux : x = u := by
      rw [List.getLast?_reverse] at hu
      simpa [B] using hu
    have vz : z = v := by simpa [C] using hv
    exact ux ▸ vz ▸ xz
  have ch : (A ++ (B.reverse ++ z :: C)).Chain' G.Adj := by
    apply Achain.append hbc
    intro u hu v hv
    have au : a = u := by simpa [A] using hu
    have bv : b = v := by
      simp [B,List.reverse_append] at hv
      exact hv
    exact au ▸ bv ▸ ab
  have one : (A ++ (B.reverse ++ z :: C)).Perm (A ++ (B ++ z :: C)) :=
    ((List.reverse_perm B).append_right (z :: C)).append_left A
  have two : (A ++ (B ++ z :: C)).Perm (z :: (A ++ (B ++ C))) := by
    simpa only [List.append_assoc] using
      (List.perm_middle (a := z) (l₁ := A ++ B) (l₂ := C))
  have perm : (A ++ (B.reverse ++ z :: C)).Perm (z :: p.vertices) := by
    simpa only [A,B,C,split,List.append_assoc] using one.trans two
  exact traceable_of_omission_permutation p perm ch

/-- A terminal link to the predecessor of an omitted vertex's
neighbor rotates the suffix and makes that neighbor an endpoint. -/
theorem traceable_of_terminal_predecessor [DecidableEq V]
    (p : PathOn G {v | v ≠ z}) {L R : List V} {a x : V}
    (split : p.vertices = (L ++ [a]) ++ x :: R)
    (xz : G.Adj x z) (jump : G.Adj a p.last) :
    Catalogue.Traceable G := by
  let A := L ++ [a]
  let B := x :: R
  have old : (A ++ B).Chain' G.Adj := by simpa only [A,B,split] using p.chain
  have b := old.right_of_append
  have rev := (List.chain'_reverse).mpr
    (b.imp (R := G.Adj) (S := flip G.Adj) (fun _ _ adj => adj.symm))
  have last : B.reverse.head? = some p.last := by
    rw [List.head?_reverse,← List.getLast?_append_of_ne_nil A (by simp [B]),← show p.vertices = A ++ B from split]
    exact List.getLast?_eq_getLast p.nonempty
  have tail : (B.reverse ++ [z]).Chain' G.Adj := by
    apply rev.append (List.chain'_singleton (R := G.Adj) z)
    intro u hu v hv
    have ux : x = u := by
      rw [List.getLast?_reverse] at hu
      simpa [B] using hu
    have vz : z = v := by simpa using hv
    exact ux ▸ vz ▸ xz
  have ch : (A ++ (B.reverse ++ [z])).Chain' G.Adj := by
    apply old.left_of_append.append tail
    intro u hu v hv
    have au : a = u := by simpa [A] using hu
    have tv : p.last = v := by
      simpa [last] using hv
    exact au ▸ tv ▸ jump
  have one : (A ++ (B.reverse ++ [z])).Perm (A ++ (B ++ [z])) :=
    ((List.reverse_perm B).append_right [z]).append_left A
  have two : (A ++ (B ++ [z])).Perm (z :: (A ++ B)) := by
    simpa only [List.append_assoc,List.append_nil] using
      (List.perm_middle (a := z) (l₁ := A ++ B) (l₂ := []))
  have perm : (A ++ (B.reverse ++ [z])).Perm (z :: p.vertices) := by
    simpa only [A,B,split] using one.trans two
  exact traceable_of_omission_permutation p perm ch

#print axioms traceable_of_predecessor_chord
#print axioms traceable_of_terminal_predecessor

end Graffiti199Depleted
