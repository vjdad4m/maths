import MinimumCompactExclusion

namespace Graffiti199Depleted.CompactOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem singleton_of_short {X : List V} (ne : X ≠ []) (short : X.length < 2) :
    ∃ x, X = [x] := by
  cases X with
  | nil => exact (ne rfl).elim
  | cons x tail =>
    cases tail with
    | nil => exact ⟨x,rfl⟩
    | cons y tail => simp at short; omega

/-- If the neighbors of a cubic omission with a cubic neighbor are
independent, at least one of the two gaps between their visits on
a spanning path of its deletion has two or more intervening vertices. -/
theorem two_intervening_vertices (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) {z w a b c : V}
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (p : PathOn G {v | v ≠ z}) (L X Y R : List V)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c) :
    2 ≤ X.length ∨ 2 ≤ Y.length := by
  classical
  have limits := omission_constraints noTrace p
  by_contra! short
  have xen : X ≠ [] := by
    rintro rfl
    have adj : p.vertices = L ++ a :: b :: (Y ++ c :: R) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    exact limits.transitionOff _ _ _ _ adj ⟨za,zb⟩
  have yen : Y ≠ [] := by
    rintro rfl
    have adj : p.vertices = (L ++ (a :: X)) ++ b :: c :: R := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    exact limits.transitionOff _ _ _ _ adj ⟨zb,zc⟩
  obtain ⟨x,rfl⟩ := singleton_of_short xen short.1
  obtain ⟨y,rfl⟩ := singleton_of_short yen short.2
  have lne : L ≠ [] := by
    rintro rfl
    have isFirst : p.first = a := by
      have opt : p.vertices.head? = some a := by rw [split]; rfl
      rw [List.head?_eq_head p.nonempty] at opt
      exact Option.some.inj opt
    exact limits.firstOff (isFirst.symm ▸ za)
  have rne : R ≠ [] := by
    rintro rfl
    have isLast : p.last = c := by
      have opt : p.vertices.getLast? = some c := by
        rw [split,List.getLast?_append_of_ne_nil _ (by simp)]
        rfl
      rw [List.getLast?_eq_getLast p.nonempty] at opt
      exact Option.some.inj opt
    exact limits.lastOff (isLast.symm ▸ zc)
  have leftForm : ∃ U l, L = U ++ [l] :=
    ⟨L.dropLast,L.getLast lne,(List.dropLast_append_getLast lne).symm⟩
  obtain ⟨U,l,rfl⟩ := leftForm
  obtain ⟨r,T,rfl⟩ := List.exists_cons_of_ne_nil rne
  let core : List V := [l,a,x,b,y,c,r]
  have norm : p.vertices = U ++ core ++ T := by
    simpa only [core,List.append_assoc,List.cons_append,List.nil_append] using split
  have allNd : (U ++ core ++ T).Nodup := norm ▸ p.nodup
  have coreNd : core.Nodup := (List.nodup_append.mp (List.nodup_append.mp allNd).1).2.1
  have zOff : z ∉ core := by
    intro h
    have hv : z ∈ p.vertices := by rw [norm]; simp [h]
    exact (p.covers z).mp hv rfl
  have nd : (core ++ [z]).Nodup := by
    exact List.nodup_append.mpr ⟨coreNd,by simp,by simpa using zOff⟩
  let f : Fin 8 ↪ V :=
    ⟨(core ++ [z]).get, List.nodup_iff_injective_get.mp nd⟩
  exact no_compact_placement budget noTrace dz dw zw p f rfl U T norm za zb zc ab ac bc

#print axioms two_intervening_vertices

end Graffiti199Depleted.CompactOmission
