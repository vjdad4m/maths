import SparsePlacement

namespace Graffiti199Depleted

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]

namespace WiderOmission

omit [DecidableEq W] [Fintype W] in
private theorem split_filter_cons (f : W → Bool) {a : W} {Xs T : List W}
    (h : Xs.filter f = a :: T) : ∃ L R, Xs = L ++ a :: R ∧ R.filter f = T := by
  induction Xs with
  | nil => simp at h
  | cons b Y ih =>
    cases e : f b
    · have rest : Y.filter f = a :: T := by simpa [List.filter_cons,e] using h
      obtain ⟨L,R,s,hh⟩ := ih rest
      exact ⟨b :: L,R,congrArg (List.cons b) s,hh⟩
    · have same : b = a ∧ Y.filter f = T := by simpa [List.filter_cons,e] using h
      exact ⟨[],Y,by simp [same.1],same.2⟩

/-- A spanning path of the deletion visits the three neighbors of a
cubic omitted vertex in some order. -/
theorem ordered_omitted_neighbors {z : W} (p : PathOn G {v | v ≠ z}) (dz : G.degree z = 3) :
    ∃ a b c L X Y R, p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R ∧
      G.Adj z a ∧ G.Adj z b ∧ G.Adj z c := by
  let keep := fun v => decide (G.Adj z v)
  let ports := p.vertices.filter keep
  have mem (v : W) : v ∈ ports ↔ G.Adj z v := by
    simp only [ports,List.mem_filter,keep,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨(p.covers v).mpr h.ne.symm,h⟩⟩
  have eq : ports.toFinset = G.neighborFinset z := by
    ext v
    exact (List.mem_toFinset.trans (mem v)).trans (G.mem_neighborFinset _ _).symm
  have len : ports.length = 3 := by
    rw [← List.toFinset_card_of_nodup (p.nodup.filter keep),eq,G.card_neighborFinset_eq_degree,dz]
  obtain ⟨a,b,c,all⟩ := List.length_eq_three.mp len
  have za := (mem a).mp (by rw [all]; simp)
  have zb := (mem b).mp (by rw [all]; simp)
  have zc := (mem c).mp (by rw [all]; simp)
  obtain ⟨L,P,lP,pa⟩ := split_filter_cons keep (show p.vertices.filter keep = a :: [b,c] from all)
  obtain ⟨X,Q,xQ,qb⟩ := split_filter_cons keep pa
  obtain ⟨Y,R,yR,_⟩ := split_filter_cons keep qb
  exact ⟨a,b,c,L,X,Y,R,by rw [lP,xQ,yR]; simp [List.append_assoc],za,zb,zc⟩


#print axioms ordered_omitted_neighbors

end WiderOmission
end Graffiti199Depleted
