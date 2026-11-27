import TerminalCompression
open private reach_of_map_or_eq from CutTorso
namespace Graffiti199Depleted.Catalogue.Anchored
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {X H : Set V} {x p r : V}

theorem connected_remove_pendant (conn : (G.induce X).Connected) (pX : p ∈ X)
    (xp : G.Adj x p) (one : ∀ v ∈ X, G.Adj x v → v = p) :
    (G.induce {v | v ∈ X ∧ v ≠ x}).Connected := by
  classical
  let S := {v | v ∈ X ∧ v ≠ x}
  let ret (v : X) : S := if e : v.val = x then ⟨p,pX,xp.ne.symm⟩ else ⟨v.val,v.property,e⟩
  have pre : (G.induce S).Preconnected := by
    intro u v
    let i : X := ⟨u.val,u.property.1⟩
    let j : X := ⟨v.val,v.property.1⟩
    have ui : ret i = u := Subtype.ext (by simp [ret,i,u.property.2])
    have vj : ret j = v := Subtype.ext (by simp [ret,j,v.property.2])
    rw [← ui,← vj]
    apply reach_of_map_or_eq (H := G.induce X) (J := G.induce S) ret ?_ (conn.preconnected i j)
    intro a b adj
    have edge : G.Adj a.val b.val := adj
    by_cases ax : a.val = x <;> by_cases bx : b.val = x
    · right; apply Subtype.ext; simp [ret,ax,bx]
    · right; apply Subtype.ext; simpa [ret,ax,bx] using (one _ b.property (ax ▸ edge)).symm
    · right; apply Subtype.ext; simpa [ret,ax,bx] using one _ a.property (bx ▸ edge.symm)
    · left; change G.Adj (ret a).val (ret b).val; simpa [ret,ax,bx] using edge
  exact @SimpleGraph.Connected.mk _ (G.induce S) pre ⟨⟨p,pX,xp.ne.symm⟩⟩

theorem two_of_universal_vertex [Fintype (insert r H : Set V)]
    (conn : (G.induce H).Connected) (off : r ∉ H) (complete : ∀ v ∈ H, G.Adj r v)
    (size : 2 < Fintype.card (insert r H : Set V)) :
    ConnectivityAtLeast (G.induce (insert r H)) 2 := by
  classical
  let W : Set V := insert r H
  let rr : W := ⟨r,Or.inl rfl⟩
  refine ⟨size,?_⟩
  intro D few
  have pre : (DeletionGraph (G.induce W) D).Preconnected := by
    by_cases keep : rr ∈ D
    · have only {v : W} (mem : v ∈ D) : v = rr := by
        by_contra ne
        have t : ({v,rr} : Finset W) ⊆ D := Finset.insert_subset mem (Finset.singleton_subset_iff.mpr keep)
        have bound := Finset.card_le_card t
        rw [Finset.card_pair ne] at bound; omega
      let f (v : H) : Survives D := ⟨⟨v.val,Or.inr v.property⟩,fun mem =>
        off ((show v.val = r from congrArg Subtype.val (only mem)) ▸ v.property)⟩
      have onto (v : Survives D) : ∃ t, f t = v := by
        have vr : v.val ≠ rr := fun e => v.property (e.symm ▸ keep)
        have vh : v.val.val ∈ H := v.val.property.resolve_left (fun eq => vr (Subtype.ext eq))
        exact ⟨⟨v.val.val,vh⟩,rfl⟩
      intro u v
      obtain ⟨i,rfl⟩ := onto u
      obtain ⟨j,rfl⟩ := onto v
      exact reach_of_map_or_eq (H := G.induce H) (J := DeletionGraph (G.induce W) D) f
        (fun _ _ h => Or.inl h) (conn.preconnected i j)
    · let center : Survives D := ⟨rr,keep⟩
      have reach (i : Survives D) : (DeletionGraph (G.induce W) D).Reachable center i := by
        rcases i.val.property with e|h
        · exact (show center = i from Subtype.ext (Subtype.ext e.symm)) ▸ Reachable.rfl
        · exact (show (DeletionGraph (G.induce W) D).Adj center i from complete _ h).reachable
      exact fun u v => (reach u).symm.trans (reach v)
  have room : D.card < (Finset.univ : Finset W).card := by rw [Finset.card_univ]; exact few.trans size
  obtain ⟨v,_,vm⟩ := Finset.exists_mem_not_mem_of_card_lt_card room
  exact @SimpleGraph.Connected.mk _ (DeletionGraph (G.induce W) D) pre ⟨⟨v,vm⟩⟩

#print axioms two_of_universal_vertex
end Graffiti199Depleted.Catalogue.Anchored

