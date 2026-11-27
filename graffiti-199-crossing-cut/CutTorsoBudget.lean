import ChordlessConnector
import SubdividedTree

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {D : Finset V} {B : Set V}

private theorem triangle_absurd {W : Type*} {H : SimpleGraph W} (tree : H.IsTree)
    {a b c : W} (ab : H.Adj a b) (ac : H.Adj a c) (cb : H.Adj c b) : False := by
  let p : H.Walk a b := .cons ac cb.toWalk
  have path1 : ab.toWalk.IsPath := by simp [SimpleGraph.Adj.toWalk,Walk.isPath_def,ab.ne]
  have path2 : p.IsPath := by
    simp [p,SimpleGraph.Adj.toWalk,Walk.isPath_def,ab.ne,ac.ne,cb.ne]
  have eq := (tree.existsUnique_path a b).unique path1 path2
  have len := congrArg Walk.length eq
  change 1 = 2 at len
  omega

/-- An induced tree in a clique-completed shore uses at most one filled
edge. Replace that edge by a shortest connector through the discarded
shore to preserve the induced-tree bound. -/
theorem cutTorso_treeNumber_le [Fintype V] [Fintype (Bᶜ : Set V)]
    (boundary : ShoreBoundary G D B) (connected : (G.induce B).Preconnected)
    (contacts : ∀ x ∈ D, ∃ y ∈ B, G.Adj x y) :
    treeNumber (cutTorso G D B) ≤ treeNumber G := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro T ht
  let X : Set V := Bᶜ
  let W : Set X := ↑T
  let H := (cutTorso G D B).induce W
  have tree : H.IsTree := (Finset.mem_filter.mp ht).2
  let f : W ↪ V := ⟨fun x => x.val.val,fun _ _ eq => Subtype.ext (Subtype.ext eq)⟩
  change T.card ≤ treeNumber G
  have hcard : Fintype.card W = T.card := Fintype.card_coe T
  have real_to_old (x y : W) (e : G.Adj (f x) (f y)) : H.Adj x y := Or.inl e
  by_cases every : ∀ x y : W, H.Adj x y → G.Adj (f x) (f y)
  · have count := card_le_treeNumber_of_induced_copy f (fun x y => ⟨real_to_old x y,every x y⟩) tree
    simpa only [hcard] using count
  · push_neg at every
    obtain ⟨u,v,uv,nonedge⟩ := every
    have Dpair {x y : W} (edge : H.Adj x y) (fake : ¬ G.Adj (f x) (f y)) :
        f x ∈ D ∧ f y ∈ D := by
      exact ((show G.Adj (f x) (f y) ∨
          (x.val ≠ y.val ∧ f x ∈ D ∧ f y ∈ D) from edge).resolve_left fake).2
    obtain ⟨uD,vD⟩ := Dpair uv nonedge
    have joined {x y : W} (ne : x ≠ y) (xD : f x ∈ D) (yD : f y ∈ D) : H.Adj x y :=
      Or.inr ⟨fun e => ne (Subtype.ext e),xD,yD⟩
    have only_ports (x : W) (xD : f x ∈ D) : x = u ∨ x = v := by
      by_cases xu : x = u
      · exact Or.inl xu
      · by_cases xv : x = v
        · exact Or.inr xv
        · exact (triangle_absurd tree uv (joined (Ne.symm xu) uD xD) (joined xv xD vD)).elim
    have old (x y : W) : G.Adj (f x) (f y) ↔ H.Adj x y ∧
        ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
      constructor
      · intro edge
        refine ⟨real_to_old x y edge,?_⟩
        rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · exact nonedge edge
        · exact nonedge edge.symm
      · rintro ⟨edge,good⟩
        apply Classical.byContradiction
        intro fake
        obtain ⟨xD,yD⟩ := Dpair edge fake
        rcases only_ports x xD with rfl|rfl <;> rcases only_ports y yD with rfl|rfl
        · exact H.loopless _ edge
        · exact good (Or.inl ⟨rfl,rfl⟩)
        · exact good (Or.inr ⟨rfl,rfl⟩)
        · exact H.loopless _ edge
    obtain ⟨p⟩ := exists_chordless_connector connected (f.injective.ne uv.ne) nonedge
      (contacts _ uD) (contacts _ vD)
    have disjoint (x : W) (i : Fin (p.last+1)) : f x ≠ p.inside i := by
      intro e
      have fx : f x ∉ B := x.val.property
      exact fx (e.symm ▸ p.kept i)
    have ends (x : W) (i : Fin (p.last+1)) :
        G.Adj (f x) (p.inside i) ↔ (x = u ∧ i.val = 0) ∨ (x = v ∧ i.val = p.last) := by
      constructor
      · intro edge
        rcases only_ports x (boundary _ (p.kept i) _ x.val.property edge.symm) with rfl|rfl
        · exact Or.inl ⟨rfl,(p.from_u i).mp edge⟩
        · exact Or.inr ⟨rfl,(p.from_v i).mp edge⟩
      · rintro (⟨rfl,h⟩|⟨rfl,h⟩)
        · exact (p.from_u i).mpr h
        · exact (p.from_v i).mpr h
    have count := card_le_treeNumber_of_subdivided_edge tree uv f p.inside disjoint old p.chain ends
    rw [hcard] at count
    omega

#print axioms cutTorso_treeNumber_le

end Graffiti199Depleted.Catalogue
