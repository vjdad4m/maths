import ThreePrivateSets

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {D : Finset V} {X Y : Set V} {r a b : V}

abbrev Noncontacts (G : SimpleGraph V) (X : Set V) (r : V) : Set V :=
  {x ∈ X | ¬ G.Adj r x}

def noncontactComponent (G : SimpleGraph V) (X : Set V) (r : V)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent) : Set V :=
  Subtype.val '' c.supp

/-- For components of the induced set of nonneighbors inside a component
of a three-cut, having a single actual contact among the neighbors of the
distinguished cut vertex suffices for the private-block bound. -/
theorem private_components_le_two
    (budget : treeNumber G ≤ 5) (conn : ConnectivityAtLeast G 3) (cut : D.card = 3)
    (offX : ∀ v ∈ D, v ∉ X) (offY : ∀ v ∈ D, v ∉ Y)
    (boundX : ShoreBoundary G D X) (boundY : ShoreBoundary G D Y)
    (apart : Disjoint X Y) (connY : (G.induce Y).Connected)
    (rD : r ∈ D) (aD : a ∈ D) (bD : b ∈ D) (ra : r ≠ a)
    (ports : ∀ v ∈ D, v = r ∨ v = a ∨ v = b)
    (missing : ∃ y ∈ Y, ¬ G.Adj r y) {n : Nat}
    (c : Fin n ↪ (G.induce (Noncontacts G X r)).ConnectedComponent) (p : Fin n → V)
    (rp : ∀ i, G.Adj r (p i))
    (single : ∀ i z, z ∈ X → G.Adj r z →
      (∃ u ∈ noncontactComponent G X r (c i), G.Adj u z) → z = p i) :
    n ≤ 2 := by
  classical
  let C (i : Fin n) : Set V := noncontactComponent G X r (c i)
  have ne (i : Fin n) : (C i).Nonempty := by
    obtain ⟨x,hx⟩ := (c i).nonempty_supp
    exact ⟨x.val,x,hx,rfl⟩
  have contained (i : Fin n) (u : V) (hu : u ∈ C i) : u ∈ X ∧ ¬ G.Adj r u := by
    obtain ⟨u,_,rfl⟩ := hu
    exact u.property
  have disjoint (i j : Fin n) (different : i ≠ j) : Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,eq⟩
    have yx : y = x := Subtype.ext eq
    exact different (c.injective (ConnectedComponent.eq_of_common_vertex hx (yx ▸ hy)))
  have boundary (i : Fin n) : ShoreBoundary G ({a,b,p i} : Finset V) (C i) := by
    intro u hu w hw uw
    have h := contained i u hu
    by_cases wX : w ∈ X
    · by_cases rw : G.Adj r w
      · have eq := single i w wX rw ⟨u,hu,uw⟩
        simp [eq]
      · obtain ⟨u,us,rfl⟩ := hu
        let w' : Noncontacts G X r := ⟨w,wX,rw⟩
        have step : (G.induce (Noncontacts G X r)).Adj u w' := uw
        exact (hw ⟨w',((c i).mem_supp_congr_adj step).mp us,rfl⟩).elim
    · rcases ports w (boundX _ h.1 _ wX uw) with eq|eq|eq
      · exact (h.2 (eq ▸ uw.symm)).elim
      · simp [eq]
      · simp [eq]
  exact private_sets_le_two budget conn cut offX offY boundX boundY apart connY
    rD aD bD ra missing C p ne contained rp disjoint boundary

#print axioms private_components_le_two

end Graffiti199Depleted.Catalogue
