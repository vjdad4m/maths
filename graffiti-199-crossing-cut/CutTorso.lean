import CatalogueInterface

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Complete the separator to a clique on the retained vertices. -/
def cutTorso (G : SimpleGraph V) (D : Finset V) (B : Set V) : SimpleGraph (Bᶜ : Set V) where
  Adj x y := G.Adj x.val y.val ∨ (x ≠ y ∧ x.val ∈ D ∧ y.val ∈ D)
  symm := by
    rintro x y (edge|⟨ne,xD,yD⟩)
    · exact Or.inl edge.symm
    · exact Or.inr ⟨ne.symm,yD,xD⟩
  loopless := by
    rintro x (edge|⟨ne,_,_⟩)
    · exact G.loopless x.val edge
    · exact ne rfl

/-- Every edge from the discarded side has its retained end in the separator. -/
def ShoreBoundary (G : SimpleGraph V) (D : Finset V) (B : Set V) : Prop :=
  ∀ x ∈ B, ∀ y ∉ B, G.Adj x y → y ∈ D

variable {D : Finset V} {B : Set V}

private theorem reach_of_map_or_eq {X Y : Type*} {H : SimpleGraph X} {J : SimpleGraph Y}
    (f : X → Y) (map : ∀ x y, H.Adj x y → J.Adj (f x) (f y) ∨ f x = f y)
    {x y : X} (r : H.Reachable x y) : J.Reachable (f x) (f y) := by
  obtain ⟨w⟩ := r
  induction w with
  | nil => exact .rfl
  | cons e _ ih =>
    rcases map _ _ e with edge|eq
    · exact edge.reachable.trans ih
    · exact eq.symm ▸ ih

/-- Fill the separator and project every discarded survivor to one remaining
port. This preserves the connectivity required by the minimum-order argument. -/
theorem cutTorso_connectivity [Fintype V] [Fintype (Bᶜ : Set V)] {k : ℕ}
    (conn : ConnectivityAtLeast G k) (count : k ≤ D.card)
    (retained : k < Fintype.card (Bᶜ : Set V))
    (ports : ∀ d ∈ D, d ∉ B) (boundary : ShoreBoundary G D B) :
    ConnectivityAtLeast (cutTorso G D B) k := by
  classical
  let X : Set V := Bᶜ
  let H := cutTorso G D B
  refine ⟨retained,?_⟩
  intro U small
  let e : X ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let U' := U.map e
  have su : U'.card < k := by rwa [Finset.card_map]
  obtain ⟨p,pD,pU⟩ := Finset.exists_mem_not_mem_of_card_lt_card (show U'.card < D.card by omega)
  let S : Set V := {x | x ∉ U'}
  let T : Set X := {x | x ∉ U}
  let forward : S → T := fun x =>
    if hx : x.val ∉ B then
      ⟨⟨x.val,hx⟩,fun h => x.property (Finset.mem_map.mpr ⟨⟨x.val,hx⟩,h,rfl⟩)⟩
    else
      ⟨⟨p,ports p pD⟩,fun h => pU (Finset.mem_map.mpr ⟨⟨p,ports p pD⟩,h,rfl⟩)⟩
  let back : T → S := fun x =>
    ⟨x.val.val,fun h => by
      obtain ⟨z,zm,eq⟩ := Finset.mem_map.mp h
      exact x.property (Subtype.ext eq ▸ zm)⟩
  have right (x : T) : forward (back x) = x := by
    have hx : (back x).val ∉ B := x.val.property
    exact dif_pos hx
  have map (x y : S) (edge : (G.induce S).Adj x y) :
      (H.induce T).Adj (forward x) (forward y) ∨ forward x = forward y := by
    by_cases hx : x.val ∉ B <;> by_cases hy : y.val ∉ B
    · simp only [forward,dif_pos hx,dif_pos hy]
      exact Or.inl (Or.inl edge)
    · have xD := boundary y.val (Classical.not_not.mp hy) x.val hx edge.symm
      simp only [forward,dif_pos hx,dif_neg hy]
      by_cases eq : x.val = p
      · exact Or.inr (Subtype.ext (Subtype.ext eq))
      · exact Or.inl (Or.inr ⟨fun h => eq (congrArg Subtype.val h),xD,pD⟩)
    · have yD := boundary x.val (Classical.not_not.mp hx) y.val hy edge
      simp only [forward,dif_neg hx,dif_pos hy]
      by_cases eq : p = y.val
      · exact Or.inr (Subtype.ext (Subtype.ext eq))
      · exact Or.inl (Or.inr ⟨fun h => eq (congrArg Subtype.val h),pD,yD⟩)
    · simp only [forward,dif_neg hx,dif_neg hy]
      exact Or.inr True.intro
  have reach : (H.induce T).Preconnected := by
    intro x y
    simpa only [right] using reach_of_map_or_eq forward map
      ((conn.2 U' su).preconnected (back x) (back y))
  exact @SimpleGraph.Connected.mk _ (H.induce T) reach ⟨forward ⟨p,pU⟩⟩

/-- Every port sees a nonempty anticomplete shore on the other side of
a three-cut. The same proof works at any connectivity. -/
theorem contact_of_shore [Fintype V] {k : ℕ}
    (conn : ConnectivityAtLeast G k) (small : D.card ≤ k)
    (ports : ∀ d ∈ D, d ∉ B) (boundary : ShoreBoundary G D B)
    (nonempty : B.Nonempty) {p : V} (pD : p ∈ D) :
    ∃ x ∈ B, G.Adj p x := by
  classical
  obtain ⟨s,sB⟩ := nonempty
  let U := D.erase p
  have fewer : U.card < k := by
    have pos := Finset.card_pos.mpr ⟨p,pD⟩
    change (D.erase p).card < k
    rw [Finset.card_erase_of_mem pD]
    omega
  let X : Set V := {x | x ∉ U}
  have keepS : s ∈ X := fun h => ports s (Finset.mem_of_mem_erase h) sB
  have keepP : p ∈ X := Finset.not_mem_erase _ _
  obtain ⟨w⟩ := (conn.2 U fewer).preconnected ⟨s,keepS⟩ ⟨p,keepP⟩
  obtain ⟨x,xB,y,yB,xy⟩ := crossingOnWalk (U := {x : X | x.val ∈ B}) w sB (ports p pD)
  have yp : y.val = p :=
    Classical.byContradiction (fun ne => y.property (Finset.mem_erase.mpr
      ⟨ne,boundary x.val xB y.val yB xy⟩))
  have edge : G.Adj y.val x.val := xy.symm
  exact ⟨x.val,xB,yp ▸ edge⟩

#print axioms cutTorso_connectivity
#print axioms contact_of_shore

end Graffiti199Depleted.Catalogue
