import RootedIndependence
open private reach_of_map_or_eq from CutTorso
namespace Graffiti199Depleted.Catalogue.Anchored
open SimpleGraph
variable {V : Type*}

def exteriorGraph (G : SimpleGraph V) (W : Set V) : SimpleGraph (Option W) where
  Adj
    | none, none => False
    | some x, some y => G.Adj x.val y.val
    | none, some y => ∃ u ∉ W, G.Adj u y.val
    | some x, none => ∃ u ∉ W, G.Adj u x.val
  symm := by rintro (_|x) (_|y) h <;> first | exact h | exact h.symm
  loopless := by rintro (_|v); exact id; exact G.loopless _

noncomputable def collapse (W : Set V) (v : V) : Option W := by
  classical
  exact if h : v ∈ W then some ⟨v,h⟩ else none

theorem collapse_edge (G : SimpleGraph V) (W : Set V) {u v : V} (e : G.Adj u v) :
    (exteriorGraph G W).Adj (collapse W u) (collapse W v) ∨ collapse W u = collapse W v := by
  classical
  by_cases um : u ∈ W <;> by_cases vm : v ∈ W
  · left; simpa [collapse,um,vm,exteriorGraph] using e
  · left; simpa [collapse,um,vm,exteriorGraph] using (show ∃ y ∉ W, G.Adj y u from ⟨v,vm,e.symm⟩)
  · left; simpa [collapse,um,vm,exteriorGraph] using (show ∃ y ∉ W, G.Adj y v from ⟨u,um,e⟩)
  · right; simp [collapse,um,vm]

/-- Compress the deleted part to a single vertex. Three-connectivity of the
original graph and two-connectivity of the exterior suffice for three-connectivity
of the compression. -/
theorem exterior_three [Fintype V] {G : SimpleGraph V} {W : Set V} [Fintype W]
    (conn : ConnectivityAtLeast G 3) (two : ConnectivityAtLeast (G.induce W) 2)
    {z : V} (off : z ∉ W) : ConnectivityAtLeast (exteriorGraph G W) 3 := by
  classical
  let K := exteriorGraph G W
  have size := two.1
  refine ⟨by rw [Fintype.card_option]; omega,?_⟩
  intro D small
  let f : W ↪ Option W := ⟨some,Option.some_injective _⟩
  let S := (Finset.univ : Finset W).filter (fun v => some v ∈ D)
  have spec (v : W) : v ∈ S ↔ some v ∈ D := by simp [S]
  have sub : S.map f ⊆ D := by
    intro i hi
    obtain ⟨w,wm,rfl⟩ := Finset.mem_map.mp hi
    exact (spec w).mp wm
  have sl : S.card ≤ D.card := by simpa only [Finset.card_map] using Finset.card_le_card sub
  have pre : (DeletionGraph K D).Preconnected := by
    by_cases deleted : none ∈ D
    · have sub' : insert none (S.map f) ⊆ D := Finset.insert_subset deleted sub
      have outside : none ∉ S.map f := by simp [f]
      have shorter := Finset.card_le_card sub'
      rw [Finset.card_insert_of_not_mem outside,Finset.card_map] at shorter
      let incl : Survives S → Survives D := fun w => ⟨some w.val,fun h => w.property ((spec _).mpr h)⟩
      have onto (i : Survives D) : ∃ w, incl w = i := by
        rcases i with ⟨_|v,hi⟩
        · exact (hi deleted).elim
        · exact ⟨⟨v,fun h => hi ((spec _).mp h)⟩,rfl⟩
      intro i j
      obtain ⟨u,rfl⟩ := onto i
      obtain ⟨v,rfl⟩ := onto j
      exact reach_of_map_or_eq (H := DeletionGraph (G.induce W) S) (J := DeletionGraph K D) incl
        (fun _ _ e => Or.inl e) ((two.2 S (by omega)).preconnected u v)
    · let val : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      let T := S.map val
      have ct : T.card = S.card := Finset.card_map ..
      let lift (u : Survives T) : Survives D := ⟨collapse W u.val,by
        by_cases h : u.val ∈ W
        · have hm : (⟨u.val,h⟩ : W) ∉ S := fun m => u.property (Finset.mem_map.mpr ⟨_,m,rfl⟩)
          simpa [collapse,h] using (show some (⟨u.val,h⟩ : W) ∉ D from fun m => hm ((spec _).mpr m))
        · simpa [collapse,h] using deleted⟩
      have onto (t : Survives D) : ∃ v, lift v = t := by
        rcases t with ⟨_|v,ht⟩
        · have zT : z ∉ T := by rintro h; obtain ⟨u,_,e⟩ := Finset.mem_map.mp h; exact off (e ▸ u.property)
          exact ⟨⟨z,zT⟩,Subtype.ext (by simp [lift,collapse,off])⟩
        · have vT : v.val ∉ T := by
            intro h
            obtain ⟨w,m,e⟩ := Finset.mem_map.mp h
            have same : w = v := Subtype.ext e
            exact ht ((spec _).mp (same ▸ m))
          exact ⟨⟨v.val,vT⟩,Subtype.ext (by simp [lift,collapse,v.property])⟩
      intro i j
      obtain ⟨u,rfl⟩ := onto i
      obtain ⟨v,rfl⟩ := onto j
      apply reach_of_map_or_eq (H := DeletionGraph G T) (J := DeletionGraph K D) lift ?_
        ((conn.2 T (by omega)).preconnected u v)
      intro l q e
      rcases collapse_edge G W e with adj|same
      · exact Or.inl adj
      · exact Or.inr (Subtype.ext same)
  have room : D.card < (Finset.univ : Finset (Option W)).card := by
    rw [Finset.card_univ,Fintype.card_option]; omega
  obtain ⟨v,_,h⟩ := Finset.exists_mem_not_mem_of_card_lt_card room
  exact @SimpleGraph.Connected.mk _ (DeletionGraph K D) pre ⟨⟨v,h⟩⟩

#print axioms exterior_three
end Graffiti199Depleted.Catalogue.Anchored
