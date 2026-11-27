import InducedBudget
import TwinReduction
import MinimumContraction

namespace Graffiti199Depleted

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- In a three-connected graph on at least five vertices, an adjacent
twin has degree at least four. Removing its two other contacts if it
had degree three would separate the twin pair. -/
theorem AdjacentTwins.degree_ge_four {u v : V} (tw : AdjacentTwins G u v)
    (conn : Catalogue.ConnectivityAtLeast G 3) (order : 5 ≤ Fintype.card V) :
    4 ≤ G.degree v := by
  by_contra! low
  let D := (G.neighborFinset v).erase u
  have uN := (G.mem_neighborFinset v u).mpr tw.edge.symm
  have small : D.card < 3 := by
    change ((G.neighborFinset v).erase u).card < 3
    rw [Finset.card_erase_of_mem uN,G.card_neighborFinset_eq_degree]
    omega
  have ou : u ∉ D := Finset.not_mem_erase _ _
  have ov : v ∉ D := by
    intro h
    exact G.loopless v ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase h))
  let E := insert u (insert v D)
  have le : E.card ≤ D.card + 2 := by
    dsimp [E]
    have h := Finset.card_insert_le v D
    have hh := Finset.card_insert_le u (insert v D)
    omega
  have eproper : E.card < (Finset.univ : Finset V).card := by rw [Finset.card_univ]; omega
  obtain ⟨w,_,we⟩ := Finset.exists_mem_not_mem_of_card_lt_card eproper
  have wOff := show w ≠ u ∧ w ≠ v ∧ w ∉ D by simpa [E] using we
  let X : Set V := {x | x ∉ D}
  let shore : Set X := {x | x.val = u ∨ x.val = v}
  have reaches := (conn.2 D small).preconnected (⟨u,ou⟩ : X) (⟨w,wOff.2.2⟩ : X)
  obtain ⟨p⟩ := reaches
  have west : (⟨u,ou⟩ : X) ∈ shore := Or.inl rfl
  have east : (⟨w,wOff.2.2⟩ : X) ∉ shore := fun h => h.elim wOff.1 wOff.2.1
  obtain ⟨a,ha,b,hb,e⟩ := crossingOnWalk (G := G.induce X) p west east
  have bu : b.val ≠ u := fun h => hb (Or.inl h)
  have bv : b.val ≠ v := fun h => hb (Or.inr h)
  have adj : G.Adj v b.val := by
    change G.Adj a.val b.val at e
    rcases ha with e'|e'
    · exact (tw.same _ bu bv).mp (e' ▸ e)
    · exact e' ▸ e
  exact b.property (Finset.mem_erase.mpr ⟨bu,(G.mem_neighborFinset _ _).mpr adj⟩)

private theorem card_delete {u : V} :
    Fintype.card {x : V // x ≠ u} = Fintype.card V - 1 := by
  rw [Fintype.card_subtype_compl (fun x => x = u)]
  simp

/-- In the archived cut case, deleting one of two adjacent twins
preserves three-connectivity if their common neighbors have degree
at least four. -/
theorem AdjacentTwins.connectivity_delete {u v : V} (tw : AdjacentTwins G u v)
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (order : 5 ≤ Fintype.card V)
    (common : ∀ x, G.Adj x u → G.Adj x v → 4 ≤ G.degree x) :
    Catalogue.ConnectivityAtLeast (G.induce {x | x ≠ u}) 3 := by
  classical
  let S : Set V := {x | x ≠ u}
  let H := G.induce S
  have sz : Fintype.card S = Fintype.card V - 1 := card_delete (u := u)
  have gt : 3 < Fintype.card S := by omega
  refine ⟨gt,?_⟩
  intro D small
  let emb : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let R := insert u (D.map emb)
  have rsize : R.card ≤ 3 := by
    have le := Finset.card_insert_le u (D.map emb)
    rw [Finset.card_map] at le
    change (insert u (D.map emb)).card ≤ 3
    omega
  let X : Set V := {x | x ∉ R}
  have keepNot (a : X) : a.val ≠ u := fun e => a.property (by simp [R,e])
  have near (x : X) : ∃ y : X, G.Adj x.val y.val := by
    apply Classical.byContradiction
    intro absent
    have sub : G.neighborFinset x.val ⊆ R := by
      intro y hy
      by_cases h : y ∈ R
      · exact h
      · exact False.elim (absent ⟨⟨y,h⟩,(G.mem_neighborFinset _ _).mp hy⟩)
    have deg3 := degree_of_small_deletion_preconnected (G := G) (by omega)
      (fun D hD => (conn.2 D hD).preconnected) x.val
    have hitsU : G.Adj x.val u := by
      apply Classical.byContradiction
      intro noU
      have smallSub : G.neighborFinset x.val ⊆ D.map emb := by
        intro y hy
        rcases Finset.mem_insert.mp (sub hy) with yu|keep
        · exact (noU (yu ▸ (G.mem_neighborFinset _ _).mp hy)).elim
        · exact keep
      have hh := Finset.card_le_card smallSub
      rw [Finset.card_map,G.card_neighborFinset_eq_degree] at hh
      omega
    have deg4 : 4 ≤ G.degree x.val := by
      by_cases e : x.val = v
      · rw [e]
        exact tw.degree_ge_four conn order
      · exact common x.val hitsU (((tw.same _ (keepNot x) e).mp hitsU.symm).symm)
    have bound := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at bound
    omega
  have connected : (G.induce X).Preconnected := by
    intro a b
    obtain ⟨a',ae⟩ := near a
    obtain ⟨b',be⟩ := near b
    exact edgeReach_iff_crossing_between_surviving_edges.mpr cross R rsize a a' b b' ae be
  let T : Set S := {x | x ∉ D}
  let forward : X → T :=
    fun a => ⟨⟨a.val,keepNot a⟩,fun h => a.property (Finset.mem_insert_of_mem
      (Finset.mem_map.mpr ⟨⟨a.val,keepNot a⟩,h,rfl⟩))⟩
  let back : T → X := fun a =>
    ⟨a.val.val,by
      intro h
      rcases Finset.mem_insert.mp h with hu|hm
      · exact a.val.property hu
      · obtain ⟨b,hb,eq⟩ := Finset.mem_map.mp hm
        have e : b = a.val := Subtype.ext eq
        exact a.property (e ▸ hb)⟩
  have right (a : T) : forward (back a) = a := Subtype.ext (Subtype.ext rfl)
  let f : G.induce X →g H.induce T := ⟨forward,fun e => e⟩
  have reach : (H.induce T).Preconnected := by
    intro a b
    have h := (connected (back a) (back b)).map f
    change (H.induce T).Reachable (forward (back a)) (forward (back b)) at h
    simpa only [right] using h
  have proper : D.card < (Finset.univ : Finset S).card := by rw [Finset.card_univ]; omega
  obtain ⟨a,_,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
  exact @SimpleGraph.Connected.mk _ (H.induce T) reach ⟨⟨a,off⟩⟩

theorem AdjacentTwins.traceable_of_minimum {u v : V} (tw : AdjacentTwins G u v)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 5 ≤ Fintype.card V)
    (common : ∀ x, G.Adj x u → G.Adj x v → 4 ≤ G.degree x) :
    Catalogue.Traceable G := by
  classical
  let S : Set V := {x | x ≠ u}
  have size : Fintype.card S = Fintype.card V - 1 := card_delete (u := u)
  exact tw.traceable_of_delete (smaller S (G.induce S) (by omega)
    (tw.connectivity_delete conn cross order common)
    ((Catalogue.treeNumber_induce_le (G := G) S).trans budget))

#print axioms AdjacentTwins.connectivity_delete
#print axioms AdjacentTwins.traceable_of_minimum

end Graffiti199Depleted
