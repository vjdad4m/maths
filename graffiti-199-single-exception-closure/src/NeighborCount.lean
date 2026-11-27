import MissingPath
import SeparatedNeighbors

namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] {X H : Set V} {z r a b : V}

structure ThreeCliques (G : SimpleGraph V) (H : Set V) where
  part : Fin 3 → Set V
  nonempty : ∀ i, (part i).Nonempty
  cover : ∀ v, v ∈ H ↔ ∃ i, v ∈ part i
  clique : ∀ i, (part i).Pairwise G.Adj
  separate : ∀ i j, i ≠ j → ∀ s ∈ part i, ∀ t ∈ part j, s ≠ t ∧ ¬ G.Adj s t

/-- If the complement of the cone has a spanning cycle and the graph
is nontraceable, the ordinary neighbor set consists of exactly three cliques. -/
theorem SingletonCut.three_cliques_of_cycle (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (hne : H.Nonempty)
    (Q : PathOn G (insert r H)ᶜ) (closes : G.Adj Q.last Q.first) (no : ¬ Traceable G) :
    Nonempty (ThreeCliques G H) := by
  classical
  let S := Hᶜ.toFinset
  let K := (DeletionGraph G S).ConnectedComponent
  letI : Fintype K := Fintype.ofFinite _
  let U (i : K) := componentShore S i
  have us (i : K) : U i ⊆ H := by
    rintro v ⟨s,_,rfl⟩; simpa [S] using s.property
  have choosePart (v : V) (vh : v ∈ H) : ∃ i : K, v ∈ U i := by
    have vs : v ∉ S := by simpa [S] using vh
    let t : Survives S := ⟨v,vs⟩
    exact ⟨(DeletionGraph G S).connectedComponentMk t,t,rfl,rfl⟩
  have non (i : K) : (U i).Nonempty := by
    obtain ⟨s⟩ := (componentShore_connected S i).nonempty; exact ⟨s.val,s.property⟩
  choose point inside using non
  let e : K ↪ V := ⟨point,fun {i j} eq => Classical.byContradiction fun ne =>
    (distinct_component_vertices ne (inside i) (inside j)).1 eq⟩
  let T := Finset.univ.map e
  have selected (x : V) (hx : x ∈ T) : ∃ i : K, point i = x := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx; exact ⟨i,rfl⟩
  have stable : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y := by
    intro x hx y hy
    obtain ⟨i,rfl⟩ := selected _ hx
    obtain ⟨j,rfl⟩ := selected _ hy
    by_cases same : i = j
    · subst j; exact G.loopless _
    · exact (distinct_component_vertices same (inside i) (inside j)).2
  have cap := F.cone_cap sub on T (fun v hv => by
    obtain ⟨i,rfl⟩ := selected v hv; exact Or.inr (us i (inside i))) stable
  have ct : T.card = Fintype.card K := by simp [T]
  have pos : 0 < Fintype.card K := by
    obtain ⟨_,h⟩ := hne; obtain ⟨i,_⟩ := choosePart _ h; exact Fintype.card_pos_iff.mpr ⟨i⟩
  by_cases one : Fintype.card K = 1
  · obtain ⟨i,all⟩ := Fintype.card_eq_one_iff.mp one
    have same : U i = H := Set.Subset.antisymm (us i) (fun _ h => by
      obtain ⟨j,jm⟩ := choosePart _ h; exact (all j) ▸ jm)
    exact (no (F.traceable_of_connected_neighbors sub on (same ▸ componentShore_connected S i) Q closes)).elim
  by_cases two : Fintype.card K = 2
  · let f := (Fintype.equivFinOfCardEq two).symm
    have ij : f 0 ≠ f 1 := f.injective.ne (by decide)
    have same : U (f 0) ∪ U (f 1) = H := Set.Subset.antisymm (Set.union_subset (us _) (us _)) (by
      intro v h
      obtain ⟨i,im⟩ := choosePart v h
      obtain ⟨k,rfl⟩ := f.surjective i
      fin_cases k
      · exact Or.inl im
      · exact Or.inr im)
    have sp : ∀ R : PathOn G (insert r (U (f 0) ∪ U (f 1)))ᶜ, G.Adj R.last R.first → Traceable G :=
      F.traceable_of_two_neighbor_parts (same.symm ▸ sub) (same.symm ▸ on) (componentShore_connected S _)
        (componentShore_connected S _) (componentShore_disjoint ij)
        (fun _ hu _ hv => (distinct_component_vertices ij hu hv).2)
    rw [same] at sp
    exact (no (sp Q closes)).elim
  have three : Fintype.card K = 3 := by omega
  let f := (Fintype.equivFinOfCardEq three).symm
  refine ⟨⟨fun i => U (f i),fun i => ⟨point (f i),inside (f i)⟩,fun v => ⟨fun h => ?_,?_⟩,?_,?_⟩⟩
  · obtain ⟨i,im⟩ := choosePart v h
    obtain ⟨k,rfl⟩ := f.surjective i
    exact ⟨k,im⟩
  · rintro ⟨i,im⟩; exact us _ im
  · intro i u hu v hv uv
    by_contra edge
    let T' := (T.erase (point (f i))) ∪ {u,v}
    have pm : point (f i) ∈ T := Finset.mem_map.mpr ⟨f i,Finset.mem_univ _,rfl⟩
    have other (w : V) (hw : w ∈ T.erase (point (f i))) :
        ∃ j : K, j ≠ f i ∧ point j = w := by
      obtain ⟨j,rfl⟩ := selected w (Finset.mem_erase.mp hw).2
      exact ⟨j,fun e => (Finset.mem_erase.mp hw).1 (congrArg point e),rfl⟩
    have apart {w s : V} (hw : w ∈ T.erase (point (f i))) (hs : s ∈ U (f i)) :
        w ≠ s ∧ ¬ G.Adj w s := by
      obtain ⟨j,ne,rfl⟩ := other w hw
      exact distinct_component_vertices ne (inside _) hs
    have d : Disjoint (T.erase (point (f i))) ({u,v} : Finset V) := Finset.disjoint_left.mpr (by
      intro w hw h; rcases (show w=u ∨ w=v by simpa using h) with e|e
      · exact (apart hw hu).1 e
      · exact (apart hw hv).1 e)
    have count : T'.card = 4 := by
      rw [Finset.card_union_of_disjoint d,Finset.card_erase_of_mem pm,ct,three,Finset.card_pair uv]
    have limit := F.cone_cap sub on T' (by
      intro w h
      rcases Finset.mem_union.mp h with t|e
      · obtain ⟨j,_,rfl⟩ := other w t; exact Or.inr (us _ (inside j))
      · rcases (show w=u ∨ w=v by simpa using e) with rfl|rfl <;> exact Or.inr (us _ (by assumption))) (by
      intro w wh t th
      rcases Finset.mem_union.mp wh with w0|w0 <;> rcases Finset.mem_union.mp th with t0|t0
      · exact stable _ (Finset.mem_erase.mp w0).2 _ (Finset.mem_erase.mp t0).2
      · rcases (show t=u ∨ t=v by simpa using t0) with rfl|rfl
        · exact (apart w0 hu).2
        · exact (apart w0 hv).2
      · rcases (show w=u ∨ w=v by simpa using w0) with rfl|rfl
        · exact fun e => (apart t0 hu).2 e.symm
        · exact fun e => (apart t0 hv).2 e.symm
      · simp only [Finset.mem_insert,Finset.mem_singleton] at w0 t0
        rcases w0 with w1|w1 <;> rcases t0 with t1|t1 <;> rw [w1,t1]
        · exact G.loopless _
        · exact edge
        · exact fun e => edge e.symm
        · exact G.loopless _)
    omega
  · intro i j ij s hs t ht
    exact distinct_component_vertices (f.injective.ne ij) hs ht

#print axioms SingletonCut.three_cliques_of_cycle
end Graffiti199Depleted.Catalogue.Incomplete

