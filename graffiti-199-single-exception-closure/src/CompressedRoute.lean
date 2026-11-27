import TerminalCompression
namespace Graffiti199Depleted.Catalogue.Anchored
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {W : Set V}

private theorem all_some {T : Type*} (L : List (Option T)) (h : none ∉ L) :
    ∃ B : List T, L = B.map some := by
  induction L with
  | nil => exact ⟨[],rfl⟩
  | cons i L ih =>
    rcases i with _|v
    · exact (h (by simp)).elim
    · obtain ⟨B,e⟩ := ih (fun m => h (List.mem_cons_of_mem _ m))
      exact ⟨v :: B,by simp [e]⟩

theorem exterior_path_of_anchored {e : Option W} (w0 : W)
    (route : Traverses (exteriorGraph G W) Set.univ none e) :
    ∃ t ∉ W, ∃ s ∈ W, G.Adj t s ∧ ∃ last, Traverses G W s last := by
  obtain ⟨P,pf,_⟩ := route
  obtain ⟨N,eq⟩ : ∃ N : List (Option W), P.vertices = none :: N := by
    rcases he : P.vertices with _|⟨i,N⟩
    · exact (P.nonempty he).elim
    · have si : some i = some (none : Option W) := by
        simpa only [he,List.head?_cons] using (show P.vertices.head? = some none from (List.head?_eq_head P.nonempty).trans (congrArg some pf))
      exact ⟨N,by rw [Option.some.inj si]⟩
  obtain ⟨B,hB⟩ := all_some N ((List.nodup_cons.mp (eq ▸ P.nodup)).1)
  subst N
  rcases B with _|⟨s,B⟩
  · have mem := (P.covers (some w0)).mpr (Set.mem_univ _)
    simp [eq] at mem
  let L := s :: B
  have ord : P.vertices = none :: L.map some := eq
  have adj := List.chain'_cons.mp (show (none :: some s :: B.map some).Chain' (exteriorGraph G W).Adj from eq ▸ P.chain)
  obtain ⟨t,tOff,ts⟩ := adj.1
  have nd : L.Nodup := (List.nodup_map_iff (Option.some_injective _)).mp (List.nodup_cons.mp (ord ▸ P.nodup)).2
  let Q : PathOn G W := ⟨L.map Subtype.val,by simp [L],(List.chain'_map _).mpr
    ((List.chain'_map (R := (exteriorGraph G W).Adj) some).mp adj.2 : L.Chain' (fun x y => G.Adj x.val y.val)),nd.map Subtype.val_injective,by
      intro v
      constructor
      · rintro h
        obtain ⟨w,_,we⟩ := List.mem_map.mp h
        exact we ▸ w.property
      · intro vw
        have mem := (P.covers (some (⟨v,vw⟩ : W))).mpr (Set.mem_univ _)
        rw [ord] at mem
        have m : (⟨v,vw⟩ : W) ∈ L := by simpa using mem
        exact List.mem_map.mpr ⟨⟨v,vw⟩,m,rfl⟩⟩
  exact ⟨t,tOff,s,s.property,ts,Q.last,Q,rfl,rfl⟩

/-- A graph part traversable to every one of its possible attachment
vertices can be lifted after a rooted traversal of the compression. -/
theorem traceable_via_exterior [Fintype V] [Fintype W]
    (conn : ConnectivityAtLeast G 3) (connW : ConnectivityAtLeast (G.induce W) 2)
    {z : V} (zOff : z ∉ W)
    (cap : ∀ I : Finset V, (∀ v ∈ I, v ∈ W) → (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → I.card ≤ 3)
    (terminal : ∀ t ∉ W, (∃ s ∈ W, G.Adj t s) → ∃ start, Traverses G Wᶜ start t) :
    Traceable G := by
  classical
  let K := exteriorGraph G W
  have three := exterior_three conn connW zOff
  obtain ⟨e,path⟩ := spanning_path_from_root (G := K) none three (by
    intro S rootOff stable
    let T := (Finset.univ : Finset W).filter (fun w => some w ∈ S)
    let f : W ↪ Option W := ⟨some,Option.some_injective _⟩
    let val : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have eq : T.map f = S := by
      ext t
      cases t with
      | none => simp [T,f,rootOff]
      | some v => simp [T,f]
    have limit := cap (T.map val) (by
      intro v hv; obtain ⟨w,_,rfl⟩ := Finset.mem_map.mp hv; exact w.property) (by
      intro u hu v hv edge
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hv
      exact stable (some i) (Finset.mem_filter.mp hi).2 (some j) (Finset.mem_filter.mp hj).2 edge)
    simpa only [← eq,Finset.card_map] using limit)
  have size := connW.1
  obtain ⟨w0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card W)
  obtain ⟨t,ht,s,hs,edge,last,R⟩ := exterior_path_of_anchored w0 path
  obtain ⟨start,L⟩ := terminal t ht ⟨s,hs,edge⟩
  obtain ⟨p,_,_⟩ := L.join R disjoint_compl_left edge
  have full : Wᶜ ∪ W = Set.univ := Set.compl_union_self _
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ p⟩)

#print axioms traceable_via_exterior
end Graffiti199Depleted.Catalogue.Anchored

