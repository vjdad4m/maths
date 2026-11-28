import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Alternate peripheral vertices with a clique, leaving the requested
clique vertex as the last vertex. No adjacency within the peripheral set is required. -/
theorem route_clique_join_end_hub {H L : Finset V} {x : V}
    (dis : Disjoint H L) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ l∈L,G.Adj h l) (cap : L.card<H.card) (xh : x∈H) :
    ∃ z∈H,RouteOn G (H∪L) z x := by
  classical
  have main : ∀ n : ℕ,∀ H L : Finset V, L.card=n →
      ∀ x∈H, Disjoint H L → CompleteOn G H →
      (∀ h∈H,∀ l∈L,G.Adj h l) → L.card<H.card →
      ∃ z∈H,RouteOn G (H∪L) z x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H L nl x xh dis cl cross cap
      by_cases ne : L.Nonempty
      · obtain ⟨y,yl⟩ := ne
        have hp : 0<L.card := card_pos.mpr ⟨y,yl⟩
        have hm : 0<(H.erase x).card := by rw [card_erase_of_mem xh]; omega
        obtain ⟨u,uu⟩ := card_pos.mp hm
        obtain ⟨ux,uh⟩ := mem_erase.mp uu
        let H' := H.erase u
        let L' := L.erase y
        have hsub : H'⊆H := erase_subset _ _
        have lsub : L'⊆L := erase_subset _ _
        have xh' : x∈H' := mem_erase.mpr ⟨ux.symm,xh⟩
        have shr : L'.card<n := by
          change (L.erase y).card<n
          rw [card_erase_of_mem yl]
          omega
        have c' : L'.card<H'.card := by
          change (L.erase y).card<(H.erase u).card
          rw [card_erase_of_mem yl,card_erase_of_mem uh]
          omega
        obtain ⟨z,zh,p⟩ := ih L'.card shr H' L' rfl x xh' (dis.mono hsub lsub)
          (fun a ah b bh ab=>cl a (hsub ah) b (hsub bh) ab)
          (fun a ah b bh=>cross a (hsub ah) b (lsub bh)) c'
        have ny : y∉H'∪L' := by
          intro m
          rcases mem_union.mp m with yh|yl'
          · exact disjoint_left.mp dis (hsub yh) yl
          exact (mem_erase.mp yl').1 rfl
        have nu : u∉insert y (H'∪L') := by
          intro m
          rcases mem_insert.mp m with eq|m
          · exact disjoint_left.mp dis uh (eq.symm ▸ yl)
          rcases mem_union.mp m with uu|ul
          · exact (mem_erase.mp uu).1 rfl
          exact disjoint_left.mp dis uh (lsub ul)
        have q := (p.prefix (cross z (hsub zh) y yl).symm ny).prefix (cross u uh y yl) nu
        have shape : insert u (insert y (H'∪L'))=H∪L := by
          ext v
          by_cases hu : v=u
          · subst v
            simp [uh]
          by_cases hy : v=y
          · subst v
            simp [yl]
          simp [H',L',hu,hy]
        exact ⟨u,uh,shape ▸ q⟩
      have z : L=∅ := Finset.eq_empty_iff_forall_not_mem.mpr (fun y yl=>ne ⟨y,yl⟩)
      obtain ⟨u,p,pp,ps⟩ := rooted_path_in_clique H cl xh
      have q : RouteOn G H x u := ⟨p,pp,ps⟩
      exact ⟨u,(ps u).mp p.end_mem_support,by simpa [z] using q.reverse⟩
  exact main L.card H L rfl x xh dis cl cross cap

/-- With at most as many peripheral vertices as clique vertices, a chosen
peripheral vertex may be the last one, with a chosen incoming clique edge. -/
theorem route_clique_join_end_leaf {H L : Finset V} {x y : V}
    (dis : Disjoint H L) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ l∈L.erase y,G.Adj h l) (cap : L.card≤H.card) (xh : x∈H)
    (yl : y∈L) (xy : G.Adj x y) : ∃ z∈H,RouteOn G (H∪L) z y := by
  classical
  have ls : L.erase y⊆L := erase_subset _ _
  have cap' : (L.erase y).card<H.card := by
    rw [card_erase_of_mem yl]
    have pos := card_pos.mpr ⟨y,yl⟩
    omega
  obtain ⟨z,zh,q⟩ := route_clique_join_end_hub (dis.mono (Subset.refl H) ls) cl cross cap' xh
  have ny : y∉H∪L.erase y := fun m=>(mem_union.mp m).elim
    (fun yh=>disjoint_left.mp dis yh yl) (fun ye=>(mem_erase.mp ye).1 rfl)
  have p := q.suffix xy ny
  have shape : insert y (H∪L.erase y)=H∪L := by
    ext v
    by_cases hy : v=y
    · subst v
      simp [yl]
    simp [hy]
  exact ⟨z,zh,shape ▸ p⟩

#print axioms route_clique_join_end_hub
#print axioms route_clique_join_end_leaf
end Graffiti189LongestPath.CrossSaturation
