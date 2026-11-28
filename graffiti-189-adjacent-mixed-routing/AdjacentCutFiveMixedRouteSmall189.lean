import AdjacentCutFiveComponents189
import DegreeFiveSmallSides189
import RootedOreTwoRootsNonedge189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Vis vis_card_ge_two from AdjacentCutFiveComponents189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem inside_lower_of_boundary (S B : Finset V) {u : V}
    (bound : ∀ w, G.Adj u w → w∈S ∨ w∈B) :
    G.degree u≤(inside G S u).card+B.card := by
  classical
  have sub : G.neighborFinset u ⊆ inside G S u ∪ B := by
    intro w wm
    have e := (mem_neighborFinset G u w).mp wm
    rcases bound w e with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨h,e⟩)
    · exact mem_union_right _ h
  have h := (card_le_card sub).trans (card_union_le (inside G S u) B)
  rwa [card_neighborFinset_eq_degree] at h

private theorem rooted_side (S : Finset V) (R high : V→Prop)
    (conn : (G.induce (↑S : Set V)).Connected)
    (roots : ∃ x∈S,∃ y∈S,x≠y ∧ R x ∧ R y)
    (degree : ∀ u∈S, ∀ v∈S,u≠v → high u ∨ high v)
    (ore : ∀ u∈S, ∀ v∈S,u≠v → ¬G.Adj u v → high u → high v →
      S.card≤(inside G S u).card+(inside G S v).card) :
    ∃ s t, R s ∧ RouteOn G S s t := by
  classical
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : Finset U := univ.filter (fun u=>R u.val)
  obtain ⟨x,hx,y,hy,xy,rx,ry⟩ := roots
  have rk : 2≤K.card := one_lt_card.mpr
    ⟨⟨x,hx⟩,mem_filter.mpr ⟨mem_univ _,rx⟩,⟨y,hy⟩,mem_filter.mpr ⟨mem_univ _,ry⟩,
      fun e=>xy (congrArg Subtype.val e)⟩
  have pair (u v : U) (hu : high u.val) (hv : high v.val) (n : u≠v) (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have sc : Fintype.card U=S.card := Fintype.card_coe S
    rw [sc,←inside_card_eq_degree_induce (G:=G) S u,←inside_card_eq_degree_induce (G:=G) S v]
    exact ore u.val u.property v.val v.property (fun e=>n (Subtype.ext e)) no hu hv
  obtain ⟨r,rK,t,p,pp,ps⟩ := rooted_Ore_with_two_roots_of_nonedge conn K rk
    (fun u=>high u.val) (fun u v e=>degree u.val u.property v.val v.property (fun h=>e (Subtype.ext h))) pair
  exact ⟨r.val,t.val,(mem_filter.mp rK).2,lift_side_path S p pp ps⟩

private theorem conn_insert_of_edge (S : Finset V) {x w : V}
    (h : (G.induce (↑S : Set V)).Connected) (wm : w∈S) (edge : G.Adj x w) :
    (G.induce (↑(insert x S) : Set V)).Connected := by
  let W : Set V := ↑(insert x S)
  let w' : W := ⟨w,mem_insert_of_mem wm⟩
  have reach (u : W) : (G.induce W).Reachable u w' := by
    rcases mem_insert.mp u.property with e|e
    · apply Adj.reachable
      change G.Adj u.val w
      rwa [e]
    · obtain ⟨p⟩ := h.preconnected ⟨u.val,e⟩ ⟨w,wm⟩
      have incl : (↑S : Set V) ≤ W := fun _ v=>mem_insert_of_mem v
      exact (p.map (G.induceHomOfLE incl).toHom).reachable
  letI : Nonempty W := ⟨w'⟩
  exact SimpleGraph.Connected.mk (fun u v=>(reach u).trans (reach v).symm)

/-- A small shore can enter either terminal, and an all-high shore of order at most
seven can absorb the other terminal. No even-distance or twin hypothesis is used. -/
theorem traceable_of_mixed_adjacent_small_high_shores (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (cmin : 2≤(Shore C).card) (cmax : (Shore C).card≤6)
    (dmax : (Shore D).card≤7) (dhigh : ∀ z∈Shore D,5≤G.degree z) :
    ∃ s t, ∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have cdeg {u : V} (uc : u∈Shore C) :
      G.degree u≤(inside G (Shore C) u).card+2 := by
    have q := inside_lower_of_boundary (G:=G) (Shore C) {a,b} (u:=u)
      (fun w uw=>by
        rcases shore_closed C u uc w uw with rfl|rfl|h
        · exact .inr (by simp)
        · exact .inr (by simp)
        · exact .inl h)
    simpa [ab.ne] using q
  obtain ⟨v,hv,w,hw,vw⟩ := one_lt_card.mp (vis_card_ge_two ab.ne conn C cmin)
  obtain ⟨s,t,port,p⟩ := rooted_side (Shore C) (fun z=>G.Adj a z ∨ G.Adj b z)
    (fun z=>5≤G.degree z) (shore_connected C)
    ⟨v,(mem_filter.mp hv).1,w,(mem_filter.mp hw).1,vw,(mem_filter.mp hv).2,(mem_filter.mp hw).2⟩
    (fun u _ v _ uv=>degree u v uv) (by
      intro u uc v vc _ _ hu hv
      have du := cdeg uc
      have dv := cdeg vc
      omega)
  obtain ⟨wa,waD,awa⟩ := shore_hit_a ab.ne conn D
  obtain ⟨wb,wbD,bwb⟩ := shore_hit_b ab.ne conn D
  have run {x y k l : V} (xy : G.Adj x y)
      (xC : x∉Shore C) (xD : x∉Shore D) (yC : y∉Shore C) (yD : y∉Shore D)
      (ends : ∀ {z : V}, z≠x → z≠y → z∈Shore C ∨ z∈Shore D)
      (bd : ∀ u∈Shore D, ∀ z, G.Adj u z → z=x ∨ z=y ∨ z∈Shore D)
      (kD : k∈Shore D) (lD : l∈Shore D) (xk : G.Adj x k) (yl : G.Adj y l)
      (ys : G.Adj y s) :
      ∃ u v,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
    let S := insert x (Shore D)
    have sz : S.card≤8 := (card_insert_le _ _).trans (by omega)
    have deg' (u : V) (um : u∈Shore D) :
        G.degree u≤(inside G S u).card+1 := by
      have q := inside_lower_of_boundary (G:=G) S {y} (u:=u) (fun z uz=>by
        rcases bd u um z uz with rfl|rfl|h
        · exact .inl (mem_insert_self _ _)
        · exact .inr (mem_singleton_self _)
        · exact .inl (mem_insert_of_mem h))
      simpa using q
    obtain ⟨r,u,yr,q⟩ := rooted_side S (G.Adj y) (fun z=>z∈Shore D)
      (conn_insert_of_edge (Shore D) (shore_connected D) kD xk)
      ⟨x,mem_insert_self _ _,l,mem_insert_of_mem lD,fun e=>xD (e.symm ▸ lD),xy.symm,yl⟩
      (by
        intro u um v vm ne
        rcases mem_insert.mp um with rfl|h
        · exact .inr ((mem_insert.mp vm).resolve_left ne.symm)
        · exact .inl h)
      (by
        intro u _ v _ _ _ hu hv
        have p := deg' u hu
        have q := deg' v hv
        have a := dhigh u hu
        have b := dhigh v hv
        omega)
    have apart : Disjoint (insert y (Shore C)) S := by
      apply disjoint_left.mpr
      intro z zc zd
      rcases mem_insert.mp zc with rfl|h
      · exact (mem_insert.mp zd).elim xy.ne.symm yD
      rcases mem_insert.mp zd with rfl|j
      · exact xC h
      · exact disjoint_left.mp (shore_disjoint cd) h j
    obtain ⟨w,wp,ws⟩ := (p.reverse.suffix ys.symm yC).join q apart yr
    refine ⟨t,u,w,wp,fun z=>(ws z).mpr ?_⟩
    by_cases e : z=x
    · simp [e,S]
    by_cases f : z=y
    · simp [f]
    rcases ends e f with h|h <;> simp [S,h]
  rcases port with h|h
  · exact run ab.symm (shore_off C).2 (shore_off D).2 (shore_off C).1 (shore_off D).1
      (fun zb za=>cover za zb) (fun u um z uz=>by simpa only [or_left_comm] using shore_closed D u um z uz)
      wbD waD bwb awa h
  · exact run ab (shore_off C).1 (shore_off D).1 (shore_off C).2 (shore_off D).2
      cover (shore_closed D) waD wbD awa bwb h

#print axioms traceable_of_mixed_adjacent_small_high_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
