import FourShoreModel

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- A connected four-vertex side either has a spanning route between
distinct ports or is an induced claw. Hall is used to certify distinct
attachments where every endpoint pair is available. -/
theorem route_or_claw_of_four_shore
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (off : ∀ v ∈ D, v ∉ B) (boundary : ShoreBoundary G D B)
    (connected : (G.induce B).Connected) (n : Nat.card B = 4)
    (other : ∃ b : V, b ∉ B ∧ b ∉ D) :
    (∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ShoreRoute G B a b) ∨ Nonempty (ClawShore G B) := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  have cardB : Fintype.card B = 4 := by simpa only [Nat.card_eq_fintype_card] using n
  let e : Fin 4 ≃ B := (Fintype.equivFinOfCardEq cardB).symm
  let f : Fin 4 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  have fMem (i : Fin 4) : f i ∈ B := (e i).property
  have allB (v : V) (hv : v ∈ B) : ∃ i, f i = v := by
    let x : B := ⟨v,hv⟩
    exact ⟨e.symm x,congrArg Subtype.val (e.apply_symm_apply x)⟩
  let m : FourShoreModel.Mask := fun k => decide (G.Adj (f (FourShoreModel.low k)) (f (FourShoreModel.high k)))
  have chart (i j : Fin 4) : FourShoreModel.edge m i j = true ↔ G.Adj (f i) (f j) := by
    fin_cases i <;> fin_cases j <;>
      simp [FourShoreModel.edge,m,FourShoreModel.low,FourShoreModel.high,min_def,max_def] <;>
      exact G.adj_comm _ _
  have connModel : FourShoreModel.connectedCuts m := by
    intro T nonempty proper
    obtain ⟨x,hx⟩ := nonempty
    have hasOutside : ∃ y : Fin 4, y ∉ T := by
      apply Classical.byContradiction
      intro hall
      exact proper (Finset.eq_univ_iff_forall.mpr (fun v =>
        Classical.byContradiction (fun hv => hall ⟨v,hv⟩)))
    obtain ⟨y,hy⟩ := hasOutside
    obtain ⟨w⟩ := connected.preconnected (e x) (e y)
    let cut : Set B := {v | e.symm v ∈ T}
    have inX : e x ∈ cut := by simpa [cut] using hx
    have outY : e y ∉ cut := by simpa [cut] using hy
    obtain ⟨a,ha,b,hb,edge⟩ := crossingOnWalk w inX outY
    have h : G.Adj (f (e.symm a)) (f (e.symm b)) := by
      change G.Adj (e (e.symm a)).val (e (e.symm b)).val
      simpa only [Equiv.apply_symm_apply] using edge
    exact ⟨e.symm a,ha,e.symm b,hb,(chart _ _).mpr h⟩
  have path {x y : Fin 4} (ends : FourShoreModel.ends m x y) : Traverses G B (f x) (f y) := by
    obtain ⟨c,d,nd,xc,cd,dy⟩ := ends
    let L := [x,c,d,y]
    have card : L.toFinset.card = 4 := by
      rw [List.toFinset_card_of_nodup nd]
      rfl
    have univ : L.toFinset = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by rw [Finset.card_univ,card]; decide)
    let P : PathOn G B := ⟨L.map f,by simp [L],
      by simp [L,List.chain'_cons,(chart _ _).mp xc,(chart _ _).mp cd,(chart _ _).mp dy],
      nd.map f.injective,?_⟩
    · exact ⟨P,rfl,rfl⟩
    · intro v
      constructor
      · intro hv
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
        exact fMem i
      · intro hv
        obtain ⟨i,rfl⟩ := allB v hv
        have inside : i ∈ L.toFinset := univ.symm ▸ Finset.mem_univ i
        exact List.mem_map.mpr ⟨i,List.mem_toFinset.mp inside,rfl⟩
  let N (i : Fin 4) := D.filter (G.Adj (f i))
  have threshold (i : Fin 4) : 3 ≤ FourShoreModel.internalDegree m i + (N i).card := by
    let J := Finset.univ.filter (fun j : Fin 4 => FourShoreModel.edge m i j = true)
    have sub : G.neighborFinset (f i) ⊆ J.map f ∪ N i := by
      intro v hv
      have adj := (G.mem_neighborFinset _ _).mp hv
      by_cases vB : v ∈ B
      · obtain ⟨j,rfl⟩ := allB _ vB
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(chart _ _).mpr adj⟩,rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨boundary _ (fMem _) _ vB adj,adj⟩)
    have lower := degree_of_small_deletion_preconnected (G := G)
      (by have n := conn.1; omega : 4 ≤ Fintype.card V)
      (fun R hR => (conn.2 R hR).preconnected) (f i)
    have hi := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at hi
    have up := Finset.card_union_le (J.map f) (N i)
    rw [Finset.card_map] at up
    change 3 ≤ J.card + (N i).card
    omega
  have contact {i : Fin 4} {p : V} (hp : p ∈ N i) : p ∈ D ∧ G.Adj p (f i) :=
    ⟨(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2.symm⟩
  have routeOf {i j : Fin 4} (t : FourShoreModel.ends m i j) {p q : V}
      (hp : p ∈ N i) (hq : q ∈ N j) : ShoreRoute G B p q :=
    ⟨f i,f j,(contact hp).2,(contact hq).2.symm,path t⟩
  rcases FourShoreModel.connected_model_profile m connModel with hClaw|hPairs|hLeaf|hDom
  · right
    obtain ⟨c,edgeC,noLeaf⟩ := hClaw
    let J := (Finset.univ : Finset (Fin 4)).erase c
    let T := J.map f
    have count : T.card = 3 := by simp [T,J,Finset.card_erase_of_mem]
    have offCenter : f c ∉ T := by
      intro hc
      obtain ⟨i,hi,ic⟩ := Finset.mem_map.mp hc
      exact (Finset.mem_erase.mp hi).1 (f.injective ic)
    have shape : B = insert (f c) (↑T : Set V) := by
      ext v
      constructor
      · intro vB
        obtain ⟨i,rfl⟩ := allB _ vB
        by_cases eq : i = c
        · exact Or.inl (congrArg f eq)
        · exact Or.inr (Finset.mem_map.mpr ⟨i,Finset.mem_erase.mpr ⟨eq,Finset.mem_univ _⟩,rfl⟩)
      · rintro (eq|hT)
        · exact eq.symm ▸ fMem c
        · obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hT
          exact fMem i
    refine ⟨⟨f c,T,shape,count,offCenter,?_,?_⟩⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
      exact (chart _ _).mp (edgeC _ (Finset.mem_erase.mp hi).1)
    · intro x hx y hy adj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hy
      have yes := (chart _ _).mpr adj
      rw [noLeaf _ _ (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1] at yes
      contradiction
  · left
    obtain ⟨g,gm⟩ := shore_distinct_attachments conn size off boundary (by omega) other
    obtain ⟨p,hp⟩ : D.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q,hq,ne⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < D.card) p
    let pi : ↥D := ⟨p,hp⟩
    let qi : ↥D := ⟨q,hq⟩
    let x := e.symm (g pi)
    let y := e.symm (g qi)
    have xeq : f x = (g pi).val := congrArg Subtype.val (e.apply_symm_apply _)
    have yeq : f y = (g qi).val := congrArg Subtype.val (e.apply_symm_apply _)
    have xy : x ≠ y := by
      intro eq
      have eg := e.symm.injective eq
      exact ne (congrArg Subtype.val (g.injective eg).symm)
    exact ⟨p,hp,q,hq,ne.symm,f x,f y,xeq.symm ▸ gm pi,yeq.symm ▸ (gm qi).symm,path (hPairs x y xy)⟩
  · left
    obtain ⟨x,y,dx,dy,ends⟩ := hLeaf
    have tx := threshold x
    have ty := threshold y
    obtain ⟨q,hq⟩ : (N y).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p,hp,pq⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < (N x).card) q
    exact ⟨p,(contact hp).1,q,(contact hq).1,pq,routeOf ends hp hq⟩
  · left
    apply Classical.byContradiction
    intro no
    have same {x y : Fin 4} (t : FourShoreModel.ends m x y) {p q : V}
        (hp : p ∈ N x) (hq : q ∈ N y) : p = q := by
      apply Classical.byContradiction
      intro ne
      exact no ⟨p,(contact hp).1,q,(contact hq).1,ne,routeOf t hp hq⟩
    obtain ⟨x,y,dx,dy,ends,dominate⟩ := hDom
    have tx := threshold x
    have ty := threshold y
    obtain ⟨p,hp⟩ : (N x).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p',hp'⟩ : (N y).Nonempty := Finset.card_pos.mp (by omega)
    have eq := same ends hp hp'
    have forbid {z : Fin 4} {q : V} (hq : q ∈ N z) : q = p := by
      by_cases zx : z = x
      · subst z
        exact (same ends hq hp').trans eq.symm
      by_cases zy : z = y
      · subst z
        exact (same ends hp hq).symm
      rcases dominate z zx zy with fromX|fromY
      · exact (same fromX hp hq).symm
      · exact (same fromY hp' hq).symm.trans eq.symm
    obtain ⟨q,hq,qp⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < D.card) p
    obtain ⟨v,vB,edge⟩ := contact_of_shore conn (by omega) off boundary
      ⟨f x,fMem x⟩ hq
    obtain ⟨i,rfl⟩ := allB _ vB
    exact qp (forbid (Finset.mem_filter.mpr ⟨hq,edge.symm⟩))

/-- The exactly-two-component branch with a cubic-ended three-vertex path
and a component of order four closes under the minimum-order hypotheses. -/
theorem traceable_of_minimum_cubic_path_and_four_shore
    (S : ThreeVertexShore G A)
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V)
    (ind : ∀ x y, G.degree x = 3 → G.degree y = 3 → ¬ G.Adj x y)
    (size : D.card = 3) (degree : G.degree S.left = 3)
    (offA : ∀ x ∈ D, x ∉ A) (offB : ∀ x ∈ D, x ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (connected : (G.induce B).Connected) (n : Nat.card B = 4) : Traceable G := by
  have ext : ∃ x : V, x ∉ B ∧ x ∉ D :=
    ⟨S.left,Set.disjoint_left.mp apart S.left_mem,fun h => offA _ h S.left_mem⟩
  rcases route_or_claw_of_four_shore conn size offB boundB connected n ext with route|cl
  · obtain ⟨a,aD,b,bD,ab,supported⟩ := route
    exact traceable_of_minimum_cubic_path_shore_and_route S smaller conn budget order ind size offA
      offB boundA apart cover degree aD bD ab supported
  · obtain ⟨C⟩ := cl
    exact traceable_of_minimum_cubic_path_shore_and_claw S C smaller conn budget order ind size
      offA offB boundA boundB apart cover degree

#print axioms route_or_claw_of_four_shore
#print axioms traceable_of_minimum_cubic_path_and_four_shore

end Graffiti199Depleted.Catalogue
