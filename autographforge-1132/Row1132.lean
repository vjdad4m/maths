import OuterForest
import HallRainbow

namespace OuterCliques1132
open Finset SimpleGraph HallRainbow1121 AutoGraphForge370
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
/-- Vertices of D give distinct clique labels. Unmatched vertices outside D
can each be assigned an extra label. -/
private theorem cover_with_exceptions (D X : Finset V) (f : V → V)
    (hit : ∀ x ∉ D, f x ∈ D ∧ G.Adj x (f x))
    (separate : ∀ x ∉ D, x ∉ X → ∀ y ∉ D, y ∉ X → f x = f y → x = y) :
    vertexCliqueCover G ≤ D.card + X.card := by
  classical
  let S := D ∪ X
  have outside {v : V} (h : v ∉ S) : v ∉ D ∧ v ∉ X := by simpa [S] using h
  let mate (x : {v // v ∉ S}) := f x.val
  have injective : Function.Injective mate := by
    intro x y he
    exact Subtype.ext (separate x (outside x.property).1 (outside x.property).2
      y (outside y.property).1 (outside y.property).2 he)
  have cuts (x : {v // v ∉ S}) : mate x ∈ S ∧ G.Adj x.val (mate x) := by
    have hx := hit x (outside x.property).1
    exact ⟨mem_union_left _ hx.1,hx.2⟩
  exact (Nat.sInf_le (s := {r | Gᶜ.Colorable r}) (cover_of_matching G S mate injective cuts)).trans
    (card_union_le D X)

/-- A finite connected graph with a feasible outer-connected dominating set D
needs at most |D| plus its cycle rank many cliques. The additive form avoids
natural subtraction at the tree boundary. -/
theorem cover_cycle_rank [DecidableRel G.Adj] (conn : G.Connected)
    (D : Finset V) (hd : OuterDominating G D) :
    vertexCliqueCover G + Fintype.card V ≤ D.card + G.edgeFinset.card + 1 := by
  classical
  let f (x : V) := if hx : x ∉ D then (hd.1 x hx).choose else x
  have hit (x : V) (hx : x ∉ D) : f x ∈ D ∧ G.Adj x (f x) := by
    simpa [f,hx] using (hd.1 x hx).choose_spec
  let rep (y : V) := if h : ∃ x ∉ D, f x = y then h.choose else y
  have repr {x : V} (hx : x ∉ D) : rep (f x) ∉ D ∧ f (rep (f x)) = f x := by
    have ex : ∃ z ∉ D, f z = f x := ⟨x,hx,rfl⟩
    simpa only [rep,dif_pos ex] using ex.choose_spec
  let X := univ.filter (fun x => x ∉ D ∧ rep (f x) ≠ x)
  have extra {x : V} : x ∈ X ↔ x ∉ D ∧ rep (f x) ≠ x := by simp [X]
  have cover : vertexCliqueCover G ≤ D.card + X.card := by
    apply cover_with_exceptions G D X f hit
    intro x hx hx' y hy hy' eq
    have rx : rep (f x) = x := by by_contra hn; exact hx' (extra.mpr ⟨hx,hn⟩)
    have ry : rep (f y) = y := by by_contra hn; exact hy' (extra.mpr ⟨hy,hn⟩)
    exact rx.symm.trans ((congrArg rep eq).trans ry)
  let edge (x : V) : Sym2 V := s(x,f x)
  let E := X.image edge
  have sub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := mem_image.mp he
    exact (G.mem_edgeFinset).mpr (hit x (extra.mp hx).1).2
  have size : E.card = X.card := by
    apply card_image_of_injOn
    intro x hx y hy he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.1
    · exact ((extra.mp hx).1 (h.1 ▸ (hit y (extra.mp hy).1).1)).elim
  let H := G.deleteEdges (E : Set (Sym2 V))
  have inside {x y : V} (hx : x ∉ D) (hy : y ∉ D) (adj : G.Adj x y) : H.Adj x y := by
    apply deleteEdges_adj.mpr
    refine ⟨adj,?_⟩
    intro he
    obtain ⟨z,hz,eq⟩ := mem_image.mp he
    have zin := (hit z (extra.mp hz).1).1
    rcases Sym2.eq_iff.mp eq with p | p
    · exact hy (p.2 ▸ zin)
    · exact hx (p.2 ▸ zin)
  let incl : G.induce (D : Set V)ᶜ →g H :=
    ⟨Subtype.val, fun {x y} a => inside x.property y.property a⟩
  have retained {x : V} (hx : x ∉ D) : H.Adj (rep (f x)) (f x) := by
    obtain ⟨hr,fr⟩ := repr hx
    apply deleteEdges_adj.mpr
    have adjacent := (hit _ hr).2
    rw [fr] at adjacent
    refine ⟨adjacent,?_⟩
    intro he
    obtain ⟨z,hz,eq⟩ := mem_image.mp he
    rcases Sym2.eq_iff.mp eq with p | p
    · exact (extra.mp hz).2 ((congrArg rep p.2).trans p.1.symm)
    · exact (extra.mp hz).1 (p.1 ▸ (hit x hx).1)
  have detour (x : V) (hx : x ∉ D) : H.Reachable x (f x) := by
    have path := hd.2.preconnected ⟨x,hx⟩ ⟨rep (f x),(repr hx).1⟩
    exact (path.map incl).trans (retained hx).reachable
  have reroute {u v : V} (adj : G.Adj u v) : H.Reachable u v := by
    by_cases he : s(u,v) ∈ E
    · obtain ⟨x,hx,eq⟩ := mem_image.mp he
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact detour x (extra.mp hx).1
      · exact (detour x (extra.mp hx).1).symm
    · exact (show H.Adj u v from deleteEdges_adj.mpr ⟨adj,he⟩).reachable
  have connected : H.Connected := by
    rw [connected_iff]
    refine ⟨fun u v => ?_,conn.nonempty⟩
    obtain ⟨w⟩ := conn.preconnected u v
    induction w with
    | nil => exact Reachable.rfl
    | cons e _ ih => exact (reroute e).trans ih
  have vertices := connected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← H.edgeFinset_card] at vertices
  have count : H.edgeFinset.card + E.card = G.edgeFinset.card := by
    rw [show H.edgeFinset = G.edgeFinset \ E from edgeFinset_deleteEdges (G := G) E]
    exact card_sdiff_add_card_eq_card sub
  omega

theorem outer_attained {o : ℕ} (h : outerNumber G = some o) :
    ∃ D : Finset V, OuterDominating G D ∧ D.card = o := by
  classical
  unfold outerNumber at h
  split at h
  · rename_i ex
    cases h
    exact Nat.find_spec ex
  · contradiction

theorem numerical_cycle_rank [DecidableRel G.Adj] (conn : G.Connected) {o : ℕ}
    (h : outerNumber G = some o) :
    vertexCliqueCover G + Fintype.card V ≤ o + G.edgeFinset.card + 1 := by
  obtain ⟨D,hd,rfl⟩ := outer_attained G h
  exact cover_cycle_rank G conn D hd

/-- Even the order and degree hypotheses are unnecessary for the tree inequality
whenever both inputs are numeric. -/
theorem tree_bound (tree : G.IsTree) {o : ℕ} (h : outerNumber G = some o) :
    vertexCliqueCover G ≤ o := by
  classical
  have total := numerical_cycle_rank G tree.isConnected h
  have count := tree.card_edgeFinset
  omega

/-- The related untagged implication on line 5385, on its numeric domain. -/
theorem row5385 {o : ℕ} (h : outerNumber G = some o) (strict : o < vertexCliqueCover G) :
    ¬ G.IsTree :=
  fun tree => (not_lt_of_ge (tree_bound G tree h)) strict

/-- The nontrivial tree domain always supplies a numerical outer-connected optimum. -/
theorem row1132 [DecidableRel G.Adj] (order : 2 ≤ Fintype.card V)
    (_subcubic : ∀ v, G.degree v ≤ 3) (tree : G.IsTree) :
    ∃ o, outerNumber G = some o ∧ vertexCliqueCover G ≤ o := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  obtain ⟨x,y,diff⟩ := exists_pair_ne V
  have adj : ∃ u v, G.Adj u v := by
    obtain ⟨p⟩ := tree.isConnected.preconnected x y
    cases p with
    | nil => exact (diff rfl).elim
    | cons e _ => exact ⟨_,_,e⟩
  obtain ⟨o,ho⟩ := (outerNumber_defined_iff (G := G)).mpr adj
  exact ⟨o,ho,tree_bound G tree ho⟩

#print axioms cover_cycle_rank
#print axioms numerical_cycle_rank
#print axioms tree_bound
#print axioms row5385
#print axioms row1132
end OuterCliques1132
