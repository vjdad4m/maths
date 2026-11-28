import AdjacentCutFiveThreeSingleton189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_disjoint from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Any walk from one side to the opposite side has to pass through the
two cut vertices, so its length is at least the better of the two metric
detours through them. -/
theorem cross_metric {a b x y : V} (L : Finset V)
    (hc : G.Connected) (xl : x∈L) (yo : y∉L)
    (boundary : ∀ u∈L, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈L) :
    G.dist x y = min (G.dist x a+G.dist a y) (G.dist x b+G.dist b y) := by
  have lower' {u w : V} (p : G.Walk u w) (ul : u∈L) (wo : w∉L) :
      min (G.dist x a+G.dist a w) (G.dist x b+G.dist b w) ≤
        G.dist x u + p.length := by
    induction p with
    | nil => exact (wo ul).elim
    | @cons u v w uv q ih =>
        have tri := hc.dist_triangle (u:=x) (v:=u) (w:=v)
        rw [dist_eq_one_iff_adj.mpr uv] at tri
        simp only [Walk.length_cons]
        rcases boundary u ul v uv with va|vb|vl
        · subst v
          have n := Nat.min_le_left (G.dist x a+G.dist a w) (G.dist x b+G.dist b w)
          have ql := G.dist_le q
          omega
        · subst v
          have n := Nat.min_le_right (G.dist x a+G.dist a w) (G.dist x b+G.dist b w)
          have ql := G.dist_le q
          omega
        · have h := ih vl wo
          omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x y
  have lo := lower' p xl yo
  rw [SimpleGraph.dist_self,zero_add,pl] at lo
  exact Nat.le_antisymm (le_min (hc.dist_triangle (u:=x) (v:=a) (w:=y))
    (hc.dist_triangle (u:=x) (v:=b) (w:=y))) lo

noncomputable def depth (G : SimpleGraph V) (a b x : V) : ℕ :=
  min (G.dist a x) (G.dist b x)

theorem depth_step (hc : G.Connected) {x y : V} (xy : G.Adj x y) :
    depth G a b x ≤ depth G a b y + 1 := by
  have ax := hc.dist_triangle (u:=a) (v:=y) (w:=x)
  have bx := hc.dist_triangle (u:=b) (v:=y) (w:=x)
  have d := dist_eq_one_iff_adj.mpr xy.symm
  unfold depth
  omega

private theorem depth_a : depth G a b a = 0 := by simp [depth, SimpleGraph.dist_self]

private theorem walk_cannot_cross_depth {W : Set V} (hc : G.Connected) {z t : W}
    (q : (G.induce W).Walk z t) (k : ℕ)
    (avoid : ∀ x : W, depth G a b x.val ≠ k)
    (deep : k < depth G a b z.val) :
    k < depth G a b t.val := by
  induction q with
  | nil => exact deep
  | @cons x y z xy q ih =>
    have edge : G.Adj x.val y.val := xy
    have le := depth_step (a:=a) (b:=b) hc edge
    exact ih (by have no := avoid y; omega)

/-- If a vertex is strictly deeper than a layer, that layer has at
least two vertices in a graph connected after every singleton deletion.
This holds for any choice of distinct terminals (in fact distinctness
isn't needed). -/
theorem two_vertices_in_intermediate_depth (hc : G.Connected)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {x : V} {k : ℕ} (k0 : 0 < k) (deep : k < depth G a b x) :
    ∃ u v : V, u ≠ v ∧ depth G a b u = k ∧ depth G a b v = k := by
  classical
  have layer : ∃ u : V, depth G a b u = k := by
    by_contra! no
    obtain ⟨q⟩ := hc.preconnected x a
    let f : G →g G.induce (Set.univ : Set V) := ⟨fun v=>⟨v, trivial⟩, fun h=>h⟩
    have aDeep : k < depth G a b a :=
      walk_cannot_cross_depth hc (q.map f) k (fun z=>no z.val) deep
    rw [depth_a] at aDeep
    omega
  obtain ⟨u,uk⟩ := layer
  have neX : x ≠ u := by intro h; rw [h,uk] at deep; omega
  have neA : a ≠ u := by intro h; rw [← h,depth_a] at uk; omega
  let W : Set V := (↑({u} : Finset V) : Set V)ᶜ
  let xx : W := ⟨x,by simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using neX⟩
  let aa : W := ⟨a,by simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using neA⟩
  have another : ∃ v : W, depth G a b v.val = k := by
    by_contra! no
    obtain ⟨q⟩ := (conn {u} (by simp)).preconnected xx aa
    have aDeep : k < depth G a b a := walk_cannot_cross_depth hc q k no deep
    rw [depth_a] at aDeep
    omega
  obtain ⟨v,vk⟩ := another
  have neV : v.val ≠ u := by
    simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using v.property
  exact ⟨u,v.val,neV.symm,uk,vk⟩

#print axioms two_vertices_in_intermediate_depth
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
