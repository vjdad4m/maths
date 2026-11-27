import Core180
import Mathlib.Data.Finset.Sum

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

noncomputable def pull (f : V → W) (S : Finset W) : Finset V := by
  classical exact univ.filter (fun v => f v ∈ S)

omit [Fintype W] [DecidableEq V] in
@[simp] theorem mem_pull {f : V → W} {S : Finset W} {v : V} :
    v ∈ pull f S ↔ f v ∈ S := by classical simp [pull]

theorem split_card (S : Finset (V ⊕ W)) :
    S.card = (pull Sum.inl S).card + (pull Sum.inr S).card := by
  classical
  have e : (pull Sum.inl S).disjSum (pull Sum.inr S) = S := by
    ext v; cases v <;> simp
  rw [← card_disjSum,e]

omit [Fintype W] in
theorem restrict_color (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (inj : Function.Injective f) (map : ∀ {x y}, G.Adj x y → H.Adj (f x) (f y))
    {S : Finset W} (h : TwoColor H S) : TwoColor G (pull f S) := by
  obtain ⟨A,B,dis,eq,ai,bi⟩ := h
  have ind (Z : Finset W) (hz : Indep H Z) : Indep G (pull f Z) := by
    intro a ha b hb ne e
    exact hz _ (mem_pull.mp ha) _ (mem_pull.mp hb) (fun h => ne (inj h)) (map e)
  refine ⟨pull f A,pull f B,Finset.disjoint_left.mpr (fun _ a b =>
    Finset.disjoint_left.mp dis (mem_pull.mp a) (mem_pull.mp b)),?_,ind A ai,ind B bi⟩
  rw [← eq]
  ext v
  simp

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem walk_project (T : SimpleGraph W) (f : V → W) (g : W → V)
    (step : ∀ {u v}, T.Adj u v → g u = g v ∨ T.Adj (f (g u)) (f (g v)))
    {u v : W} (w : T.Walk u v) : (T.comap f).Reachable (g u) (g v) := by
  induction w with
  | nil => exact Reachable.refl _
  | cons e _ ih =>
    rcases step e with h|h
    · exact h ▸ ih
    · exact (show (T.comap f).Adj _ _ from h).reachable.trans ih

/- Dead-end excursions collapse under the projection, leaving a connected
spanning subgraph of the original piece in every ambient spanning tree. -/
omit [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem tree_inside (G : SimpleGraph V) (T : SimpleGraph W) (tc : T.Connected)
    (f : V → W) (g : W → V) (left : Function.LeftInverse g f)
    (step : ∀ {u v}, T.Adj u v → g u = g v ∨ T.Adj (f (g u)) (f (g v)))
    (sub : ∀ {u v}, T.Adj (f u) (f v) → G.Adj u v) :
    ∃ K ≤ G, K.IsTree ∧ ∀ {u v}, K.Adj u v → T.Adj (f u) (f v) := by
  have h : (T.comap f).Connected := by
    letI : Nonempty V := ⟨g (Classical.choice tc.nonempty)⟩
    refine ⟨fun u v => ?_⟩
    obtain ⟨w⟩ := tc (f u) (f v)
    have e := walk_project T f g step w
    rwa [left u,left v] at e
  obtain ⟨K,ks,kt⟩ := h.exists_isTree_le
  exact ⟨K,fun _ _ e => sub (ks e),kt,fun {_ _} e => ks e⟩

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
theorem leaf_unique (T : SimpleGraph W) {v u w : W} (leaf : v ∈ leaves T)
    (e : T.Adj v u) (h : T.Adj v w) : u = w := by
  classical
  have one : (T.neighborFinset v).card = 1 := by
    rw [card_neighborFinset_eq_degree]
    exact (mem_filter.mp leaf).2
  obtain ⟨j,eq⟩ := card_eq_one.mp one
  have a := (T.mem_neighborFinset v u).mpr e
  have b := (T.mem_neighborFinset v w).mpr h
  rw [eq,mem_singleton] at a b
  exact a.trans b.symm

theorem piece_leaves (G : SimpleGraph V) (hn : 1 < Fintype.card V)
    (T : SimpleGraph W) (f : V → W) (inj : Function.Injective f)
    {K : SimpleGraph V} (ks : K ≤ G) (kt : K.IsTree)
    (map : ∀ {u v}, K.Adj u v → T.Adj (f u) (f v))
    (U B : Finset V)
    (exclude : ∀ v ∈ B, v ∉ U → ∃ w, T.Adj (f v) w ∧ ∀ u, w ≠ f u) :
    (B ∩ pull f (leaves T)).card ≤ weightedLeaves G U := by
  classical
  apply (show (B ∩ pull f (leaves T)).card ≤ (U ∩ leaves K).card from card_le_card ?_).trans
    (le_sup (f := fun J => (U ∩ leaves J).card) (mem_filter.mpr ⟨mem_univ _,ks,kt⟩))
  intro v hv
  obtain ⟨bv,lv⟩ := mem_inter.mp hv
  have l := mem_pull.mp lv
  obtain ⟨u,e⟩ := exists_adj K kt.isConnected hn v
  have eq (w) (a : K.Adj v w) : w = u := inj (leaf_unique T l (map a) (map e))
  refine mem_inter.mpr ⟨?_,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  · by_contra out
    obtain ⟨w,edge,ne⟩ := exclude v bv out
    exact ne u (leaf_unique T l edge (map e))
  · have sing : K.neighborFinset v = {u} := by
      ext w
      simp only [mem_neighborFinset,mem_singleton]
      exact ⟨eq w,fun h => h ▸ e⟩
    rw [← card_neighborFinset_eq_degree,sing,card_singleton]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem forced_edge (T : SimpleGraph W) (tc : T.Connected) (u v : W) (side : W → Prop)
    (su : side u) (sv : ¬ side v)
    (only : ∀ {a b}, T.Adj a b → side a → ¬ side b → a = u ∧ b = v) : T.Adj u v := by
  have cross {a b : W} (w : T.Walk a b) : side a → ¬side b → T.Adj u v := by
    induction w with
    | nil => exact fun h hn => (hn h).elim
    | @cons a c b e _ ih =>
      intro h hn
      by_cases k : side c
      · exact ih k hn
      · obtain ⟨eq1,eq2⟩ := only e h k
        simpa only [← eq1,← eq2] using e
  obtain ⟨w⟩ := tc u v
  exact cross w su sv

/- Characterization of distance by a 1-Lipschitz layer labeling with a
descending neighbor at every nonroot vertex. Also proves connectedness. -/
omit [Fintype V] [DecidableEq V] in
theorem layers (G : SimpleGraph V) (r : V) (d : V → ℕ) (z : d r = 0)
    (lip : ∀ {v w}, G.Adj v w → d v ≤ d w + 1)
    (down : ∀ v, v ≠ r → ∃ w, G.Adj v w ∧ d v = d w + 1) :
    G.Connected ∧ ∀ v, G.dist v r = d v := by
  have path (v) : ∃ p : G.Walk v r, p.length = d v := by
    induction k : d v using Nat.strong_induction_on generalizing v with
    | h k ih =>
      by_cases eq : v = r
      · subst v
        exact ⟨.nil,by simp only [Walk.length_nil]; omega⟩
      · obtain ⟨w,edge,dist⟩ := down v eq
        obtain ⟨p,pe⟩ := ih (d w) (by omega) w rfl
        exact ⟨p.cons edge,by simp only [Walk.length_cons,pe]; omega⟩
  have hc : G.Connected := (connected_iff_exists_forall_reachable _).mpr
    ⟨r,fun v => (Reachable.symm ⟨(path v).choose⟩)⟩
  refine ⟨hc,fun v => ?_⟩
  have lower {x y : V} (p : G.Walk x y) : d x ≤ d y + p.length := by
    induction p with
    | nil => simp
    | cons e _ ih => have := lip e; simp only [Walk.length_cons]; omega
  obtain ⟨p,pe⟩ := hc.exists_walk_length_eq_dist v r
  have a := lower p
  obtain ⟨q,qe⟩ := path v
  have b := G.dist_le q
  omega

#print axioms piece_leaves
#print axioms layers
end Converse180
