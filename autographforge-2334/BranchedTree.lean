import OuterForest
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Ján Pastorek's AutoGraphForge normalized row 2334, ID 37af8e28.
Two central vertices each have two support neighbors. Each support has two leaves. -/

namespace AutoGraphForge2334

open SimpleGraph AutoGraphForge370

abbrev V := Fin 14

def parent : V → V := ![0,0,0,0,1,1,2,2,3,3,4,4,5,5]

def relation (x y : V) : Prop := (x < y ∧ parent y = x) ∨ (y < x ∧ parent x = y)

def tree : SimpleGraph V where
  Adj := relation
  symm _ _ h := h.symm
  loopless x := by simp [relation]

instance : DecidableRel tree.Adj := fun x y =>
  inferInstanceAs (Decidable ((x < y ∧ parent y = x) ∨ (y < x ∧ parent x = y)))

/-- In any cycle, its largest vertex has two distinct smaller neighbors.
This is impossible when each vertex has at most one downward edge. -/
theorem acyclic_of_unique_lower {W : Type*} [Fintype W] [LinearOrder W]
    {G : SimpleGraph W} (h : ∀ ⦃v a b⦄, G.Adj v a → G.Adj v b → a < v → b < v → a = b) :
    G.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨z,hz,hmax⟩ := p.support.toFinset.exists_max_image id
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have htwo := hp.ncard_neighborSet_toSubgraph_eq_two (List.mem_toFinset.mp hz)
  obtain ⟨x,hx,y,hy,hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (by omega :
    1 < (p.toSubgraph.neighborSet z).ncard)
  have lower (a : W) (ha : p.toSubgraph.Adj z a) : a < z :=
    lt_of_le_of_ne (hmax a (List.mem_toFinset.mpr
      (Walk.mem_support_of_adj_toSubgraph ha.symm))) ha.adj_sub.ne.symm
  exact hne (h hx.adj_sub hy.adj_sub (lower x hx) (lower y hy))

theorem acyclic : tree.IsAcyclic := by
  apply acyclic_of_unique_lower
  intro v a b hva hvb hav hbv
  change relation v a at hva
  change relation v b at hvb
  rcases hva with ⟨hva, _⟩ | ⟨_, ha⟩
  · exact False.elim (not_lt_of_gt hav hva)
  rcases hvb with ⟨hvb, _⟩ | ⟨_, hb⟩
  · exact False.elim (not_lt_of_gt hbv hvb)
  exact ha.symm.trans hb

theorem chordal : Chordal tree := by
  intro v p hp
  exact False.elim (acyclic p hp)

theorem subcubic : ∀ x, tree.degree x ≤ 3 := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide

def chosen : Finset V := {0,6,7,8,9,10,11,12,13}

theorem indep_lower : 9 ≤ tree.indepNum := by
  have hi : tree.IsIndepSet chosen := by decide
  have hn : chosen.card = 9 := by decide
  exact hn ▸ hi.card_le_indepNum

def step (x : V) : V := if x ≤ 1 then x else parent x

private theorem shortStep {x y : V} (h : x = y ∨ tree.Adj x y) :
    ∃ w : tree.Walk x y, w.length ≤ 1 := by
  rcases h with rfl | e
  · exact ⟨Walk.nil, by simp⟩
  · exact ⟨Walk.cons e Walk.nil, by simp⟩

theorem toCenter (x : V) : ∃ p : tree.Walk x (step (step x)), p.length ≤ 2 := by
  have step_ok : ∀ a : V, a = step a ∨ tree.Adj a (step a) := by decide
  obtain ⟨p,hp⟩ := shortStep (step_ok x)
  obtain ⟨q,hq⟩ := shortStep (step_ok (step x))
  exact ⟨p.append q, by rw [Walk.length_append]; omega⟩

theorem shortWalk (x y : V) : ∃ w : tree.Walk x y, w.length ≤ 5 := by
  have centers : ∀ a b : V, step (step a) = step (step b) ∨
      tree.Adj (step (step a)) (step (step b)) := by decide
  obtain ⟨p,hp⟩ := toCenter x
  obtain ⟨q,hq⟩ := shortStep (centers x y)
  obtain ⟨r,hr⟩ := toCenter y
  exact ⟨(p.append q).append r.reverse, by simp only [Walk.length_append, Walk.length_reverse]; omega⟩

theorem connected : tree.Connected :=
  ⟨fun x y => (shortWalk x y).choose.reachable⟩

/-- The distinct-triple definition used in the published row 764 certificate. -/
noncomputable def triameter {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) : ℕ :=
  Finset.univ.sup fun a => (Finset.univ.erase a).sup fun b =>
    ((Finset.univ.erase a).erase b).sup fun c => G.dist a b + G.dist b c + G.dist c a

theorem tri_upper : triameter tree ≤ 15 := by
  have bound (a b : V) : tree.dist a b ≤ 5 := by
    obtain ⟨w,hw⟩ := shortWalk a b
    exact (dist_le w).trans hw
  simp only [triameter, Finset.sup_le_iff]
  intro a _ b _ c _
  have := bound a b
  have := bound b c
  have := bound c a
  omega

theorem counterexample :
    ∃ (G : SimpleGraph V) (k : ℕ), 2 ≤ Fintype.card V ∧ G.Connected ∧ Chordal G ∧
      (∀ x, (G.neighborSet x).ncard ≤ 3) ∧ outerNumber G = some k ∧
      ((triameter G : ℚ) / 2 + 1 < k) := by
  classical
  have hasEdge : tree.Adj 0 1 := by decide
  obtain ⟨k,hk⟩ := (outerNumber_defined_iff (G := tree)).mpr ⟨0,1,hasEdge⟩
  have lower : 9 ≤ k := by
    apply indep_lower.trans
    unfold outerNumber at hk
    split at hk
    · rename_i h
      cases hk
      obtain ⟨D,hd,he⟩ := Nat.find_spec h
      exact he ▸ forest_indep_le_outer_card acyclic D hd
    · contradiction
  refine ⟨tree,k,by decide,connected,chordal,(fun x => ?_),hk,?_⟩
  · rw [Set.ncard_eq_toFinset_card']
    exact subcubic x
  have upper : (triameter tree : ℚ) ≤ 15 := by exact_mod_cast tri_upper
  have klow : (9 : ℚ) ≤ k := by exact_mod_cast lower
  linarith

#print axioms acyclic_of_unique_lower
#print axioms tri_upper
#print axioms counterexample

end AutoGraphForge2334
