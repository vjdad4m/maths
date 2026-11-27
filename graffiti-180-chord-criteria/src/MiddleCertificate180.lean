import PathMaximum180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem score_of_tree (G T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) (U : Finset V) :
    (U∩leaves T).card≤weightedLeaves G U := by
  classical
  exact le_sup (f:=fun F => (U∩leaves F).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)

/-- Removing prescribed leaves from a nontrivial tree leaves the remaining
vertices connected. This cut form suffices to certify upper leaf bounds. -/
theorem leaf_cut_constant (G T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) (hn : 2<Fintype.card V)
    (X : Finset V) (lf : X⊆leaves T) (color : V→Bool)
    (keep : ∀ a∉X, ∀ b∉X, G.Adj a b → color a=color b) :
    ∀ a∉X, ∀ b∉X, color a=color b := by
  classical
  let q (v : V) := (exists_adj T tr.isConnected (by omega : 1<Fintype.card V) v).choose
  have edge (v : V) : T.Adj v (q v) := (exists_adj T tr.isConnected (by omega : 1<Fintype.card V) v).choose_spec
  let f (v : V) := if v∈X then q v else v
  have step {v w : V} (e : T.Adj v w) : color (f v)=color (f w) := by
    by_cases vx : v∈X
    · have ow : w∉X := fun h => leaves_nonadjacent T tr hn e (lf vx) (lf h)
      simp [f,vx,ow,leaf_unique T (lf vx) (edge v) e]
    by_cases wx : w∈X
    · simp [f,vx,wx,leaf_unique T (lf wx) (edge w) e.symm]
    · simpa [f,vx,wx] using keep v vx w wx (sub e)
  intro a ha b hb
  obtain ⟨walk⟩ := tr.isConnected a b
  have all {i j : V} (p : T.Walk i j) : color (f i)=color (f j) := by
    induction p with
    | nil => rfl
    | cons e _ ih => exact (step e).trans ih
  simpa [f,ha,hb] using all walk

omit [Fintype V] in
private theorem monochrome (G : SimpleGraph V) (S : Finset V) (h : TwoColor G S) :
    ∃ C : Finset V, ∀ x∈S, ∀ y∈S, G.Adj x y → (x∈C ↔ y∉C) := by
  obtain ⟨C,D,dis,rfl,ci,di⟩ := h
  refine ⟨C,?_⟩
  intro x hx y hy e
  constructor
  · exact fun xc yc => ci x xc y yc e.ne e
  · intro yc
    by_contra xc
    exact di x ((mem_union.mp hx).resolve_left xc) y ((mem_union.mp hy).resolve_left yc) e.ne e

omit [Fintype V] in
theorem triangle_excluded (G : SimpleGraph V) (S : Finset V) (h : TwoColor G S)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) :
    ¬({a,b,c}:Finset V)⊆S := by
  intro inc
  obtain ⟨C,rule⟩ := monochrome G S h
  have ha : a∈S := inc (by simp)
  have hb : b∈S := inc (by simp)
  have hc : c∈S := inc (by simp)
  have := rule a ha b hb ab
  have := rule b hb c hc bc
  have := rule c hc a ha ca
  tauto

omit [Fintype V] in
theorem five_excluded (G : SimpleGraph V) (S : Finset V) (h : TwoColor G S)
    (a b c d e : V) (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e) (ea : G.Adj e a) :
    ¬({a,b,c,d,e}:Finset V)⊆S := by
  intro inc
  obtain ⟨C,rule⟩ := monochrome G S h
  have ha : a∈S := inc (by simp)
  have hb : b∈S := inc (by simp)
  have hc : c∈S := inc (by simp)
  have hd : d∈S := inc (by simp)
  have he : e∈S := inc (by simp)
  have := rule a ha b hb ab
  have := rule b hb c hc bc
  have := rule c hc d hd cd
  have := rule d hd e he de
  have := rule e he a ha ea
  tauto

omit [Fintype V] in
/-- Certify a biconnected graph using a descending route after each deletion. -/
theorem noCut_of_routes (G : SimpleGraph V) (base : V→V) (h : V→V→ℕ) (distinct : ∀ c, base c≠c)
    (next : ∀ c v, v≠c → v≠base c → ∃ y≠c, G.Adj v y ∧ h c y<h c v) : NoCut G := by
  intro c
  let s : ↥({c}ᶜ : Set V) := ⟨base c,distinct c⟩
  let H := G.induce ({c}ᶜ : Set V)
  have route (v : ↥({c}ᶜ : Set V)) : H.Reachable v s := by
    induction eq : h c v.val using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases same : v.val=base c
      · have ve : v=s := Subtype.ext same
        rw [ve]
      · obtain ⟨y,yc,e,lt⟩ := next c v.val v.property same
        let w : ↥({c}ᶜ : Set V) := ⟨y,yc⟩
        exact (show H.Adj v w from e).reachable.trans (ih _ (eq ▸ lt) w rfl)
  exact fun a b => (route a).trans (route b).symm

#print axioms leaf_cut_constant
#print axioms triangle_excluded
#print axioms five_excluded
#print axioms noCut_of_routes
end Minimal180
