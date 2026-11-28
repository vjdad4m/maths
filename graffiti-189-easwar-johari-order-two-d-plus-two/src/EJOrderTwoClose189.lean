import EJDisjointClosure189

namespace Graffiti189LongestPath.SmallOrder
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore Graffiti189LongestPath
open private Graffiti189Ore.degree_increasing Graffiti189Ore.graphSize_lt Graffiti189Ore.graphSize_le from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def EdgeReady (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  Fintype.card V≤G.degree u+G.degree v+1 ∨
    (Fintype.card V≤G.degree u+G.degree v+2 ∧ ∀ w,¬(G.Adj u w ∧ G.Adj v w))

/-- Every connected nontraceable graph has a connected nontraceable
supergraph terminal under the two safe connected-graph edge moves. -/
theorem exists_terminal_basic_completion (hc : G.Connected)
    (no : ¬Graffiti189Ore.Traceable G) :
    ∃ (H : SimpleGraph V) (inst : DecidableRel H.Adj),
      G≤H ∧ ¬Graffiti189Ore.Traceable H ∧
      ∀ u v : V,u≠v → ¬H.Adj u v → ¬(letI : DecidableRel H.Adj := inst; EdgeReady H u v) := by
  classical
  induction hn : graphSize (⊤ : SimpleGraph V)-graphSize G using Nat.strong_induction_on
      generalizing G with
  | h n ih =>
    by_cases terminal : ∀ u v : V,u≠v → ¬G.Adj u v → ¬EdgeReady G u v
    · exact ⟨G,_,le_rfl,no,terminal⟩
    have new : ∃ u v : V,u≠v ∧ ¬G.Adj u v ∧ EdgeReady G u v := by
      apply Classical.byContradiction
      intro never
      exact terminal (fun u v uv h r=>never ⟨u,v,uv,h,r⟩)
    obtain ⟨u,v,uv,notAdj,ready⟩ := new
    let K := G ⊔ fromEdgeSet ({s(u,v)} : Set (Sym2 V))
    letI : DecidableRel K.Adj := Classical.decRel _
    have sub : G≤K := le_sup_left
    have e : K.Adj u v := (sup_adj _ _ _ _).mpr (.inr ((fromEdgeSet_adj _).mpr ⟨rfl,uv⟩))
    have only (a b : V) (h : K.Adj a b) : G.Adj a b ∨ s(a,b)=s(u,v) := by
      rcases (sup_adj _ _ _ _).mp h with e|e
      · exact Or.inl e
      · exact Or.inr ((fromEdgeSet_adj _).mp e).1
    have nk : ¬Graffiti189Ore.Traceable K := by
      intro p
      apply no
      rcases ready with big|⟨little,dis⟩
      · exact traceable_closure_one only big p
      exact traceable_disjoint_neighbor_one_edge hc only notAdj dis little p
    have glt : G<K := lt_of_le_of_ne sub (fun h=>notAdj (h.symm ▸ e))
    have smaller : graphSize (⊤ : SimpleGraph V)-graphSize K<n := by
      have p := Graffiti189Ore.graphSize_lt glt
      have q := Graffiti189Ore.graphSize_le (le_top : K≤(⊤ : SimpleGraph V))
      omega
    obtain ⟨H,inst,h,nt,done⟩ := ih _ smaller (G:=K) (connected_of_supergraph sub hc) nk rfl
    exact ⟨H,inst,sub.trans h,nt,done⟩

/-- Easwar–Johari Theorem B(2), for arbitrary threshold d, with exact
parity counting and at most one degree below d. -/
theorem traceable_at_order_le_two_d_add_two (hc : G.Connected) (d : ℕ)
    (cap : ∀ v,(EvenFrom G v).card≤d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (bound : Fintype.card V≤2*d+2) : Graffiti189Ore.Traceable G := by
  classical
  by_cases low : Fintype.card V≤2*d+1
  · exact traceable_all_but_one_by_order hc d degree low
  have order : Fintype.card V=2*d+2 := by omega
  apply Classical.byContradiction
  intro no
  obtain ⟨H,inst,sub,nt,terminal⟩ := exists_terminal_basic_completion hc no
  letI : DecidableRel H.Adj := inst
  apply nt
  apply traceable_terminal_order_two_add hc d order sub cap degree
  intro u v uv uhi vhi uvn
  have stop := terminal u v uv uvn
  have deU := uhi.trans (Graffiti189Ore.degree_increasing sub u)
  have deV := vhi.trans (Graffiti189Ore.degree_increasing sub v)
  refine ⟨by
    apply Classical.byContradiction
    intro bad
    exact stop (.inl (by omega)),?_⟩
  apply Classical.byContradiction
  intro none
  apply stop
  exact .inr ⟨by omega,fun w both=>none ⟨w,both.1,both.2.symm⟩⟩

#print axioms traceable_at_order_le_two_d_add_two
end Graffiti189LongestPath.SmallOrder
