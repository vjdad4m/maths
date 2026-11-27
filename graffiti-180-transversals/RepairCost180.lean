import RootReserve180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The outside neighbors of the protected vertices in a transversal. -/
noncomputable def repairNeighbors (G : SimpleGraph V) (X K : Finset V) : Finset V :=
  (univ\X).filter (fun y => ∃ x∈X∩K,G.Adj x y)

omit [Fintype V] [DecidableEq V] in
theorem cheap_side (N : Finset V) (c : V→Bool) :
    ∃ a : Bool,2*(N.filter (fun x => c x=a)).card≤N.card := by
  classical
  have cnt := filter_card_add_filter_neg_card_eq_card (s:=N) (p:=fun x => c x=true)
  have eq : N.filter (fun x => ¬c x=true)=N.filter (fun x => c x=false) := by ext x;simp
  rw [eq] at cnt
  by_cases small : 2*(N.filter (fun x => c x=true)).card≤N.card
  · exact ⟨true,small⟩
  · exact ⟨false,by omega⟩

/-- Repair a bipartization after requiring the independent set K. Remove
the unprotected transversal vertices and the cheaper color of outside
neighbors of its protected vertices. -/
theorem transversal_repair (G : SimpleGraph V) (X K : Finset V) (ki : Indep G K)
    (bi : TwoColor G (univ\X)) :
    ∃ Z, TwoColor G Z ∧ K⊆Z ∧
      2*(Fintype.card V-Z.card)≤2*(X\K).card+(repairNeighbors G X K).card := by
  classical
  obtain ⟨c,ok⟩ := (color_function ..).mp bi
  let N := repairNeighbors G X K
  obtain ⟨a,cheap⟩ := cheap_side N c
  let F := N.filter (fun x => c x=a)
  let M := (X\K)∪F
  let Z := univ\M
  let paint x := if x∈X then a else c x
  have keep : K⊆Z := by
    intro x xk
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    rintro m
    rcases mem_union.mp m with old|f
    · exact (mem_sdiff.mp old).2 xk
    · obtain ⟨y,ym,ed⟩ := (mem_filter.mp (mem_filter.mp f).1).2
      exact ki y (mem_inter.mp ym).2 x xk ed.ne ed
  have pinned (x : V) (xz : x∈Z) (xx : x∈X) : x∈K := by
    by_contra miss
    exact (mem_sdiff.mp xz).2 (mem_union_left _ (mem_sdiff.mpr ⟨xx,miss⟩))
  have unlike (x : V) (xz : x∈Z) (xx : x∈X) (y : V) (yz : y∈Z) (yx : y∉X)
      (ed : G.Adj x y) : a≠c y := by
    intro eq
    have yn : y∈N := mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,yx⟩,x,mem_inter.mpr ⟨xx,pinned x xz xx⟩,ed⟩
    exact (mem_sdiff.mp yz).2 (mem_union_right _ (mem_filter.mpr ⟨yn,eq.symm⟩))
  have color : TwoColor G Z := by
    apply (color_function ..).mpr
    refine ⟨paint,fun x xz y yz ed => ?_⟩
    by_cases xx : x∈X <;> by_cases yx : y∈X
    · exact (ki x (pinned x xz xx) y (pinned y yz yx) ed.ne ed).elim
    · simpa [paint,xx,yx] using unlike x xz xx y yz yx ed
    · simpa [paint,xx,yx] using Ne.symm (unlike y yz yx x xz xx ed.symm)
    · simpa [paint,xx,yx] using ok x (mem_sdiff.mpr ⟨mem_univ _,xx⟩) y (mem_sdiff.mpr ⟨mem_univ _,yx⟩) ed
  have cnt := card_sdiff_add_card_eq_card (subset_univ M)
  change Z.card+M.card=Fintype.card V at cnt
  have small : M.card≤(X\K).card+F.card := card_union_le ..
  change 2*F.card≤N.card at cheap
  exact ⟨Z,color,keep,by change 2*(Fintype.card V-Z.card)≤2*(X\K).card+N.card;omega⟩

theorem one_repair (G : SimpleGraph V) (t : V) (K : Finset V) (ki : Indep G K) (tk : t∈K)
    (bi : TwoColor G (univ.erase t)) :
    ∃ Z,TwoColor G Z ∧ K⊆Z ∧ 2*(Fintype.card V-Z.card)≤G.degree t := by
  classical
  have empty : ({t}:Finset V)\K=∅ := sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr tk)
  have eq : (univ : Finset V)\{t}=univ.erase t := by ext x; simp [and_comm]
  obtain ⟨Z,col,keep,cap⟩ := transversal_repair G {t} K ki (eq.symm ▸ bi)
  have sub : repairNeighbors G {t} K⊆G.neighborFinset t := by
    intro y ym
    obtain ⟨x,xm,ed⟩ := (mem_filter.mp ym).2
    exact (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp (mem_inter.mp xm).1) ▸ ed)
  have deg := card_le_card sub
  rw [card_neighborFinset_eq_degree] at deg
  rw [empty,card_empty,Nat.mul_zero,zero_add] at cap
  exact ⟨Z,col,keep,cap.trans deg⟩

#print axioms cheap_side
#print axioms transversal_repair
#print axioms one_repair
end Minimal180.Transversals
