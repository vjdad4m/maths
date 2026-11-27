import ForkPattern180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Keep a depth-two tree around a prescribed hub while reserving two
root edges. The hub need not be adjacent to the root. -/
theorem fork_tree (H : SimpleGraph V) (hc : H.Connected) (r m s t : V)
    (C L : Finset V) (f : V→V) (dis : Disjoint C L) (free : ∀ z∈({r,m,s,t}:Finset V),z∉C∪L)
    (rs : H.Adj r s) (rt : H.Adj r t) (st : s≠t)
    (arm : ∀ v∈L,f v∈C ∧ H.Adj v (f v)) :
    ∃ T≤H,T.IsTree ∧ r∉leaves T ∧ (∀ c∈C,H.Adj c m → T.Adj c m) ∧ (∀ v∈L,T.Adj v (f v)) := by
  classical
  have outside (z : V) (hz : z∈({r,m,s,t}:Finset V)) : z∉C ∧ z∉L :=
    ⟨fun h => free z hz (mem_union_left _ h),fun h => free z hz (mem_union_right _ h)⟩
  have rh := outside r (by simp)
  have mh := outside m (by simp)
  have sh := outside s (by simp)
  have th := outside t (by simp)
  let p (x : V) := if x∈L then f x else if x∈C then m else r
  let d (x : V) : ℕ := if x∈L then 3 else if x∈C then 2 else if x=r then 0 else 1
  have down (x : V) (xr : x≠r) : d (p x)<d x := by
    by_cases xl : x∈L
    · have fc := (arm x xl).1
      have fl : f x∉L := fun h => disjoint_left.mp dis fc h
      simp [d,p,xl,fl,fc]
    by_cases xc : x∈C
    · simp only [p,xl,if_false,xc,if_true,d,mh.1,mh.2]
      split_ifs <;> decide
    · simp [p,d,xl,xc,xr,rh.1,rh.2]
  obtain ⟨K,kt,ke⟩ := virtual_tree r p d down
  obtain ⟨T,sub,tr,keep⟩ := keep_target H K hc kt
  have root (v : V) (rv : H.Adj r v) (fv : v∉C ∧ v∉L) : T.Adj r v :=
    keep ⟨rv,(show K.Adj v r by simpa [p,fv.1,fv.2] using ke v rv.ne.symm).symm⟩
  refine ⟨T,sub,tr,fun h => st (leaf_unique T h (root s rs sh) (root t rt th)),?_,?_⟩
  · intro c cm spoke
    have no : c∉L := fun h => disjoint_left.mp dis cm h
    have nr : c≠r := fun eq => rh.1 (eq ▸ cm)
    exact keep ⟨spoke,by simpa [p,no,cm] using ke c nr⟩
  · intro v vl
    exact keep ⟨(arm v vl).2,by simpa [p,vl] using ke v (fun eq => rh.2 (eq ▸ vl))⟩

theorem marked_tree_budget (G T : SimpleGraph V) [DecidableRel T.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A)
    (sub : T≤G) (tr : T.IsTree) (nr : r∉leaves T) :
    let P := parity G r odd
    (∀ {x y},T.Adj x y → (x∈P ↔ y∉P)) →
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card →
    1+(∑ v∈A∪P,(T.degree v-2))+bipartiteNum G<Fintype.card V := by
  classical
  intro P cross bad
  let D := (A∪P)\(A∩P)
  have id := tree_defect T tr hn r nr A P (fun x hx y hy ne e => ai x hx y hy ne (sub e)) cross
  change Fintype.card V+(eligible A P r∩leaves T).card+(T.edgeFinset∩D.sym2).card=
    1+A.card+P.card+D.card+∑ v∈A∪P,(T.degree v-2) at id
  have fs := forest_strict T tr D (failed_difference G hc hn r odd A ai bad)
  have lf : (eligible A P r∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  omega

#print axioms fork_tree
#print axioms marked_tree_budget
end Minimal180.HigherRank
