import TriangleDefect180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- For a fixed forced-spoke tree in a tight instance, optimality and a
nonbranching middle are equivalent to a linear edge-weight certificate.
The set B selects the marked vertices whose degree surplus is counted. -/
theorem reserve_iff (J T : SimpleGraph V) [DecidableRel T.Adj]
    (hn : 1<Fintype.card V) (r w : V) (tr : T.IsTree) (sub : T≤J) (root : r∉leaves T)
    (A P : Finset V) (ai : Indep J A) (cross : ∀ {i j}, T.Adj i j → (i∈P ↔ j∉P))
    (wm : w∈A∪P)
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card) :
    let D := (A∪P)\(A∩P)
    ((eligible A P r∩leaves T).card=weightedLeaves J (eligible A P r) ∧ T.degree w≤2) ↔
    ∃ B⊆A∪P, w∉B ∧
      Fintype.card V+(T.edgeFinset∩D.sym2).card+2*B.card≤bipartiteNum J+D.card+∑ x∈B,T.degree x := by
  classical
  let X := A∪P
  let D := X\(A∩P)
  let exc (x : V) := T.degree x-2
  have eqn := tree_defect T tr hn r root A P (fun x hx y hy ne e => ai x hx y hy ne (sub e)) cross
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+∑ x∈X,exc x at eqn
  change _ ↔ ∃ B⊆X, w∉B ∧ Fintype.card V+(T.edgeFinset∩D.sym2).card+2*B.card≤bipartiteNum J+D.card+∑ x∈B,T.degree x
  constructor
  · rintro ⟨opt,two⟩
    let B := X.filter (fun x => 2<T.degree x)
    have out : w∉B := fun h => (Nat.not_lt.mpr two) (mem_filter.mp h).2
    have excB : ∑ x∈B, exc x=∑ x∈X,exc x := by
      apply sum_subset (filter_subset ..)
      intro x hx notB
      have small : T.degree x≤2 := Nat.le_of_not_gt (fun lt => notB (mem_filter.mpr ⟨hx,lt⟩))
      exact Nat.sub_eq_zero_of_le small
    have deg : ∑ x∈B,T.degree x=∑ x∈B,(2+exc x) := by
      apply sum_congr rfl
      intro x h
      have large := (mem_filter.mp h).2
      change 2<T.degree x at large
      dsimp only [exc]; omega
    rw [sum_add_distrib,sum_const,smul_eq_mul,excB] at deg
    exact ⟨B,filter_subset ..,out,by omega⟩
  · rintro ⟨B,bx,out,limit⟩
    have bound := score_bound_aux (T:=T) (J:=J) (U:=eligible A P r) sub tr
    have deg : ∑ x∈B,T.degree x≤∑ x∈B,(2+exc x) := sum_le_sum (fun x _ => by dsimp only [exc]; omega)
    rw [sum_add_distrib,sum_const,smul_eq_mul] at deg
    have subset : insert w B⊆X := insert_subset wm bx
    have remaining := sum_le_sum_of_subset_of_nonneg (f:=exc) subset (fun _ _ _ => Nat.zero_le _)
    rw [sum_insert out] at remaining
    have ew : exc w=T.degree w-2 := rfl
    constructor <;> omega
where
  score_bound_aux {T J : SimpleGraph V} {U : Finset V} (sub : T≤J) (tr : T.IsTree) :
      (U∩leaves T).card≤weightedLeaves J U := by
    classical
    exact le_sup (f:=fun F => (U∩leaves F).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)

theorem reserve_triangle_gain (J T : SimpleGraph V) [DecidableRel T.Adj]
    (hn : 3<Fintype.card V) (r u v w : V) (uv : u≠v) (tr : T.IsTree) (sub : T≤J)
    (root : r∉leaves T) (A P : Finset V) (ai : Indep J A)
    (cross : ∀ {i j}, T.Adj i j → (i∈P ↔ j∉P))
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (uw : T.Adj u w) (vw : T.Adj v w) (elig : w∈eligible A P r)
    (B : Finset V) (bx : B⊆A∪P) (out : w∉B)
    (limit : let D := (A∪P)\(A∩P)
             Fintype.card V+(T.edgeFinset∩D.sym2).card+2*B.card≤bipartiteNum J+D.card+∑ x∈B,T.degree x) :
    weightedLeaves J (eligible A P r)<weightedLeaves (J⊔SimpleGraph.edge u v) (eligible A P r) := by
  obtain ⟨opt,two⟩ := (reserve_iff J T (by omega) r w tr sub root A P ai cross (mem_union.mpr (eligible_iff.mp elig).1) tight).mpr ⟨B,bx,out,limit⟩
  exact optimal_middle_gain J T hn u v w uv tr sub _ opt uw vw elig two

#print axioms reserve_iff
#print axioms reserve_triangle_gain
end Minimal180
