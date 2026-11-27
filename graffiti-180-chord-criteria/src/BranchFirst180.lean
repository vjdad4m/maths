import TightFirst180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- If prescribed branching consumes all but one unit of bipartite deficit,
the remaining unit makes the symmetric-difference forest connected. Every
vertex outside the selected branching set which is marked has degree at most two. -/
theorem saturated_branch (J T : SimpleGraph V) [DecidableRel T.Adj]
    (tr : T.IsTree) (sub : T≤J) (hn : 1<Fintype.card V) (r : V) (internal : r∉leaves T)
    (A P B : Finset V) (ai : Indep J A) (ne : A≠P) (bx : B⊆A∪P)
    (cross : ∀ {x y}, T.Adj x y → (x∈P ↔ y∉P))
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (budget : Fintype.card V+2*B.card≤bipartiteNum J+1+∑ x∈B,T.degree x) :
    (eligible A P r∩leaves T).card=weightedLeaves J (eligible A P r) ∧
    (∀ w∈A∪P,w∉B → T.degree w≤2) ∧
    let D := (A∪P)\(A∩P)
    (T.edgeFinset∩D.sym2).card+1=D.card := by
  classical
  let D := (A∪P)\(A∩P)
  let exc (x : V) := T.degree x-2
  have pos : D.Nonempty := by
    by_contra! no
    apply ne
    ext x
    have out : x∉D := fun h => no ⟨x,h⟩
    simp only [D,mem_sdiff,mem_union,mem_inter] at out
    tauto
  have few := forest_strict T tr D pos
  have ident := tree_defect T tr hn r internal A P (fun x hx y hy neq e => ai x hx y hy neq (sub e)) cross
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+∑ x∈A∪P,exc x at ident
  have cap := score_of_tree J T sub tr (eligible A P r)
  have deg : ∑ x∈B,T.degree x≤∑ x∈B,(2+exc x) := sum_le_sum (fun _ _ => by dsimp only [exc]; omega)
  rw [sum_add_distrib,sum_const,smul_eq_mul] at deg
  have lo := sum_le_sum_of_subset_of_nonneg (f:=exc) bx (fun _ _ _ => Nat.zero_le _)
  refine ⟨by omega,?_,by change (T.edgeFinset∩D.sym2).card+1=D.card; omega⟩
  intro w wx wb
  have all := sum_le_sum_of_subset_of_nonneg (f:=exc) (insert_subset wx bx) (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert wb] at all
  have ew : exc w=T.degree w-2 := rfl
  omega

/-- A forest in the distance-parity graph suffices. It need only contain
the spokes, keep the root and the eligible tips internal, and already
exhibit the specified branching away from the middle. -/
theorem first_of_branch_forest (J F : SimpleGraph V) [DecidableRel F.Adj]
    (jc : J.Connected) (hn : 3<Fintype.card V) (r u v w : V) (uv : u≠v) (old : ¬J.Adj u v)
    (odd : Bool) (A B : Finset V) (ai : Indep J A) (ne : A≠parity J r odd)
    (bx : B⊆A∪parity J r odd) (wb : w∉B)
    (sub : F≤alternating J (parity J r odd)) (acyc : F.IsAcyclic)
    (uw : F.Adj u w) (vw : F.Adj v w) (root : 2≤F.degree r)
    (tips : ∀ x∈({u,v}:Finset V), x∈eligible A (parity J r odd) r → 2≤F.degree x)
    (middle : w∈eligible A (parity J r odd) r ∨
       (w≠r ∧ u∉A∩parity J r odd ∧ v∉A∩parity J r odd))
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card)
    (budget : Fintype.card V+2*B.card≤bipartiteNum J+1+∑ x∈B,F.degree x) :
    FirstForm J (eligible A (parity J r odd) r) u v w := by
  classical
  let P := parity J r odd
  let D := (A∪P)\(A∩P)
  let H := alternating J P
  obtain ⟨T,ft,th,tr⟩ := Graffiti179.Strong.extend_forest (alternating_parity J jc r odd).1 sub acyc
  have tj : T≤J := fun _ _ e => (th e).1
  have cross {x y} (e : T.Adj x y) : x∈P ↔ y∉P := (th e).2
  have deg (x:V) : F.degree x≤T.degree x := by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    exact card_le_card (fun y hy => (T.mem_neighborFinset ..).mpr (ft ((F.mem_neighborFinset ..).mp hy)))
  have internal (x:V) (d : 2≤F.degree x) : x∉leaves T := by
    intro lf
    have one : T.degree x=1 := (mem_filter.mp lf).2
    have := deg x
    omega
  have sum_bound := sum_le_sum (s:=B) (fun x _ => deg x)
  obtain ⟨opt,two,connectedD⟩ := saturated_branch J T tr tj (by omega) r (internal r root)
    A P B ai ne bx cross tight (by omega)
  have elig : w∈eligible A P r := by
    rcases middle with elig|⟨wr,up,vp⟩
    · exact elig
    apply eligible_iff.mpr
    refine ⟨?_,Or.inl wr⟩
    by_cases wp : w∈P
    · exact Or.inr wp
    have ud : u∈D := mem_sdiff.mpr ⟨mem_union_right _ ((cross (ft uw)).mpr wp),up⟩
    have vd : v∈D := mem_sdiff.mpr ⟨mem_union_right _ ((cross (ft vw)).mpr wp),vp⟩
    have wd := forest_middle T tr D connectedD u v w uv ud vd (ft uw) (ft vw)
    exact mem_union.mp (mem_sdiff.mp wd).1
  exact first_of_tree J T hn u v w uv old tr tj _ opt (ft uw) (ft vw) elig
    (two w (mem_union.mpr (eligible_iff.mp elig).1) wb)
    (fun x xt xu => internal x (tips x xt xu))

#print axioms saturated_branch
#print axioms first_of_branch_forest
end Minimal180
