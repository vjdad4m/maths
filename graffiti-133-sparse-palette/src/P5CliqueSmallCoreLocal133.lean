import P5CliqueOnePortAmbientBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem small_mem_neighbor [DecidableRel G.Adj] {v w : V} :
    w∈G.neighborFinset v ↔ G.Adj v w := G.mem_neighborFinset v w

/-- Distinct neighbors of v lead to disjoint target sets on their second step
once the return to v is omitted. -/
def smallTwoHop (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).biUnion (fun w=>(G.neighborFinset w).erase v)

theorem smallTwoHop_card [DecidableRel G.Adj] (h4 : FourCycleFree G) (v : V) :
    (smallTwoHop G v).card=∑ w∈G.neighborFinset v,(G.degree w-1) := by
  classical
  have dis : ((G.neighborFinset v : Finset V) : Set V).PairwiseDisjoint
      (fun w=>(G.neighborFinset w).erase v) := by
    intro a av b bv ne
    apply Finset.disjoint_left.mpr
    intro x ax bx
    obtain ⟨xv,ax'⟩ := Finset.mem_erase.mp ax
    obtain ⟨_,bx'⟩ := Finset.mem_erase.mp bx
    have eq := h4 v x a b xv.symm (small_mem_neighbor.mp av) (small_mem_neighbor.mp ax').symm
      (small_mem_neighbor.mp bv) (small_mem_neighbor.mp bx').symm
    exact ne eq
  unfold smallTwoHop
  rw [Finset.card_biUnion dis]
  apply Finset.sum_congr rfl
  intro w wm
  have vw : v∈G.neighborFinset w := small_mem_neighbor.mpr (small_mem_neighbor.mp wm).symm
  rw [Finset.card_erase_of_mem vw,G.card_neighborFinset_eq_degree]

theorem smallTwoHop_sub [DecidableRel G.Adj] (v : V) :
    smallTwoHop G v⊆(Finset.univ : Finset V).erase v := by
  classical
  intro x xm
  obtain ⟨w,wm,xx⟩ := Finset.mem_biUnion.mp xm
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp xx).1,Finset.mem_univ _⟩

theorem smallTwoHop_lower_degree [DecidableRel G.Adj] (h4 : FourCycleFree G)
    (k : Nat) (dmin : ∀ x,k+1≤G.degree x) (v : V) :
    k*G.degree v≤(smallTwoHop G v).card := by
  classical
  rw [smallTwoHop_card h4]
  calc
    _=∑ _w∈G.neighborFinset v,k := by simp [G.card_neighborFinset_eq_degree,Nat.mul_comm]
    _≤_ := Finset.sum_le_sum (fun w _=>by have h:=dmin w; omega)

theorem smallTwoHop_trianglefree_bound [DecidableRel G.Adj] (v : V)
    (free : ∀ x y,G.Adj v x→G.Adj v y→¬G.Adj x y) :
    (smallTwoHop G v).card+G.degree v+1≤Fintype.card V := by
  classical
  let N := G.neighborFinset v
  let H := smallTwoHop G v
  have dis : Disjoint H N := by
    apply Finset.disjoint_left.mpr
    intro x hx xn
    obtain ⟨w,wm,wx⟩ := Finset.mem_biUnion.mp hx
    have e := small_mem_neighbor.mp (Finset.mem_erase.mp wx).2
    exact free w x (small_mem_neighbor.mp wm) (small_mem_neighbor.mp xn) e
  have ns : N⊆(Finset.univ : Finset V).erase v := by
    intro x xm
    exact Finset.mem_erase.mpr ⟨(small_mem_neighbor.mp xm).ne.symm,Finset.mem_univ _⟩
  have le := Finset.card_le_card (Finset.union_subset (smallTwoHop_sub (G:=G) v) ns)
  rw [Finset.card_union_of_disjoint dis,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ] at le
  change H.card+N.card≤Fintype.card V-1 at le
  have n := G.card_neighborFinset_eq_degree v
  have pos : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  change N.card=G.degree v at n
  change H.card+G.degree v+1≤Fintype.card V
  omega

theorem small_local_le_degree [DecidableRel G.Adj] (v : V) :
    localIndependence G v≤G.degree v := by
  classical
  let N := G.neighborFinset v
  have adj (S : Finset V) (s : S∈localIndependentSets G v) :
      S⊆N ∧ ∀ x∈S,∀ y∈S,¬G.Adj x y := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and,N,small_mem_neighbor] using s
  unfold localIndependence
  rw [←G.card_neighborFinset_eq_degree]
  exact Finset.sup_le_iff.mpr (fun S sm=>Finset.card_le_card (adj S sm).1)

theorem small_local_triangle_loss [DecidableRel G.Adj] (v a b : V)
    (va : G.Adj v a) (vb : G.Adj v b) (ab : G.Adj a b) :
    localIndependence G v+1≤G.degree v := by
  classical
  let N := G.neighborFinset v
  have adj (S : Finset V) (s : S∈localIndependentSets G v) :
      S⊆N ∧ ∀ x∈S,∀ y∈S,¬G.Adj x y := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and,N,small_mem_neighbor] using s
  have npos : 0<G.degree v := by
    rw [←G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨a,small_mem_neighbor.mpr va⟩
  have le : localIndependence G v≤G.degree v-1 := by
    unfold localIndependence
    apply Finset.sup_le_iff.mpr
    intro S sm
    have sub := (adj S sm).1
    have ne : S≠N := by
      intro eq
      exact (adj S sm).2 a (eq.symm ▸ small_mem_neighbor.mpr va)
        b (eq.symm ▸ small_mem_neighbor.mpr vb) ab
    have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne⟩)
    change S.card<(G.neighborFinset v).card at lt
    rw [G.card_neighborFinset_eq_degree] at lt
    omega
  omega

theorem small_local_perfect_matching_bound [DecidableRel G.Adj] (h4 : FourCycleFree G) (v : V)
    (full : G.neighborFinset v⊆smallTwoHop G v) :
    2*localIndependence G v≤G.degree v := by
  classical
  let N := G.neighborFinset v
  have partner (x : V) (xm : x∈N) : ∃ y∈N,G.Adj x y := by
    obtain ⟨y,ym,xy⟩ := Finset.mem_biUnion.mp (full xm)
    exact ⟨y,ym,(small_mem_neighbor.mp (Finset.mem_erase.mp xy).2).symm⟩
  have lp : localIndependence G v≤G.degree v/2 := by
    unfold localIndependence
    apply Finset.sup_le_iff.mpr
    intro S sm
    have adj : S⊆N ∧ ∀ x∈S,∀ y∈S,¬G.Adj x y := by
      simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
        Finset.mem_univ,true_and,N,small_mem_neighbor] using sm
    have ex (x : {x : V // x∈S}) : ∃ y∈N\S,G.Adj x.val y := by
      obtain ⟨y,ym,xy⟩ := partner x.val (adj.1 x.property)
      exact ⟨y,Finset.mem_sdiff.mpr ⟨ym,fun ys=>adj.2 _ x.property _ ys xy⟩,xy⟩
    choose f fm fa using ex
    let F : {x : V // x∈S} → {y : V // y∈N\S} := fun x=>⟨f x,fm x⟩
    have inj : Function.Injective F := by
      intro x y e
      have ef : f x=f y := congrArg Subtype.val e
      have fN := (Finset.mem_sdiff.mp (fm x)).1
      have vx : G.Adj v x.val := small_mem_neighbor.mp (adj.1 x.property)
      have vy : G.Adj v y.val := small_mem_neighbor.mp (adj.1 y.property)
      have vf : G.Adj v (f x) := small_mem_neighbor.mp fN
      exact Subtype.ext (h4 v (f x) x.val y.val vf.ne vx (fa x).symm vy (ef.symm ▸ (fa y).symm))
    have bound : S.card≤(N\S).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F inj
    have total := Finset.card_sdiff_add_card_eq_card adj.1
    have nde : N.card=G.degree v := G.card_neighborFinset_eq_degree v
    rw [nde] at total
    omega
  omega

#print axioms smallTwoHop_card
#print axioms smallTwoHop_trianglefree_bound
#print axioms small_local_perfect_matching_bound
end Graffiti133P5CliqueArms
