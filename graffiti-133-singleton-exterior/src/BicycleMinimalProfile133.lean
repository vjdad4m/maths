import Partial133
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133Bicycle
open SimpleGraph Finset Graffiti133
open scoped BigOperators
set_option linter.unusedSectionVars false

section Arithmetic
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Degree arithmetic after removing a vertex of a minimal positive-excess graph. -/
theorem minimum_excess_degrees (d : V → ℕ) (edges : ℕ)
    (large : 5 ≤ Fintype.card V) (over : Fintype.card V < edges)
    (sum_eq : (∑ v : V, d v) = 2*edges)
    (del : ∀ v, edges + 1 ≤ Fintype.card V + d v) :
    edges = Fintype.card V + 1 ∧
      ((∃ x, d x=4 ∧ ∀ y, y≠x → d y=2) ∨
        ∃ x y, x≠y ∧ d x=3 ∧ d y=3 ∧ ∀ z, z≠x → z≠y → d z=2) := by
  classical
  let n := Fintype.card V
  let k := edges - n
  have ke : edges=n+k := by dsimp [k,n]; omega
  have kp : 1≤k := by dsimp [k,n]; omega
  have dge (v : V) : k+1 ≤ d v := by
    have h := del v
    change edges+1≤n+d v at h
    omega
  have klower : n*(k+1) ≤ 2*edges := by
    calc
      n*(k+1) = ∑ _ : V, (k+1) := by simp [n]
      _ ≤ ∑ v : V, d v := Finset.sum_le_sum fun v _ => dge v
      _ = 2*edges := sum_eq
  have split : n*(k+1) = n*(k-1) + 2*n := by
    calc
      n*(k+1) = n*((k-1)+2) := by congr 1; omega
      _ = n*(k-1)+2*n := by rw [Nat.mul_add,Nat.mul_comm n 2]
  have kb := Nat.mul_le_mul_right (k-1) large
  change 5*(k-1)≤n*(k-1) at kb
  have kone : k=1 := by omega
  have e : edges=n+1 := by omega
  refine ⟨e,?_⟩
  let f (v : V) := d v-2
  have hTwo (v) : 2 ≤ d v := by simpa [kone] using dge v
  have df (v : V) : d v=f v+2 := by dsimp [f]; have := hTwo v; omega
  have fs : (∑ v : V, f v)=2 := by
    have eq : (∑ v : V, d v)=(∑ v : V, f v)+2*n := by
      simp_rw [df,Finset.sum_add_distrib,Finset.sum_const]
      simp [n,Nat.mul_comm]
    omega
  have le2 (v : V) : f v ≤ 2 := by
    rw [←fs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have pair (x y : V) (xy : x≠y) : f x+f y≤2 := by
    calc
      _ = ∑ v ∈ ({x,y} : Finset V), f v := by simp [xy]
      _ ≤ ∑ v : V, f v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
      _ = 2 := fs
  by_cases big : ∃ x, f x=2
  · obtain ⟨x,hx⟩ := big
    apply Or.inl
    refine ⟨x,by rw [df,hx],?_⟩
    intro y yx
    have h := pair y x yx
    rw [df]
    omega
  · apply Or.inr
    let S := Finset.univ.filter fun v => f v=1
    have atMost (v : V) : f v≤1 := by
      have hv := le2 v
      have ne : f v≠2 := fun eq => big ⟨v,eq⟩
      omega
    have size : S.card=2 := by
      unfold S
      rw [Finset.card_filter,←fs]
      apply Finset.sum_congr rfl
      intro x _
      have hx := atMost x
      split <;> omega
    obtain ⟨x,hx,y,hy,xy⟩ := Finset.one_lt_card.mp (show 1<S.card by omega)
    have fx := (Finset.mem_filter.mp hx).2
    have fy := (Finset.mem_filter.mp hy).2
    refine ⟨x,y,xy,by rw [df,fx],by rw [df,fy],?_⟩
    intro z zx zy
    have h : f z+f x+f y≤2 := calc
      _ = ∑ v ∈ ({z,x,y} : Finset V), f v := by simp [zx,zy,xy,Nat.add_assoc]
      _ ≤ ∑ v : V, f v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
      _ = 2 := fs
    rw [df]
    omega
end Arithmetic

section Graph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact count for deleting one vertex, with no structural restrictions. -/
theorem card_delete_add_degree (x : V) :
    (G.induce {y : V | y≠x}).edgeFinset.card + G.degree x = G.edgeFinset.card := by
  classical
  have e : G.edgeFinset ∩ ({y : V | y≠x} : Set V).toFinset.sym2 =
      G.edgeFinset.filter (fun e => x∉e) := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_sym2_iff,Set.mem_toFinset,Set.mem_setOf_eq]
    constructor
    · rintro ⟨inE,h⟩
      exact ⟨inE,fun hx => h x hx rfl⟩
    · rintro ⟨inE,h⟩
      exact ⟨inE,fun v hv vx => h (vx ▸ hv)⟩
  have mapped := SimpleGraph.map_edgeFinset_induce (G:=G) (s:={y : V | y≠x})
  rw [e] at mapped
  have count := congrArg Finset.card mapped
  rw [Finset.card_map] at count
  rw [count,←G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
  simpa only [not_not] using (Finset.filter_card_add_filter_neg_card_eq_card (s:=G.edgeFinset) (fun e : Sym2 V => x∉e))

private lemma delete_card (x : V) : Fintype.card {y : V // y≠x} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype,Finset.filter_ne']
  exact (Finset.card_erase_add_one (Finset.mem_univ x)).trans Finset.card_univ

private lemma other_neighbor (degree : ∀ v, 2 ≤ G.degree v) (v w : V) :
    ∃ x, G.Adj v x ∧ x≠w := by
  classical
  apply Classical.byContradiction
  intro bad
  have sub : G.neighborFinset v ⊆ {w} := by
    intro x hx
    by_contra h
    exact bad ⟨x,(G.mem_neighborFinset _ _).mp hx, by simpa using h⟩
  have le := Finset.card_le_card sub
  rw [G.card_neighborFinset_eq_degree,Finset.card_singleton] at le
  have := degree v
  omega

private theorem five_vertices [Nonempty V] (min : ∀ v, 2 ≤ G.degree v)
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) : 5 ≤ Fintype.card V := by
  classical
  let a : V := Classical.choice inferInstance
  obtain ⟨b,ab,_⟩ := other_neighbor G min a a
  obtain ⟨c,bc,ca⟩ := other_neighbor G min b a
  obtain ⟨d,cd,db⟩ := other_neighbor G min c b
  obtain ⟨e,de,ec⟩ := other_neighbor G min d c
  have ad : a≠d := fun h => noTri _ _ _ ab bc (h.symm ▸ cd)
  have be : b≠e := fun h => noTri _ _ _ bc cd (h.symm ▸ de)
  have ae : a≠e := by
    intro h
    have da : G.Adj d a := h.symm ▸ de
    exact db (h4 a c d b ca.symm da.symm cd ab bc.symm)
  let p : Fin 5 → V := ![a,b,c,d,e]
  have hinj : Function.Injective p := List.nodup_ofFn.mp (by
    simpa [p,List.ofFn_succ] using (show [a,b,c,d,e].Nodup by
      simp [ab.ne,ca.symm,ad,ae,bc.ne,db.symm,be,cd.ne,ec.symm,de.ne]))
  simpa using Fintype.card_le_of_injective p hinj

/-- Exact graph-side minimal bicycle degree profile. Single-vertex deletions
suffice; in a vertex-minimal induced positive-excess graph they all satisfy the premise. -/
theorem vertex_minimal_profile
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) (over : Fintype.card V < G.edgeFinset.card)
    (minimal : ∀ x : V, (G.induce {y : V | y≠x}).edgeFinset.card ≤ Fintype.card {y : V // y≠x}) :
    G.edgeFinset.card=Fintype.card V+1 ∧
      ((∃ x, G.degree x=4 ∧ ∀ y, y≠x → G.degree y=2) ∨
        ∃ x y, x≠y ∧ G.degree x=3 ∧ G.degree y=3 ∧ ∀ z, z≠x → z≠y → G.degree z=2) := by
  have d (v : V) : G.edgeFinset.card+1 ≤ Fintype.card V+G.degree v := by
    have elim := card_delete_add_degree G v
    have sz := delete_card v
    have small := minimal v
    omega
  have min (v : V) : 2 ≤ G.degree v := by
    have h := d v
    omega
  have sum := G.sum_degrees_eq_twice_card_edges
  haveI : Nonempty V := by
    rcases isEmpty_or_nonempty V with emp | ne
    · letI := emp
      have zero : (∑ v : V, G.degree v)=0 :=
        Finset.sum_eq_zero (fun v _ => isEmptyElim v)
      omega
    · exact ne
  exact minimum_excess_degrees (fun v : V => G.degree v) G.edgeFinset.card (five_vertices _ min noTri h4) over sum d
end Graph

#print axioms minimum_excess_degrees
#print axioms card_delete_add_degree
#print axioms vertex_minimal_profile
end Graffiti133Bicycle
