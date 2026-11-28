import EJEdgeOpening189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
open private getVert_injective_on from OreSpliceIndex189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem endpoint_mark_cards {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (all : ∀ v,v∈p.support) :
    ((range p.length).filter (fun i=>G.Adj a (p.getVert (i+1)))).card=G.degree a ∧
    ((range p.length).filter (fun i=>G.Adj b (p.getVert i))).card=G.degree b := by
  let A := (range p.length).filter (fun i=>G.Adj a (p.getVert (i+1)))
  let B := (range p.length).filter (fun i=>G.Adj b (p.getVert i))
  have ca : A.card = G.degree a := by
    rw [← card_neighborFinset_eq_degree]
    apply card_bij (fun i _=>p.getVert (i+1))
    · intro i hi
      exact (mem_neighborFinset G a _).mpr (mem_filter.mp hi).2
    · intro i hi j hj eq
      have il := mem_range.mp (mem_filter.mp hi).1
      have jl := mem_range.mp (mem_filter.mp hj).1
      have q := getVert_injective_on p hp (by omega) (by omega) eq
      omega
    · intro z hz
      have adj := (mem_neighborFinset G a _).mp hz
      obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp (all z)
      have kn : k≠0 := by
        rintro rfl
        simp at adj
      refine ⟨k-1,?_,?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_range.mpr (by omega),?_⟩
        convert adj using 2
        omega
      · congr 1
        omega
  have cb : B.card = G.degree b := by
    rw [← card_neighborFinset_eq_degree]
    apply card_bij (fun i _=>p.getVert i)
    · intro i hi
      exact (mem_neighborFinset G b _).mpr (mem_filter.mp hi).2
    · intro i hi j hj eq
      have il := mem_range.mp (mem_filter.mp hi).1
      have jl := mem_range.mp (mem_filter.mp hj).1
      exact getVert_injective_on p hp (by omega) (by omega) eq
    · intro z hz
      have adj := (mem_neighborFinset G b _).mp hz
      obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp (all z)
      have kn : k≠p.length := by
        rintro rfl
        simp at adj
      exact ⟨k,mem_filter.mpr ⟨mem_range.mpr (by omega),adj⟩,rfl⟩
  exact ⟨ca,cb⟩

theorem endpoint_marks_cover {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (all : ∀ v,v∈p.support)
    (degree : p.length≤G.degree a+G.degree b)
    (no : ∀ i,i<p.length → ¬(G.Adj a (p.getVert (i+1)) ∧ G.Adj b (p.getVert i))) :
    ∀ i,i<p.length → G.Adj a (p.getVert (i+1)) ∨ G.Adj b (p.getVert i) := by
  classical
  let A := (range p.length).filter (fun i=>G.Adj a (p.getVert (i+1)))
  let B := (range p.length).filter (fun i=>G.Adj b (p.getVert i))
  have ⟨ca,cb⟩ := endpoint_mark_cards p hp all
  change A.card=G.degree a at ca
  change B.card=G.degree b at cb
  have d : Disjoint A B := disjoint_left.mpr (fun i ai bi=>
    no i (mem_range.mp (mem_filter.mp ai).1) ⟨(mem_filter.mp ai).2,(mem_filter.mp bi).2⟩)
  have sub : A∪B⊆range p.length := union_subset (filter_subset _ _) (filter_subset _ _)
  have eq := eq_of_subset_of_card_le sub (by rw [card_union_of_disjoint d,card_range,ca,cb]; exact degree)
  intro i il
  have h : i∈A∪B := eq.symm ▸ mem_range.mpr il
  rcases mem_union.mp h with (ai : i∈A) | (bi : i∈B)
  · exact Or.inl ((mem_filter.mp ai).2)
  · exact Or.inr ((mem_filter.mp bi).2)

theorem unique_switch_endpoint_marks (n k : ℕ) (inside : 0<k ∧ k<n)
    (A B : ℕ→Prop) (cover : ∀ i,i<n → A i ∨ B i)
    (_dis : ∀ i,i<n → ¬(A i ∧ B i)) (first : A 0) (last : B (n-1))
    (switch : ∀ i,i+1<n → A i → B (i+1) → i+1=k) :
    (∀ i : ℕ, i < k → A i) ∧ (∀ i : ℕ, k ≤ i → i < n → B i) := by
  classical
  have pre : ∀ i,i<k → A i := by
    intro i
    induction i with
    | zero => exact fun _=>first
    | succ i ih =>
      intro small
      have old := ih (by omega)
      exact (cover (i+1) (by omega)).resolve_right
        (fun h=>by have e := switch i (by omega) old h; omega)
  refine ⟨pre,?_⟩
  intro i ki il
  apply Classical.byContradiction
  intro bi
  have ex : ∃ t,i≤t ∧ t<n ∧ B t := ⟨n-1,by omega,by omega,last⟩
  let t := Nat.find ex
  have ht : i≤t ∧ t<n ∧ B t := Nat.find_spec ex
  have it : i<t := by
    have e : i≠t := fun e=>bi (e.symm ▸ ht.2.2)
    omega
  have older : ¬B (t-1) := by
    intro b
    have e := Nat.find_min' ex (show i≤t-1 ∧ t-1<n ∧ B (t-1) from ⟨by omega,by omega,b⟩)
    change t≤t-1 at e
    omega
  have prev := (cover (t-1) (by omega)).resolve_right older
  have tEq : t-1+1=t := by omega
  have e := switch (t-1) (by omega) prev (tEq.symm ▸ ht.2.2)
  omega

#print axioms endpoint_marks_cover
#print axioms unique_switch_endpoint_marks
end Graffiti189Ore
