import PoolCut
namespace Graffiti384b.PendantClose
open Finset SimpleGraph
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def cubics (X : Finset V) := X.filter (fun v => G.degree v=3)

private theorem cubic_cap {X : Finset V} {e : V} (fr : Frame G X e) : (cubics G X).card≤2 := by
  classical
  have sub : cubics G X⊆X := filter_subset ..
  have im : (cubics G X).image (trianglesAt G)⊆{2,3} := by
    intro score sm
    obtain ⟨v,vm,rfl⟩ := mem_image.mp sm
    have upper := Repair.triangles_le_choose G v
    rw [(mem_filter.mp vm).2,show (3:ℕ).choose 2=3 by decide] at upper
    have lower := fr.scores v (sub vm)
    simp only [mem_insert,mem_singleton]; omega
  have ct := card_le_card im
  rwa [card_image_of_injOn (fr.distinct.mono sub),show ({2,3}:Finset ℕ).card=2 by decide] at ct

private theorem adjacent {X : Finset V} {e : V} (fr : Frame G X e) (bad : Fintype.card V-15<gamma G)
    {C : Finset V} (cl : G.IsNClique 5 C) (cx : C⊆X) {x : V} (xc : x∈C) :
    ∃u∈X,G.degree u=3 ∧ G.Adj u x := by
  by_contra! no
  obtain ⟨P,pc,sz⟩ := exists_subset_card_eq (show 2≤(C.erase x).card by rw [card_erase_of_mem xc,cl.2]; decide)
  exact (not_lt_of_ge (paired G fr cl cx xc pc sz (fun u um _ d ux => (no u um d ux).elim))) bad

private theorem two_contacts {X : Finset V} {e : V} (fr : Frame G X e) {C : Finset V} (cl : G.IsNClique 5 C) (cx : C⊆X)
    (bad : Fintype.card V-15<gamma G)
    (x : V) (xc : x∈C) :
    2≤ ∑ u∈cubics G X, (if G.Adj u x then (if nbr G u C≤2 then 2 else 1) else 0) := by
  classical
  obtain ⟨u,umX,du,ux⟩ := adjacent G fr bad cl cx xc
  have um : u∈cubics G X := mem_filter.mpr ⟨umX,du⟩
  let w := fun v => if G.Adj v x then (if nbr G v C≤2 then 2 else 1) else 0
  change 2≤∑ v∈cubics G X,w v
  have one (v : V) (vx : G.Adj v x) : 1≤w v := by simp only [w,if_pos vx]; split <;> decide
  by_cases light : nbr G u C≤2
  · exact (show 2≤w u by simp [w,ux,light]).trans (single_le_sum (fun i _ => Nat.zero_le (w i)) um)
  by_cases other : ∃ v,v∈cubics G X ∧ v≠u ∧ G.Adj v x
  · obtain ⟨v,vm,vu,vx⟩ := other
    have both : ({v,u}:Finset V)⊆cubics G X := insert_subset vm (singleton_subset_iff.mpr um)
    have tot := sum_le_sum_of_subset_of_nonneg both (fun i _ _ => Nat.zero_le (w i))
    rw [sum_pair vu] at tot
    have := one v vx
    have := one u ux
    omega
  let N := G.neighborFinset u
  have full : C.filter (G.Adj u)=N := eq_of_subset_of_card_le
    (fun v vm => (G.mem_neighborFinset _ _).mpr (mem_filter.mp vm).2) (by
      change (G.neighborFinset u).card≤nbr G u C
      rw [card_neighborFinset_eq_degree,du]; omega)
  have nc : N⊆C := full ▸ filter_subset _ _
  have xn : x∈N := (G.mem_neighborFinset _ _).mpr ux
  have sz : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
  let P := N.erase x
  have pc : P⊆C.erase x := fun v m => mem_erase.mpr ⟨(mem_erase.mp m).1,nc (mem_erase.mp m).2⟩
  have ps : P.card=2 := by rw [show P=N.erase x from rfl,card_erase_of_mem xn,sz]
  exfalso
  apply (not_lt_of_ge (paired G fr cl cx xc pc ps ?_)) bad
  intro v vm _ dv vx
  have eq : v=u := by
    apply Classical.byContradiction
    intro diff
    exact other ⟨v,mem_filter.mpr ⟨vm,dv⟩,diff,vx⟩
  subst v
  have allP : P.filter (G.Adj u)=P := filter_true_of_mem (fun y ym =>
    (G.mem_neighborFinset _ _).mp (erase_subset _ _ ym))
  simp only [nbr,allP,ps,le_rfl]

/-- In a failure a five-clique in the pool would require ten units of
cubic contact. Its at most two pool cubics can supply only eight. -/
theorem five_free {X : Finset V} {e : V} (fr : Frame G X e) (bad : Fintype.card V-15<gamma G)
    (C : Finset V) (cx : C⊆X) : ¬G.IsNClique 5 C := by
  classical
  intro cl
  let w := fun u => if nbr G u C≤2 then 2 else 1
  have low : ∑ _x∈C,2 ≤ ∑ x∈C,∑ u∈cubics G X,(if G.Adj u x then w u else 0) :=
    sum_le_sum (fun x xc => two_contacts G fr cl cx bad x xc)
  rw [sum_comm] at low
  have upper : ∑ u∈cubics G X,∑ x∈C,(if G.Adj u x then w u else 0) ≤ ∑ _u∈cubics G X,4 := by
    apply sum_le_sum
    intro u um
    rw [← sum_filter]
    simp only [sum_const,smul_eq_mul]
    change nbr G u C * w u≤4
    have cap : nbr G u C≤3 := by
      have sub : C.filter (G.Adj u)⊆G.neighborFinset u := fun v vm => (G.mem_neighborFinset _ _).mpr (mem_filter.mp vm).2
      exact (card_le_card sub).trans_eq ((card_neighborFinset_eq_degree ..).trans (mem_filter.mp um).2)
    dsimp only [w]
    split <;> omega
  have z := low.trans upper
  simp only [sum_const,smul_eq_mul,cl.2] at z
  have := cubic_cap G fr
  omega

end Graffiti384b.PendantClose
#print axioms Graffiti384b.PendantClose.five_free
