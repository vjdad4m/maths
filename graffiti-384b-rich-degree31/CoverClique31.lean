import CoverCut31
namespace Graffiti384b.Cover31
open Finset SimpleGraph
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def cubics := (univ : Finset V).filter (fun v => G.degree v=3)

private theorem cubic_cap (t : (types G).card=31) (h : (high G).card=30) : (cubics G).card≤3 := by
  have sub : cubics G⊆high G := fun v vm => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp vm).2.ge⟩
  have inc : types G⊆((high G)\cubics G).image (trianglesAt G)∪range 4 := by
    intro j jm
    obtain ⟨v,_,rfl⟩ := mem_image.mp jm
    by_cases vd : 3<G.degree v
    · exact mem_union_left _ (mem_image.mpr ⟨v,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,vd.le⟩,
        fun z => (Nat.ne_of_lt vd) (mem_filter.mp z).2.symm⟩,rfl⟩)
    · have cap := (Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 (Nat.le_of_not_gt vd))
      exact mem_union_right _ (mem_range.mpr (by simpa using Nat.lt_succ_of_le cap))
  have total := (card_le_card inc).trans (card_union_le _ _)
  have im := card_image_le (s:=(high G)\cubics G) (f:=trianglesAt G)
  rw [t,card_range] at total
  rw [card_sdiff sub,h] at im
  have lim := card_le_card sub
  omega

/-- Every vertex of a five-clique needs a cubic neighbor in an extremal graph. -/
theorem adjacent (t : (types G).card=31) (h : (high G).card=30) (bad : bound G<gamma G)
    {C : Finset V} (cl : G.IsNClique 5 C) {x : V} (xc : x∈C) :
    ∃ u,G.degree u=3 ∧ G.Adj u x := by
  by_contra! no
  obtain ⟨P,pc,sz⟩ := exists_subset_card_eq (show 2≤(C.erase x).card by rw [card_erase_of_mem xc,cl.2]; decide)
  exact (not_lt_of_ge (paired G t h cl xc pc sz (fun u _ d ux => (no u d ux).elim))) bad

private theorem two_contacts {C : Finset V} (cl : G.IsNClique 7 C)
    (t : (types G).card=31) (h : (high G).card=30) (bad : bound G<gamma G)
    (x : V) (xc : x∈C) :
    2≤ ∑ u∈cubics G, (if G.Adj u x then (if nbr G u C≤2 then 2 else 1) else 0) := by
  classical
  obtain ⟨F,xf,fc,five⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr xc)
    (show ({x}:Finset V).card≤5 by simp) (show 5≤C.card by rw [cl.2]; decide)
  have cf : G.IsNClique 5 F := ⟨cl.1.subset fc,five⟩
  obtain ⟨u,du,ux⟩ := adjacent G t h bad cf (xf (mem_singleton_self _))
  have um : u∈cubics G := mem_filter.mpr ⟨mem_univ _,du⟩
  let w := fun v => if G.Adj v x then (if nbr G v C≤2 then 2 else 1) else 0
  change 2≤∑ v∈cubics G,w v
  have one (v : V) (vx : G.Adj v x) : 1≤w v := by simp only [w,if_pos vx]; split <;> decide
  by_cases light : nbr G u C≤2
  · exact (show 2≤w u by simp [w,ux,light]).trans (single_le_sum (fun i _ => Nat.zero_le (w i)) um)
  by_cases other : ∃ v,v∈cubics G ∧ v≠u ∧ G.Adj v x
  · obtain ⟨v,vm,vu,vx⟩ := other
    have both : ({v,u}:Finset V)⊆cubics G := insert_subset vm (singleton_subset_iff.mpr um)
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
  obtain ⟨K,nk,kc,ks⟩ := exists_subsuperset_card_eq nc (show N.card≤5 by omega) (show 5≤C.card by rw [cl.2]; decide)
  let P := N.erase x
  have pc : P⊆K.erase x := fun v m => mem_erase.mpr ⟨(mem_erase.mp m).1,nk (mem_erase.mp m).2⟩
  have ps : P.card=2 := by rw [show P=N.erase x from rfl,card_erase_of_mem xn,sz]
  exfalso
  apply (not_lt_of_ge (paired G t h (show G.IsNClique 5 K from ⟨cl.1.subset kc,ks⟩) (nk xn) pc ps ?_)) bad
  intro v _ dv vx
  have eq : v=u := by
    apply Classical.byContradiction
    intro diff
    exact other ⟨v,mem_filter.mpr ⟨mem_univ _,dv⟩,diff,vx⟩
  subst v
  have allP : P.filter (G.Adj u)=P := filter_true_of_mem (fun y ym =>
    (G.mem_neighborFinset _ _).mp (erase_subset _ _ ym))
  simp only [nbr,allP,ps,le_rfl]

/-- Seven vertices cannot receive two units each: a cubic seeing at most two
clique vertices supplies at most four units, and every other cubic at most three. -/
theorem seven_free (t : (types G).card=31) (h : (high G).card=30) (bad : bound G<gamma G) :
    G.CliqueFree 7 := by
  classical
  intro C cl
  let w := fun u => if nbr G u C≤2 then 2 else 1
  have low : ∑ _x∈C,2 ≤ ∑ x∈C,∑ u∈cubics G,(if G.Adj u x then w u else 0) :=
    sum_le_sum (fun x xc => two_contacts G cl t h bad x xc)
  rw [sum_comm] at low
  have upper : ∑ u∈cubics G,∑ x∈C,(if G.Adj u x then w u else 0) ≤ ∑ _u∈cubics G,4 := by
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
  have := cubic_cap G t h
  omega

end Graffiti384b.Cover31
#print axioms Graffiti384b.Cover31.adjacent
#print axioms Graffiti384b.Cover31.seven_free
