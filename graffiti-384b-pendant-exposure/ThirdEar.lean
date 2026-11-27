import WeightedExposure
namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor
open private FiniteRange.bad from FiniteRange384b
open private CliqueChoice.degree_neighbor from CliqueChoice384b
open private Remaining29.account from Remaining29
open private LowSample.two_degree from LowSample384b
open private Donor.rankDegree from PendantBudget
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem remove_kept (s : Finset V) {z : V} (degree : 2≤G.degree z)
    (keep : G.neighborFinset z⊆s) :
    deficient G (s.erase z)=deficient G s ∧
      ∀x∈deficient G s,nbr G x (s.erase z)=nbr G x s := by
  classical
  have ez : 2≤nbr G z (s.erase z) := degree.trans (by
    have inc : G.neighborFinset z⊆(s.erase z).filter (G.Adj z) := by
      intro y ym
      have zy := (G.mem_neighborFinset ..).mp ym
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨zy.ne.symm,keep ym⟩,zy⟩
    simpa [nbr] using card_le_card inc)
  have same {x : V} (out : x∉s) : nbr G x (s.erase z)=nbr G x s := by
    unfold nbr; congr 1; ext y
    simp only [mem_filter,mem_erase]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨fun eq => out (keep ((G.mem_neighborFinset ..).mpr (eq ▸ h.2.symm))),h.1⟩,h.2⟩⟩
  refine ⟨?_,fun _ m => same (mem_filter.mp m).2.1⟩
  ext x
  constructor
  · intro m
    obtain ⟨out,low⟩ := (mem_filter.mp m).2
    have xz : x≠z := fun eq => (Nat.not_le_of_lt low) (eq ▸ ez)
    have xs : x∉s := fun h => out (mem_erase.mpr ⟨xz,h⟩)
    exact mem_filter.mpr ⟨mem_univ _,xs,same xs ▸ low⟩
  · intro m
    obtain ⟨out,low⟩ := (mem_filter.mp m).2
    exact mem_filter.mpr ⟨mem_univ _,fun h => out ((erase_subset ..) h),(same out).trans_lt low⟩

/-- For the third ear, every trial hitting both of two selected pool vertices
works. The two selected vertices can include arbitrary padding if it has fewer
than two neighbors in the pool. -/
private theorem ear_events (X : Finset V) (sz : X.card=26) (z : V) (zd : G.degree z=2) :
    ∃T⊆X.powersetCard 10,T.card=735471 ∧ ∀k∈T,G.neighborFinset z∩X⊆k := by
  let N := G.neighborFinset z∩X
  have small : N.card≤2 := (card_le_card (show N⊆G.neighborFinset z from inter_subset_left)).trans (by simp [zd])
  obtain ⟨P,np,px,pc⟩ := exists_subsuperset_card_eq (show N⊆X from inter_subset_right) small (by omega)
  let T := (X.powersetCard 10).filter (fun k => (k∩P).card=2)
  have ct := RankStrata.hits X P px (show 2≤10 by decide)
  rw [pc,sz] at ct
  refine ⟨T,filter_subset ..,ct.trans (by decide),?_⟩
  intro k km
  have eq : k∩P=P := eq_of_subset_of_card_le inter_subset_right (by have := (mem_filter.mp km).2; omega)
  exact np.trans (eq ▸ inter_subset_left)

/-- Two separate savings can occur in the same sample: the third ear after
both its neighbors are retained, and an internal deficient pair. -/
theorem three_ear_budget (X : Finset V) (sz : X.card=26) (highX : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    {e z : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e)
    (zx : z∉X) (ze : z≠e) (ind : ¬G.Adj z e) (zd : G.degree z=2)
    (f : ℕ) (level : f=3 ∨ f=4) (degrees : ∀v∈X,f≤G.degree v)
    (Q : Finset (Finset V)) (valid : Usable G X Q)
    (paid : (if f=3 then 1211301 else 576606)<
      (exposed G X).card*170000+(∑v∈X,marked G X v)+Q.card) :
    gamma G≤Fintype.card V-15 := by
  classical
  by_contra! fail
  obtain ⟨T,ts,tc,good⟩ := ear_events G X sz z zd
  have enough := card_le_univ X
  have each (k : Finset V) (km : k∈X.powersetCard 10) :
      3+(active G X k).card+(if k∈Q then 1 else 0)+(if k∈T then 1 else 0)≤(FiniteRange.bad G X k).card := by
    obtain ⟨ks,kb⟩ := mem_powersetCard.mp km
    obtain ⟨s,desc,size,small,same⟩ := clean G X k ks inj ex outside degree
    let s' := if k∈T then s.erase z else s
    have validB : deficient G s' = deficient G s ∧
        (∀x∈deficient G s,nbr G x s'=nbr G x s) ∧ s'.card+(if k∈T then 1 else 0)=s.card := by
      by_cases event : k∈T
      · have keep : G.neighborFinset z⊆s := by
          intro y ym
          have zy := (G.mem_neighborFinset ..).mp ym
          have ya : y∉active G X k := by
            intro m
            have hi := (mem_filter.mp (highX (ks (mem_filter.mp m).1))).2
            have cmp := CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G (mem_filter.mp m).2.1) zy.symm
            omega
          rw [desc]
          apply mem_sdiff.mpr ⟨?_,by simp [(show y≠e from fun eq => ind (eq ▸ zy)),ya]⟩
          by_cases yx : y∈X
          · exact mem_union_right _ (good k event (mem_inter.mpr ⟨ym,yx⟩))
          · exact mem_union_left _ (mem_compl.mpr yx)
        have zs : z∈s := by
          rw [desc]
          exact mem_sdiff.mpr ⟨mem_union_left _ (mem_compl.mpr zx),fun m =>
            (mem_insert.mp m).elim ze (fun am => zx (ks (mem_filter.mp am).1))⟩
        obtain ⟨sameB,eq⟩ := remove_kept G s zd.ge keep
        simp only [s',if_pos event]
        exact ⟨sameB,eq,by have := card_erase_add_one zs; omega⟩
      · simp [s',event]
    have sizeB := card_le_card small
    by_cases event : k∈Q
    · obtain ⟨x,xb,y,yb,xy,one⟩ := valid.2 k event
      have translate (a : V) (ab : a∈FiniteRange.bad G X k) :
          a∉s' ∧ nbr G a s'=nbr G a (Xᶜ∪k) := by
        obtain ⟨out,eq⟩ := same a ab
        have am : a∈deficient G s := mem_filter.mpr ⟨mem_univ _,out,eq.trans_lt (mem_filter.mp ab).2⟩
        have oth : a∈deficient G s' := validB.1 ▸ am
        exact ⟨(mem_filter.mp oth).2.1,(validB.2.1 a am).trans eq⟩
      have win := pair_repair_saves G s' x y xy (translate x xb).1 (translate y yb).1 ((translate x xb).2.trans one)
        ((translate y yb).2.trans_lt (mem_filter.mp yb).2)
      change gamma G≤s'.card+(deficient G s').card-1 at win
      have mass := validB.2.2
      rw [validB.1] at win
      rw [if_pos event]
      omega
    · have win := batch_repair_saves G s' ∅ (empty_subset _) (by simp)
      change gamma G≤s'.card+(deficient G s').card-(∅ : Finset V).card at win
      simp only [validB.1,card_empty,Nat.sub_zero] at win
      have mass := validB.2.2
      rw [if_neg event]
      omega
  have lo := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_powersetCard,sz,sum_boole,Nat.cast_id,
    filter_mem_eq_inter,inter_eq_right.mpr valid.1,inter_eq_right.mpr ts,tc] at lo
  have hi := rank_budget G X sz inj pos f 170000 (by decide) (by omega) degrees
  have tab : (∑i∈range 26,envelope f 170000 i)=26*base+(if f=3 then 17881977 else 17247282) := by
    rcases level with rfl|rfl <;> unfold envelope charge reward base Donor.rankDegree FiniteRange.badCount <;>
      simp only [Nat.choose_eq_fast_choose] <;> decide
  rw [tab] at hi
  rw [show (26:ℕ).choose 10=5311735 by decide] at lo
  split_ifs at * <;> omega

def ThirdGeometry (X : Finset V) : Prop :=
  let n := (exposed G X).card
  (8≤n ∨ 6≤n ∧ LowFeature G X 5 ∨ 4≤n ∧ LowFeature G X 4) ∨
  (∀x∈X,4≤G.degree x) ∧ (4≤n ∨ 2≤n ∧ LowFeature G X 5 ∨ 1≤n ∧ LowFeature G X 4) ∨
  (∀x∈X,5≤G.degree x)

open private via_feature from PendantBounds

/-- At 30 or more nonleaves the ear and its low mate occupy at most two
of the at least three degree-two positions. At 29 nonleaves, a leaf mate
occupies none of the other degree-two positions. -/
theorem three_low_mate (t : (types G).card=29) (h : (high G).card=27)
    {e w v : V} (q : 30≤(nonleaves G).card ∨ 29≤(nonleaves G).card ∧ G.degree v<2) (wh : w∈high G) (wv : w≠v) (neigh : G.neighborFinset e={w,v}) (low : G.degree v≤2)
    (geo : ThirdGeometry G ((high G).erase w)) : gamma G≤Fintype.card V-15 := by
  classical
  let X := (high G).erase w
  let n := (exposed G X).card
  have sz : X.card=26 := by rw [show X=(high G).erase w from rfl,card_erase_of_mem wh,h]
  have sub : X⊆high G := erase_subset ..
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,neigh,card_pair wv]
  have out {a : V} (d : G.degree a≤2) : a∉X := fun am => by have hi := (mem_filter.mp (sub am)).2; omega
  have exterior (x : V) (xm : x∈X) : ¬G.Adj e x := by
    intro adj
    have hh := (G.mem_neighborFinset ..).mpr adj
    rw [neigh,mem_insert,mem_singleton] at hh
    exact hh.elim (mem_erase.mp xm).1 (fun eq => out low (eq ▸ xm))
  have acc := Remaining29.account G
  have es := card_insert_le e ({v}:Finset V)
  rw [card_singleton] at es
  obtain ⟨z,zt,zaway⟩ : ∃z∈LowSample.twos G,z∉({e,v}:Finset V) := by
    rcases q with many|⟨two,leaf⟩
    · exact exists_mem_not_mem_of_card_lt_card (show ({e,v}:Finset V).card<(LowSample.twos G).card by omega)
    · obtain ⟨z,zt,ne⟩ := exists_mem_not_mem_of_card_lt_card (show ({e}:Finset V).card<(LowSample.twos G).card by rw [card_singleton]; omega)
      have d := LowSample.two_degree G zt
      have zv : z≠v := fun eq => by rw [eq] at d; omega
      exact ⟨z,zt,by simpa only [mem_insert,mem_singleton,not_or] using And.intro (fun eq => ne (mem_singleton.mpr eq)) zv⟩
  have zd := LowSample.two_degree G zt
  have ze : z≠e := fun eq => zaway (eq ▸ mem_insert_self ..)
  have zv : z≠v := fun eq => zaway (mem_insert_of_mem (mem_singleton.mpr eq))
  have zw : z≠w := fun eq => by have := (mem_filter.mp wh).2; rw [eq] at zd; omega
  have ind : ¬G.Adj z e := by
    intro adj
    have hh := (G.mem_neighborFinset ..).mpr adj.symm
    rw [neigh,mem_insert,mem_singleton] at hh
    exact hh.elim zw zv
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  have pos (x : V) (xm : x∈X) := rich x (sub xm)
  have q0 : Usable G X ∅ := ⟨empty_subset _,by simp⟩
  have win := three_ear_budget G X sz sub (inj.mono sub) pos (out de.le) exterior de.ge (out zd.le) ze ind zd
  rcases geo with cases|⟨deg,cases⟩|deg
  · have h3 (x : V) (xm : x∈X) : 3≤G.degree x := (mem_filter.mp (sub xm)).2
    rcases cases with eight|⟨six,low'⟩|⟨four,low'⟩
    · apply win 3 (by decide) h3 ∅ q0
      change 1211301<n*170000+(∑v∈X,marked G X v)+0; change 8≤n at eight; omega
    · obtain ⟨Q,vQ,ct⟩ := via_feature G X sz sub 5 (by decide) low'
      apply win 3 (by decide) h3 Q vQ
      change 251680≤(∑v∈X,marked G X v)+Q.card at ct
      change 1211301<n*170000+(∑v∈X,marked G X v)+Q.card; change 6≤n at six; omega
    · obtain ⟨Q,vQ,ct⟩ := via_feature G X sz sub 4 (by decide) low'
      apply win 3 (by decide) h3 Q vQ
      change 539682≤(∑v∈X,marked G X v)+Q.card at ct
      change 1211301<n*170000+(∑v∈X,marked G X v)+Q.card; change 4≤n at four; omega
  · rcases cases with four|⟨two,low'⟩|⟨one,low'⟩
    · apply win 4 (by decide) deg ∅ q0
      change 576606<n*170000+(∑v∈X,marked G X v)+0; change 4≤n at four; omega
    · obtain ⟨Q,vQ,ct⟩ := via_feature G X sz sub 5 (by decide) low'
      apply win 4 (by decide) deg Q vQ
      change 251680≤(∑v∈X,marked G X v)+Q.card at ct
      change 576606<n*170000+(∑v∈X,marked G X v)+Q.card; change 2≤n at two; omega
    · obtain ⟨Q,vQ,ct⟩ := via_feature G X sz sub 4 (by decide) low'
      apply win 4 (by decide) deg Q vQ
      change 539682≤(∑v∈X,marked G X v)+Q.card at ct
      change 576606<n*170000+(∑v∈X,marked G X v)+Q.card; change 1≤n at one; omega
  · exact low_mate G t h wh wv neigh low (Or.inr (Or.inr deg))

/-- At the 30-nonleaf quota, a quartic internal edge (or an exposed
quartic) suffices when the pool has no cubic vertex. A high neighbor of the
root supplies at least one exposure automatically. -/
theorem thirty_quartic (t : (types G).card=29) (h : (high G).card=27) (q : (nonleaves G).card=30)
    {e w v : V} (wh : w∈high G) (wv : w≠v) (neigh : G.neighborFinset e={w,v}) (low : G.degree v≤2)
    (floor : ∀x∈(high G).erase w,4≤G.degree x) (feature : LowFeature G ((high G).erase w) 4) :
    gamma G≤Fintype.card V-15 := by
  apply three_low_mate G t h (Or.inl q.ge) wh wv neigh low
  refine Or.inr (Or.inl ⟨floor,Or.inr (Or.inr ⟨?_,feature⟩)⟩)
  have score := (Repair.maximal_diversity G (show (types G).card=(high G).card+2 by omega)).2.1 w wh
  have count := Remaining29.account G
  obtain ⟨a,ah,wa⟩ : ∃a∈high G,G.Adj w a := by
    by_contra! no
    have cap := low_neighbors G w no
    omega
  exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_erase.mpr ⟨wa.ne.symm,ah⟩,w,not_mem_erase w _,wa.symm⟩⟩

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.three_ear_budget
#print axioms Graffiti384b.PendantRank.three_low_mate
#print axioms Graffiti384b.PendantRank.thirty_quartic
