import SixSingletonFiveThreeActualExactOneLow189
import SixSingletonFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark strictA strictB singleton_neighborhood_exact from SixSingletonGeometry189
open private nearLeft nearRight nearBal deep mainCore shallow_partition strict_port_data_subclass deep_internal_degree
  from SixSingletonFiveGeometry189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem m5_dark_nonbalance_high
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) :
    ∀ z∈Dark D,z∉nearBal D → 5≤(inside G (Dark D) z).card := by
  classical
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨w,ws,aw⟩ := shore_hit_a ab.ne conn S
  obtain ⟨u,us,bu⟩ := shore_hit_b ab.ne conn S
  have sa : G.Adj a s := (show w=s by simpa only [sS,mem_singleton] using ws) ▸ aw
  have sb : G.Adj b s := (show u=s by simpa only [sS,mem_singleton] using us) ▸ bu
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS sa sb,
      card_insert_of_not_mem (by simpa using ab.ne),card_singleton]
  have hi (z : V) (zd : z∈Shore D) : 6≤G.degree z := by
    have ne : z≠s := fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ zd)
    exact (degree z s ne).resolve_right (by omega)
  have ⟨p,q,up⟩ :
      (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 ∧
      ∀ z∈Shore D,depth G a b z≤3 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
      ⟨_,x,y,h⟩|⟨m,_,_,_,_,_⟩
    · exact ⟨x,y,h⟩
    omega
  obtain ⟨x,xonly⟩ := card_eq_one.mp p
  obtain ⟨y,yonly⟩ := card_eq_one.mp q
  have L := strict_port_data_subclass hc xonly (nearLeft D) (filter_subset _ _)
    (fun z m=>(mem_filter.mp m).2) hi
  have swapDark : Dark (swapCut D)=Dark D := by
    simp only [Dark,Vis,shore_swapCut]
    congr 1
    ext z
    simp only [mem_filter]
    rw [or_comm (a:=G.Adj b z) (b:=G.Adj a z)]
  have R : (∀ z∈nearRight D,G.Adj y z) ∧
      (∀ z∈nearRight D,5≤(inside G (Dark D) z).card) := by
    have eq : nearLeft (swapCut D)=nearRight D := by
      unfold nearLeft nearRight strictA strictB
      rw [swapDark]
      simp only [depth,min_comm]
    have s := strict_port_data_subclass (a:=b) (b:=a) hc (D:=swapCut D) (x:=y)
      (by simpa only [aPorts,bPorts,shore_swapCut] using yonly) (nearLeft (swapCut D))
      (filter_subset _ _) (fun z m=>(mem_filter.mp m).2)
      (fun z m=>hi z (by simpa only [shore_swapCut] using m))
    simpa only [swapDark,eq] using s
  intro z zd zn
  have core : z∈mainCore D := (mem_union.mp ((shallow_partition hc D up).symm ▸ zd)).resolve_right zn
  rcases mem_union.mp core with lr|dp
  · exact (mem_union.mp lr).elim (L.2 z) (R.2 z)
  exact deep_internal_degree hc D dp (hi z (mem_sdiff.mp zd).1)

/-- The five-visible residual for the original graph now needs at least
two balanced vertices of dark degree at most three. -/
theorem traceable_of_adjacent_singleton_thirteen_five_unless_two_low
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5)
    (exception : (nearBal D).card=3 →
      ((nearBal D).filter (fun z=>(inside G (Dark D) z).card≤3)).card≤1) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases q3 : (nearBal D).card=3
  · let Bad := (nearBal D).filter (fun z=>(inside G (Dark D) z).card≤3)
    have cap : Bad.card≤1 := exception q3
    by_cases h : Bad.Nonempty
    · obtain ⟨z,zBad⟩ := h
      have ⟨zb,zlow⟩ := mem_filter.mp zBad
      apply traceable_of_adjacent_singleton_thirteen_five_three_balanced_exactly_one_low hc ab even conn degree
        sd cover one d13 v5 q3 zb zlow
      intro w wb wz
      by_contra low
      have wBad : w∈Bad := mem_filter.mpr ⟨wb,by omega⟩
      have u : ({w,z}:Finset V)⊆Bad := insert_subset wBad (singleton_subset_iff.mpr zBad)
      have q := card_le_card u
      rw [card_insert_of_not_mem (by simpa using wz),card_singleton] at q
      omega
    apply traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_dense hc ab even conn degree
      sd cover one d13 v5 q3
    intro z zd
    by_cases zb : z∈nearBal D
    · by_contra low
      exact h ⟨z,mem_filter.mpr ⟨zb,by omega⟩⟩
    exact (by decide : 4≤5).trans (m5_dark_nonbalance_high hc ab even conn degree sd cover one d13 v5 z zd zb)
  exact traceable_of_adjacent_singleton_thirteen_five_unless_three_sparse hc ab even conn degree
    sd cover one d13 v5 (fun p=>(q3 p).elim)

#print axioms traceable_of_adjacent_singleton_thirteen_five_unless_two_low
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
