import SixSingletonFiveThreeActualDense189
import SixEightHighCoreWeightedLow189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 k3 p5 from SixSingletonFiveShallowRoute189
open private cTag_mem kTag cTag_inj finite_plan sepKD from SixSingletonFivePairGeometry189
open private dark_core_five from SixSingletonFiveThreeBase189
open private erase_internal_deg from SixSingletonDarkOre189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem common_order (noniso : ∀ c∈K,∃ v∈K,G.Adj c v) :
    ∃ c m t : V, c≠m ∧ c≠t ∧ m≠t ∧ ({c,m,t}:Finset V)=K ∧ G.Adj c m ∧ G.Adj m t := by
  have s : ∀ v∈K,v=5 ∨ v=6 ∨ v=7 := by decide
  by_cases q : G.Adj 5 6
  · by_cases p : G.Adj 5 7
    · exact ⟨6,5,7,by decide,by decide,by decide,by decide,q.symm,p⟩
    obtain ⟨u,um,eu⟩ := noniso 7 (by decide)
    rcases s u um with rfl|rfl|rfl
    · exact (p eu.symm).elim
    · exact ⟨5,6,7,by decide,by decide,by decide,by decide,q,eu.symm⟩
    exact (G.loopless _ eu).elim
  obtain ⟨u,um,eu⟩ := noniso 5 (by decide)
  obtain ⟨v,vm,ev⟩ := noniso 6 (by decide)
  have u7 : u=7 := (s u um).resolve_left (fun h=>eu.ne h.symm) |>.resolve_left (fun h=>q (h ▸ eu))
  have v7 : v=7 := (s v vm).resolve_left (fun h=>q (h ▸ ev.symm)) |>.resolve_left (fun h=>ev.ne h.symm)
  exact ⟨5,7,6,by decide,by decide,by decide,by decide,u7 ▸ eu,v7 ▸ ev.symm⟩

private theorem low_visible_three {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (zd : z∈D) (low : (inside G D z).card≤3) :
    3≤(inside G P z).card := by
  have sub : G.neighborFinset z⊆inside G D z∪inside G P z := by
    intro v vm
    have j := (mem_neighborFinset _ _ _).mp vm
    exact (mem_union.mp (F.darkBounds z zd v j)).elim
      (fun m=>mem_union_left _ (mem_filter.mpr ⟨m,j⟩))
      (fun m=>mem_union_right _ (mem_filter.mpr ⟨m,j⟩))
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have k := card_union_le (inside G D z) (inside G P z)
  have j := F.darkHigh z zd
  omega

private theorem deep_hits_a_different_balance {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (_zm : z∈D\S) : ∃ w∈(D\S).erase z,G.Adj w T := by
  by_contra no
  have sub : inside G D T⊆(insert z S).erase T := by
    intro w wm
    have ⟨wd,tw⟩ := mem_filter.mp wm
    apply mem_erase.mpr
    refine ⟨tw.ne.symm,?_⟩
    by_cases wS : w∈S
    · exact mem_insert_of_mem wS
    by_cases wz : w=z
    · exact mem_insert.mpr (.inl wz)
    exact (no ⟨w,mem_erase.mpr ⟨wz,mem_sdiff.mpr ⟨wd,wS⟩⟩,tw.symm⟩).elim
  have h := card_le_card sub
  have tr : T∈insert z S := mem_insert_of_mem F.deepS
  have a := card_erase_add_one tr
  have b := card_insert_le z S
  have c := F.deep6
  have e := dark_core_five F
  omega

private theorem low_visible_port_cover {L R S : Finset V} {T z c m t : V}
    (F : ProfileThree G L R S T) (zd : z∈D) (low : (inside G D z).card≤3)
    (Ktag : ({c,m,t}:Finset V)=K) (zc : ¬G.Adj z c) (zt : ¬G.Adj z t) :
    ∀ p∈({x,y,m}:Finset V),G.Adj z p := by
  have sub : inside G P z⊆({x,y,m}:Finset V) := by
    intro p pm
    obtain ⟨pP,zp⟩ := mem_filter.mp pm
    change p∈insert x (insert y K) at pP
    rw [←Ktag] at pP
    simp only [mem_insert,mem_singleton] at pP ⊢
    rcases pP with rfl|rfl|rfl|rfl|rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact (zc zp).elim
    · exact .inr (.inr rfl)
    exact (zt zp).elim
  have e := eq_of_subset_of_card_le sub (by
    have i := card_insert_le x (insert y ({m}:Finset V))
    have j := card_insert_le y ({m}:Finset V)
    have k := low_visible_three F zd low
    rw [card_singleton] at j
    omega)
  intro p pm
  exact (mem_filter.mp (e.symm ▸ pm)).2

#print axioms common_order
#print axioms low_visible_three
#print axioms deep_hits_a_different_balance
#print axioms low_visible_port_cover
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
