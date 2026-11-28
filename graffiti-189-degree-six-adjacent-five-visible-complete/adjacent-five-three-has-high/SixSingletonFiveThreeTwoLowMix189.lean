import SixSevenLopsidedSide189
import SixSingletonFiveThreeDarkThree189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
open private erase_internal_deg from SixSingletonDarkOre189
open private erase_avoids_nonneighbor from SixEightRemoveOneLow189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- One balance of degree at most two, one of degree three and one
of degree at least four can be routed by deleting the lowest first. -/
theorem three_balances_two_low_one_degree_three {L R S : Finset V} {T : V}
    (F : ProfileThree G L R S T) (hc : G.Connected)
    (even : ∀ i,(EvenFrom G i).card≤7)
    {z w h : V} (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zw : z≠w) (zh : z≠h) (wh : w≠h)
    (zl : (inside G D z).card≤2) (w3 : 3≤(inside G D w).card)
    (h4 : 4≤(inside G D h).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  have Dsplit : D\S={z,w,h} := by
    have sub : ({z,w,h}:Finset V)⊆D\S := insert_subset zm (insert_subset wm (singleton_subset_iff.mpr hm))
    apply (eq_of_subset_of_card_le sub ?_).symm
    rw [F.balance,card_insert_of_not_mem (by simp [zw,zh]),card_insert_of_not_mem (by simp [wh]),card_singleton]
  let E := D.erase z
  have zD := (mem_sdiff.mp zm).1
  have sE : S⊆E := fun u us=>mem_erase.mpr ⟨fun q=>(mem_sdiff.mp zm).2 (q ▸ us),F.core_sub us⟩
  have hE : h∈E := mem_erase.mpr ⟨zh.symm,(mem_sdiff.mp hm).1⟩
  have wE : w∈E := mem_erase.mpr ⟨zw.symm,(mem_sdiff.mp wm).1⟩
  have e7 : E.card=7 := by change (D.erase z).card=7; rw [card_erase_of_mem zD,d8]
  have loss (u : V) : (inside G D u).card≤(inside G E u).card+1 :=
    erase_internal_deg (G:=G) D z u
  have c4 (u : V) (um : u∈S) : 4≤(inside G E u).card := by
    have j := loss u
    have f := F.dark5 u um
    omega
  have h3 : 3≤(inside G E h).card := by have p := loss h; omega
  have w2 : 2≤(inside G E w).card := by have p := loss w; omega
  have w3if (edge : ¬G.Adj w z) : 3≤(inside G E w).card := by
    change 3≤(inside G (D.erase z) w).card
    rw [erase_avoids_nonneighbor (G:=G) D edge]
    exact w3
  have shape (u : V) (um : u∈E) : u∈S ∨ u=w ∨ u=h := by
    by_cases q : u∈S
    · exact .inl q
    have p : u∈D\S := mem_sdiff.mpr ⟨(mem_erase.mp um).2,q⟩
    rw [Dsplit,mem_insert,mem_insert,mem_singleton] at p
    exact .inr (p.resolve_left (mem_erase.mp um).1)
  have big :
      (∃ C : Finset V,C⊆E ∧ 4≤C.card ∧ ∀ u∈C,5≤(inside G E u).card) ∨
      (∃ C : Finset V,C⊆E ∧ C.card=6 ∧ ∀ u∈C,4≤(inside G E u).card) := by
    by_cases hn : 4≤(inside G E h).card
    · right
      refine ⟨insert h S,insert_subset hE sE,?_,?_⟩
      · rw [card_insert_of_not_mem (mem_sdiff.mp hm).2,dark_core_five F]
      · intro u um
        exact (mem_insert.mp um).elim (fun e=>e.symm ▸ hn) (c4 u)
    have edge : G.Adj z h := by
      by_contra no
      have eq := erase_avoids_nonneighbor (G:=G) D (fun h=>no h.symm)
      exact hn (eq.symm ▸ h4)
    let I := inside G D z
    have hI : h∈I := mem_filter.mpr ⟨(mem_sdiff.mp hm).1,edge⟩
    have sub : S∩I⊆I.erase h := by
      intro u um
      obtain ⟨us,ui⟩ := mem_inter.mp um
      exact mem_erase.mpr ⟨fun e=>(mem_sdiff.mp hm).2 (e ▸ us),ui⟩
    have d := card_le_card sub
    rw [card_erase_of_mem hI] at d
    have r := card_sdiff_add_card_inter S I
    have s5 := dark_core_five F
    have i2 : I.card≤2 := zl
    left
    refine ⟨S\I,(sdiff_subset : S\I⊆S).trans sE,by omega,?_⟩
    intro u um
    obtain ⟨us,un⟩ := mem_sdiff.mp um
    have no : ¬G.Adj u z := fun e=>un (mem_filter.mpr ⟨F.core_sub us,e.symm⟩)
    change 5≤(inside G (D.erase z) u).card
    rw [erase_avoids_nonneighbor (G:=G) D no]
    exact F.dark5 u us
  have tail_dark : ∃ q∈E, G.Adj q z ∧ 2≤(inside G E q).card ∧
      ∀ u∈E,u≠q → 3≤(inside G E u).card := by
    by_cases wz : G.Adj w z
    · refine ⟨w,wE,wz,w2,?_⟩
      intro u um uw
      rcases shape u um with p|p|p
      · exact (by decide : 3≤4).trans (c4 _ p)
      · exact (uw p).elim
      exact p.symm ▸ h3
    have hit : ∃ q∈E,G.Adj q z := by
      by_contra no
      have sub : G.neighborFinset z⊆P := by
        intro u um
        have j := (mem_neighborFinset _ _ _).mp um
        exact (mem_union.mp (F.darkBounds z zD u j)).resolve_left
          (fun uD=>no ⟨u,mem_erase.mpr ⟨j.ne.symm,uD⟩,j.symm⟩)
      have h := card_le_card sub
      rw [card_neighborFinset_eq_degree,p5] at h
      have j := F.darkHigh z zD
      omega
    obtain ⟨q,qm,qz⟩ := hit
    have all (u : V) (um : u∈E) : 3≤(inside G E u).card := by
      rcases shape u um with p|p|p
      · exact (by decide : 3≤4).trans (c4 _ p)
      · exact p.symm ▸ (w3if wz)
      exact p.symm ▸ h3
    exact ⟨q,qm,qz,(by decide : 2≤3).trans (all q qm),fun u um _=>all u um⟩
  obtain ⟨q,qm,qz,q2,others⟩ := tail_dark
  obtain ⟨l,lm,lq⟩ := exists_ne_of_one_lt_card (s:=L) (by rw [F.l2]; decide) q
  have p := seven_lopsided_side E e7 (sE (F.left_sub lm)) qm lq q2 others big
  have r := p.suffix qz (by simp [E])
  change RouteOn G (insert z (D.erase z)) l z at r
  rw [insert_erase zD] at r
  obtain ⟨c,cm,t,tm,cp,zc⟩ := three_balance_low_can_exit F hc even zm (by omega)
  exact finish_by_balance r cp F.sa F.ax (F.xL l lm) zc (F.commonB t tm).symm F.by'

#print axioms three_balances_two_low_one_degree_three
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
