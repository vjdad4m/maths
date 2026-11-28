import SixSingletonFiveThreeTinyComplete189
import SixRootAvoidTwo189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
open private sum_loss_at_most_one paired_low_forbids_two from SixSingletonFiveThreeAdjacentTwoTiny189
open private erase_internal_deg from SixSingletonDarkOre189
open private erase_avoids_nonneighbor from SixEightRemoveOneLow189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem full_inside_six {E : Finset V} (e6 : E.card=6)
    {u : V} (uE : u∈E) (u5 : 5≤(inside G E u).card) :
    ∀ v∈E,v≠u → G.Adj u v := by
  have sub : inside G E u⊆E.erase u := fun v vm=>mem_erase.mpr
    ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
  have eq := eq_of_subset_of_card_le sub (by rw [card_erase_of_mem uE,e6]; exact u5)
  intro v vm vu
  exact (mem_filter.mp (eq.symm ▸ mem_erase.mpr ⟨vu,vm⟩)).2

private theorem erased_pair_retains_six_ore {L R S : Finset V} {T z w h : V}
    (F : ProfileThree G L R S T) (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zw : z≠w) (zh : z≠h) (wh : w≠h)
    (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤2) (h4 : 4≤(inside G D h).card) :
    ∀ u∈(D.erase z).erase w,∀ v∈(D.erase z).erase w,u≠v →
      6≤(inside G ((D.erase z).erase w) u).card+(inside G ((D.erase z).erase w) v).card := by
  let E := (D.erase z).erase w
  have W : D\S={z,w,h} := by
    have sub : ({z,w,h}:Finset V)⊆D\S := insert_subset zm (insert_subset wm (singleton_subset_iff.mpr hm))
    apply (eq_of_subset_of_card_le sub ?_).symm
    rw [F.balance,card_insert_of_not_mem (by simp [zw,zh]),card_insert_of_not_mem (by simp [wh]),card_singleton]
  have wE : w∈D.erase z := mem_erase.mpr ⟨zw.symm,(mem_sdiff.mp wm).1⟩
  have e6 : E.card=6 := by
    change ((D.erase z).erase w).card=6
    rw [card_erase_of_mem wE,card_erase_of_mem (mem_sdiff.mp zm).1,d8]
  have ES : S⊆E := fun v vm=>mem_erase.mpr ⟨fun e=>(mem_sdiff.mp wm).2 (e ▸ vm),
    mem_erase.mpr ⟨fun e=>(mem_sdiff.mp zm).2 (e ▸ vm),F.core_sub vm⟩⟩
  have mark (u : V) (ue : u∈E) : u∈S ∨ u=h := by
    by_cases uS : u∈S
    · exact .inl uS
    have us : u∈D\S := mem_sdiff.mpr ⟨(mem_erase.mp (mem_erase.mp ue).2).2,uS⟩
    rw [W,mem_insert,mem_insert,mem_singleton] at us
    exact .inr (us.resolve_left (mem_erase.mp (mem_erase.mp ue).2).1 |>.resolve_left (mem_erase.mp ue).1)
  intro u um v vm uv
  change u∈E at um
  change v∈E at vm
  change 6≤(inside G E u).card+(inside G E v).card
  have old : 9≤(inside G D u).card+(inside G D v).card := by
    rcases mark u um with uS|ue <;> rcases mark v vm with vS|ve
    · have p := F.dark5 u uS; have q := F.dark5 v vS; omega
    · have p := F.dark5 u uS; subst v; omega
    · have q := F.dark5 v vS; subst u; omega
    exact (uv (ue.trans ve.symm)).elim
  have D2 (p : V) : (inside G D p).card≤(inside G E p).card+2 := by
    have o := erase_internal_deg (G:=G) D z p
    have k := erase_internal_deg (G:=G) (D.erase z) w p
    change (inside G (D.erase z) p).card≤(inside G E p).card+1 at k
    omega
  by_cases zBoth : G.Adj u z ∧ G.Adj v z
  · by_cases wBoth : G.Adj u w ∧ G.Adj v w
    · have uD := (mem_erase.mp (mem_erase.mp um).2).2
      have vD := (mem_erase.mp (mem_erase.mp vm).2).2
      have ex (m : V) (mu : G.Adj u m) (mv : G.Adj v m) (mb : (inside G D m).card≤2) :
          inside G D m=({u,v}:Finset V) := by
        have sub : ({u,v}:Finset V)⊆inside G D m :=
          insert_subset (mem_filter.mpr ⟨uD,mu.symm⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨vD,mv.symm⟩))
        apply (eq_of_subset_of_card_le sub ?_).symm
        rw [card_insert_of_not_mem (by simpa using uv),card_singleton]
        exact mb
      have ez := ex z zBoth.1 zBoth.2 zl
      have ew := ex w wBoth.1 wBoth.2 wl
      let M := (S.erase u).erase v
      have many : 3≤M.card := by
        have a := card_erase_le (s:=S.erase u) (a:=v)
        have b := card_erase_le (s:=S) (a:=u)
        have c : S.card≤(S.erase u).card+1 := by
          by_cases f : u∈S
          · exact (card_erase_add_one f).ge
          · rw [erase_eq_of_not_mem f]
            omega
        have d : (S.erase u).card≤M.card+1 := by
          change (S.erase u).card≤((S.erase u).erase v).card+1
          by_cases f : v∈S.erase u
          · exact (card_erase_add_one f).ge
          · rw [erase_eq_of_not_mem f]
            omega
        have p := dark_core_five F
        omega
      have hit (m : V) (mm : m∈M) : G.Adj u m ∧ G.Adj v m := by
        have ⟨mV,mU,mS⟩ : m≠v ∧ m≠u ∧ m∈S := by simpa only [M,mem_erase] using mm
        have noZ : ¬G.Adj m z := by
          intro e
          have r : m∈inside G D z := mem_filter.mpr ⟨F.core_sub mS,e.symm⟩
          rw [ez,mem_insert,mem_singleton] at r
          exact r.elim mU mV
        have noW : ¬G.Adj m w := by
          intro e
          have r : m∈inside G D w := mem_filter.mpr ⟨F.core_sub mS,e.symm⟩
          rw [ew,mem_insert,mem_singleton] at r
          exact r.elim mU mV
        have k : 5≤(inside G E m).card := by
          change 5≤(inside G ((D.erase z).erase w) m).card
          rw [erase_avoids_nonneighbor (G:=G) (D.erase z) noW,erase_avoids_nonneighbor (G:=G) D noZ]
          exact F.dark5 m mS
        have f := full_inside_six e6 (ES mS) k
        exact ⟨(f u um mU.symm).symm,(f v vm mV.symm).symm⟩
      have i := card_le_card (show M⊆inside G E u from fun p pm=>mem_filter.mpr
        ⟨ES (mem_erase.mp (mem_erase.mp pm).2).2,(hit p pm).1⟩)
      have j := card_le_card (show M⊆inside G E v from fun p pm=>mem_filter.mpr
        ⟨ES (mem_erase.mp (mem_erase.mp pm).2).2,(hit p pm).2⟩)
      omega
    have p := erase_internal_deg (G:=G) D z u
    have q := erase_internal_deg (G:=G) D z v
    have k := sum_loss_at_most_one (G:=G) (D.erase z) w u v wBoth
    change _≤(inside G E u).card+(inside G E v).card+1 at k
    omega
  have h0 := sum_loss_at_most_one (G:=G) D z u v zBoth
  have p := erase_internal_deg (G:=G) (D.erase z) w u
  have q := erase_internal_deg (G:=G) (D.erase z) w v
  change _≤(inside G E u).card+1 at p
  change _≤(inside G E v).card+1 at q
  omega

#print axioms erased_pair_retains_six_ore
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
