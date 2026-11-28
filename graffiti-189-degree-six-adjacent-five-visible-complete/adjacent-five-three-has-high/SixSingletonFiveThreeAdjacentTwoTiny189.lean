import SixSingletonFiveThreeTwoLowMix189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
open private erase_internal_deg from SixSingletonDarkOre189
open private erase_avoids_nonneighbor from SixEightRemoveOneLow189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem sum_loss_at_most_one (S : Finset V) (z u v : V)
    (no : ¬(G.Adj u z ∧ G.Adj v z)) :
    (inside G S u).card+(inside G S v).card≤
      (inside G (S.erase z) u).card+(inside G (S.erase z) v).card+1 := by
  by_cases h : G.Adj u z
  · have hn : ¬G.Adj v z := fun v=>no ⟨h,v⟩
    rw [erase_avoids_nonneighbor (G:=G) S hn]
    have e := erase_internal_deg (G:=G) S z u
    omega
  rw [erase_avoids_nonneighbor (G:=G) S h]
  have e := erase_internal_deg (G:=G) S z v
  omega

private theorem paired_low_forbids_two (S : Finset V) {z w u v : V}
    (wS : w∈S) (uS : u∈S) (vS : v∈S) (zw : G.Adj z w)
    (uW : u≠w) (vW : v≠w) (uv : u≠v) (low : (inside G S z).card≤2) :
    ¬(G.Adj u z ∧ G.Adj v z) := by
  rintro ⟨uz,vz⟩
  have h : ({u,v,w}:Finset V)⊆inside G S z := insert_subset (mem_filter.mpr ⟨uS,uz.symm⟩)
    (insert_subset (mem_filter.mpr ⟨vS,vz.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨wS,zw⟩)))
  have k := card_le_card h
  rw [card_insert_of_not_mem (by simp [uv,uW]),card_insert_of_not_mem (by simp [vW]),card_singleton] at k
  omega

private theorem paired_tiny_core_ore {L R S : Finset V} {T z w h : V} (F : ProfileThree G L R S T)
    (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zh : z≠h) (wh : w≠h) (zw : G.Adj z w)
    (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤2)
    (h4 : 4≤(inside G D h).card) :
    ∀ u∈(D.erase z).erase w,∀ v∈(D.erase z).erase w,u≠v →
    7≤(inside G ((D.erase z).erase w) u).card+(inside G ((D.erase z).erase w) v).card := by
  have W : D\S={z,w,h} := by
    have sub : ({z,w,h}:Finset V)⊆D\S := insert_subset zm (insert_subset wm (singleton_subset_iff.mpr hm))
    apply (eq_of_subset_of_card_le sub ?_).symm
    rw [F.balance,card_insert_of_not_mem (by simp [zw.ne,zh]),card_insert_of_not_mem (by simp [wh]),card_singleton]
  have mark (u : V) (um : u∈(D.erase z).erase w) : u∈S ∨ u=h := by
    by_cases uS : u∈S
    · exact .inl uS
    have us : u∈D\S := mem_sdiff.mpr ⟨(mem_erase.mp (mem_erase.mp um).2).2,uS⟩
    rw [W,mem_insert,mem_insert,mem_singleton] at us
    exact .inr (us.resolve_left (mem_erase.mp (mem_erase.mp um).2).1 |>.resolve_left (mem_erase.mp um).1)
  intro u um v vm uv
  have ⟨uW,uZ,uD⟩ : u≠w ∧ u≠z ∧ u∈D := by simpa only [mem_erase] using um
  have ⟨vW,vZ,vD⟩ : v≠w ∧ v≠z ∧ v∈D := by simpa only [mem_erase] using vm
  have A := sum_loss_at_most_one D z u v
    (paired_low_forbids_two D (mem_sdiff.mp wm).1 uD vD zw uW vW uv zl)
  have B := sum_loss_at_most_one (D.erase z) w u v
    (paired_low_forbids_two D (mem_sdiff.mp zm).1 uD vD zw.symm uZ vZ uv wl)
  have base : 9≤(inside G D u).card+(inside G D v).card := by
    rcases mark u um with uS|ue <;> rcases mark v vm with vS|ve
    · have p := F.dark5 u uS; have q := F.dark5 v vS; omega
    · have p := F.dark5 u uS; subst v; omega
    · have q := F.dark5 v vS; subst u; omega
    exact (uv (ue.trans ve.symm)).elim
  omega

private theorem tiny_pair_splice {L R S : Finset V} {T z w n : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ i,(EvenFrom G i).card≤7)
    (zm : z∈D\S) (wm : w∈D\S) (zw : G.Adj z w) (wl : (inside G D w).card≤2)
    (nd : n∈(D.erase z).erase w) (nz : G.Adj n z)
    (ore : ∀ u∈(D.erase z).erase w,∀ v∈(D.erase z).erase w,u≠v →
      7≤(inside G ((D.erase z).erase w) u).card+(inside G ((D.erase z).erase w) v).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  let E := (D.erase z).erase w
  have wE : w∈D.erase z := mem_erase.mpr ⟨zw.ne.symm,(mem_sdiff.mp wm).1⟩
  have e6 : E.card=6 := by change ((D.erase z).erase w).card=6; rw [card_erase_of_mem wE,card_erase_of_mem (mem_sdiff.mp zm).1,d8]
  obtain ⟨l,lm,ln⟩ := exists_ne_of_one_lt_card (s:=L) (by rw [F.l2]; decide) n
  have lE : l∈E := mem_erase.mpr ⟨fun e=>(mem_sdiff.mp wm).2 (e ▸ F.left_sub lm),
    mem_erase.mpr ⟨fun e=>(mem_sdiff.mp zm).2 (e ▸ F.left_sub lm),F.core_sub (F.left_sub lm)⟩⟩
  have p : RouteOn G E l n := terminal_route_on_of_local_ore E lE nd ln
    (fun u um v vm uv _=>by rw [e6]; exact ore u um v vm uv)
  have p1 := p.suffix nz (fun m=>(mem_erase.mp (mem_erase.mp m).2).1 rfl)
  have p2 := p1.suffix zw (fun m=>(mem_insert.mp m).elim zw.ne.symm (fun m=>(mem_erase.mp m).1 rfl))
  have eq : insert w (insert z E)=D := by
    change insert w (insert z ((D.erase z).erase w))=D
    rw [insert_comm,insert_erase wE,insert_erase (mem_sdiff.mp zm).1]
  rw [eq] at p2
  obtain ⟨c,_,t,tm,q,wc⟩ := three_balance_low_can_exit F hc even wm (by omega)
  exact finish_by_balance p2 q F.sa F.ax (F.xL l lm) wc (F.commonB t tm).symm F.by'

#print axioms paired_tiny_core_ore
#print axioms tiny_pair_splice
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
