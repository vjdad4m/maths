import SixSingletonThreeCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

open private joinAcross from SixSingletonDarkOre189
open private two_local_counts from SixCutFar189
open private cannot_miss_two_on_seven from SixSingletonThreeCore189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_via_one_exception)

theorem small_dark_core_terminal_ore (D S : Finset V) (sub : S⊆D)
    (d6 : 6≤D.card) (d7 : D.card≤7) (s5 : 4≤S.card)
    (strict : ∀ z∈S,D.card-2≤(inside G D z).card)
    (other : ∀ z∈D,z∉S → 3≤(inside G D z).card)
    {x y : V} (xd : x∈D) (yd : y∈D) (xy : x≠y) :
    RouteOn G D x y := by
  classical
  let U := ↑(↑D : Set V)
  let J := G.induce (↑D : Set V)
  let A : Finset U := univ.filter (fun z=>z.val∈S)
  let B : Finset U := univ\A
  let H := joinAcross J A B
  have n : Fintype.card U=D.card := Fintype.card_coe D
  have ea (z : U) : z∈A ↔ z.val∈S := by simp [A]
  have eb (z : U) : z∈B ↔ z.val∉S := by simp [B,ea]
  have A5 : 4≤A.card := by
    have e : (S : Finset V).card=A.card := by
      apply card_bij (fun z zz=>(⟨z,sub zz⟩ : U))
      · intro z zz
        exact (ea _).mpr zz
      · intro z _ w _ h
        exact congrArg Subtype.val h
      · intro z za
        exact ⟨z.val,(ea _).mp za,rfl⟩
    omega
  have jA {u : U} (ua : u∈A) : D.card-2≤J.degree u := by
    rw [←inside_card_eq_degree_induce (G:=G) D u]
    exact strict u.val ((ea u).mp ua)
  have jB {u : U} (ub : u∈B) : 3≤J.degree u := by
    rw [←inside_card_eq_degree_induce (G:=G) D u]
    exact other u.val u.property ((eb u).mp ub)
  have incl : J≤H := fun _ _ h=>.inl h
  have closure_budget (u v : U) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    rcases uv with uv|⟨_,⟨ua,vb⟩|⟨va,ub⟩⟩
    · exact (no uv).elim
    · have i := jA ua
      have j := jB vb
      omega
    have i := jA va
    have j := jB ub
    omega
  have minH (u : U) : 4≤H.degree u := by
    by_cases ua : u∈A
    · have p := jA ua
      have w : J.neighborFinset u⊆H.neighborFinset u := fun _ h=>
        (mem_neighborFinset _ _ _).mpr (incl ((mem_neighborFinset _ _ _).mp h))
      have q := card_le_card w
      rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at q
      omega
    have ub : u∈B := mem_sdiff.mpr ⟨mem_univ _,ua⟩
    have ss : A⊆H.neighborFinset u := by
      intro v va
      exact (mem_neighborFinset _ _ _).mpr (.inr ⟨fun e=>ua (e.symm ▸ va),.inr ⟨va,ub⟩⟩)
    have p := card_le_card ss
    rw [card_neighborFinset_eq_degree] at p
    omega
  let x' : U := ⟨x,xd⟩
  let y' : U := ⟨y,yd⟩
  have xy' : x'≠y' := fun e=>xy (congrArg Subtype.val e)
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=H)
    (fun u v _ _=>by have u' := minH u; have v' := minH v; change Fintype.card U+1≤H.degree u+H.degree v; omega) xy'
  obtain ⟨q,qp,qs⟩ := terminal_ore_closure incl closure_budget p pp ps
  exact lift_side_path D q qp qs

private theorem at_least_four_after_dark_erase (D S : Finset V) {w : V}
    (hi : ∀ z∈S,5≤(inside G D z).card) :
    ∀ z∈S,4≤(inside G (D.erase w) z).card := by
  intro z zs
  have d := hi z zs
  have b := erase_internal_deg (G:=G) D w z
  omega

/-- In a four-strict / three-balanced dark block, a low balanced vertex
with a dark neighbor can be reached at the end of a spanning path
from some member of any specified two-vertex strict subset. -/
theorem dark_three_low_balance_end (D S L : Finset V)
    (sD : S⊆D) (lS : L⊆S) (l2 : 2≤L.card)
    (seven : D.card=7) (four : S.card=4)
    (hi : ∀ z∈S,5≤(inside G D z).card)
    {w : V} (wd : w∈D) (wn : w∉S) (low : (inside G D w).card≤2)
    (touch : ∃ z∈D,G.Adj w z) :
    ∃ l∈L,RouteOn G D l w := by
  classical
  let E := D.erase w
  let W := D\S
  have W3 : W.card=3 := by
    change (D\S).card=3
    rw [card_sdiff sD,seven,four]
  have wW : w∈W := mem_sdiff.mpr ⟨wd,wn⟩
  have w2 : (W.erase w).card=2 := by rw [card_erase_of_mem wW,W3]
  obtain ⟨p,q,pq,PQ⟩ := card_eq_two.mp w2
  have pe : p∈W.erase w := by rw [PQ]; simp
  have qe : q∈W.erase w := by rw [PQ]; simp
  have ⟨pw,pm⟩ := mem_erase.mp pe
  have ⟨qw,qm⟩ := mem_erase.mp qe
  have pd := (mem_sdiff.mp pm).1
  have qd := (mem_sdiff.mp qm).1
  have E6 : E.card=6 := by change (D.erase w).card=6; rw [card_erase_of_mem wd,seven]
  have sE : S⊆E := fun z zm=>mem_erase.mpr ⟨fun h=>wn (h ▸ zm),sD zm⟩
  let N (x : V) := S.filter (G.Adj x)
  have aSub : N w⊆inside G D w := fun z zm=>
    mem_filter.mpr ⟨sD (mem_filter.mp zm).1,(mem_filter.mp zm).2⟩
  have a2 : (N w).card≤2 := (card_le_card aSub).trans low
  have cover : N p∪N q=S := by
    apply Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _))
    intro z zs
    have pz : z≠p := fun h=>(mem_sdiff.mp pm).2 (h ▸ zs)
    have qz : z≠q := fun h=>(mem_sdiff.mp qm).2 (h ▸ zs)
    rcases cannot_miss_two_on_seven D seven (sD zs) pd qd pz qz pq (hi z zs) with e|e
    · exact mem_union_left _ (mem_filter.mpr ⟨zs,e.symm⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨zs,e.symm⟩)
  have meet : (S\N w)⊆N p∩N q := by
    intro z zm
    have ⟨zs,zn⟩ := mem_sdiff.mp zm
    have no : ¬G.Adj z w := fun h=>zn (mem_filter.mpr ⟨zs,h.symm⟩)
    have wz : z≠w := fun h=>wn (h ▸ zs)
    have pz : z≠p := fun h=>(mem_sdiff.mp pm).2 (h ▸ zs)
    have qz : z≠q := fun h=>(mem_sdiff.mp qm).2 (h ▸ zs)
    have h1 := (cannot_miss_two_on_seven D seven (sD zs) wd pd wz pz pw.symm (hi z zs)).resolve_left no
    have h2 := (cannot_miss_two_on_seven D seven (sD zs) wd qd wz qz qw.symm (hi z zs)).resolve_left no
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨zs,h1.symm⟩,mem_filter.mpr ⟨zs,h2.symm⟩⟩
  have csum := card_union_add_card_inter (N p) (N q)
  rw [cover,four] at csum
  have eCard : (S\N w).card=S.card-(N w).card := card_sdiff (filter_subset _ _)
  have ci := card_le_card meet
  rw [eCard,four] at ci
  have p4 : (N p).card≤4 := (card_le_card (filter_subset _ _)).trans (by omega)
  have q4 : (N q).card≤4 := (card_le_card (filter_subset _ _)).trans (by omega)
  have sp4 (z : V) (zs : z∈S) : 4≤(inside G E z).card :=
    at_least_four_after_dark_erase D S hi z zs
  have nSub (z : V) : N z⊆inside G E z :=
    fun v vm=>mem_filter.mpr ⟨sE (mem_filter.mp vm).1,(mem_filter.mp vm).2⟩
  have a6 (z : V) (ze : z∈E) (zn : z∉S) : z=p ∨ z=q := by
    have e : z∈W.erase w := mem_erase.mpr ⟨(mem_erase.mp ze).1,mem_sdiff.mpr ⟨(mem_erase.mp ze).2,zn⟩⟩
    rw [PQ] at e
    simpa using e
  have finish {l z : V} (ll : l∈L) (wz : G.Adj w z) (p' : RouteOn G E l z) :
      ∃ l∈L,RouteOn G D l w := by
    have h := p'.suffix wz.symm (show w∉E from not_mem_erase _ _)
    change RouteOn G (insert w (D.erase w)) l w at h
    rw [insert_erase wd] at h
    exact ⟨l,ll,h⟩
  have lowCase {u v : V} (ue : u∈E) (un : u∉S)
      (no : S\N w⊆N u) (sizeu : (N u).card=2) (sizev : (N v).card=4)
      (every : ∀ z∈E,z∉S → z=u ∨ z=v) :
      ∃ l∈L,RouteOn G D l w := by
    have nwu : (S\N w).card≤2 := (card_le_card no).trans (by omega)
    rw [eCard,four] at nwu
    have cw : (N w).card=2 := by omega
    have eq : S\N w=N u := eq_of_subset_of_card_le no (by
      rw [eCard,four,cw,sizeu])
    obtain ⟨z,zw⟩ := card_pos.mp (show 0<(N w).card by omega)
    have zs := (mem_filter.mp zw).1
    have wz := (mem_filter.mp zw).2
    have zU : z∉N u := fun h=>(mem_sdiff.mp (eq.symm ▸ h)).2 zw
    obtain ⟨l,ll,lz⟩ := exists_ne_of_one_lt_card (s:=L) (by omega) z
    have ls := lS ll
    obtain ⟨i,j,ij,Nu⟩ := card_eq_two.mp sizeu
    have iU : i∈N u := by rw [Nu]; simp
    have jU : j∈N u := by rw [Nu]; simp
    have ins (z : V) (zs : z∈S) : z∈E.erase u :=
      mem_erase.mpr ⟨fun e=>un (e ▸ zs),sE zs⟩
    have V4 (p : V) (pm : p∈E.erase u) : 4≤(inside G E p).card := by
      by_cases r : p∈S
      · exact sp4 p r
      rcases every p (mem_erase.mp pm).2 r with h|h
      · exact ((mem_erase.mp pm).1 h).elim
      subst p
      have b := card_le_card (nSub v)
      omega
    apply finish ll wz
    apply terminal_route_on_via_one_exception E ue (ins l ls) (ins z zs) lz
      (ins i (mem_filter.mp iU).1) (ins j (mem_filter.mp jU).1) ij
      (mem_filter.mp iU).2 (mem_filter.mp jU).2
    · rintro (⟨_,e⟩|⟨_,e⟩)
      · exact zU (e.symm ▸ jU)
      exact zU (e.symm ▸ iU)
    intro p pm q qm _ _
    have pp := V4 p pm
    have qq := V4 q qm
    omega
  by_cases ph : 3≤(inside G E p).card
  · by_cases qh : 3≤(inside G E q).card
    · obtain ⟨z,zd,wz⟩ := touch
      obtain ⟨l,ll,lz⟩ := exists_ne_of_one_lt_card (s:=L) (by omega) z
      apply finish ll wz
      apply small_dark_core_terminal_ore E S sE (by omega) (by omega) (by omega)
        (fun u um=>by have k := sp4 u um; omega) _ (sE (lS ll)) (mem_erase.mpr ⟨wz.ne.symm,zd⟩) lz
      intro u um un
      rcases a6 u um un with rfl|rfl
      · exact ph
      exact qh
    -- Exchange the two residual balances so that the low one is first.
    have pl : (N p).card=4 := by
      have q2 := card_le_card (nSub q)
      omega
    have rest : (N q).card=2 := by
      have q2 := card_le_card (nSub q)
      omega
    exact lowCase (u:=q) (v:=p) (mem_erase.mpr ⟨qw,qd⟩) (mem_sdiff.mp qm).2
      (fun z h=>(mem_inter.mp (meet h)).2) rest pl (fun z zm zn=>(a6 z zm zn).symm)
  -- The other orientation, with a low first residual balance.
  have rest : (N p).card=2 := by
    have p2 := card_le_card (nSub p)
    omega
  have ql : (N q).card=4 := by
    have p2 := card_le_card (nSub p)
    omega
  exact lowCase (u:=p) (v:=q) (mem_erase.mpr ⟨pw,pd⟩) (mem_sdiff.mp pm).2
    (fun z h=>(mem_inter.mp (meet h)).1) rest ql a6

#print axioms small_dark_core_terminal_ore
#print axioms dark_three_low_balance_end
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
