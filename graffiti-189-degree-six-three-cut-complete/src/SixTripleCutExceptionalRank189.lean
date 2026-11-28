import SixTripleCutExceptional189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189

theorem exceptional_other_port_rank_two
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (b4 : 4≤B.card) (c4 : 4≤C.card)
    (vb : (visible G S B).card=3)
    (bh : ∀ w∈B, 6≤G.degree w)
    {x l t : V} (lm : l∈A) (tl : G.Adj t l) (ts : t∈S)
    (ux : ∀ u∈S,G.Adj x u)
    (ct : C.card=(ports G C t).card+(localTwo G C t).card)
    (qa : 1≤(localTwo G A t).card) :
    ∃ y∈ports G B t, ∃ u∈S, u≠t ∧ G.Adj y u := by
  classical
  by_contra! deny
  obtain ⟨u,um⟩ := card_pos.mp (show 0<(S.erase t).card by rw [card_erase_of_mem ts,ss]; decide)
  obtain ⟨ut,us⟩ := mem_erase.mp um
  obtain ⟨v,vm⟩ := card_pos.mp (show 0<((S.erase t).erase u).card by
    rw [card_erase_of_mem um,card_erase_of_mem ts,ss]; decide)
  obtain ⟨vu,vm'⟩ := mem_erase.mp vm
  obtain ⟨vt,vs⟩ := mem_erase.mp vm'
  have uv : u≠v := Ne.symm vu
  -- The combined ports of the other two terminals use two of the three visible positions.
  let T := ports G B u ∪ ports G B v
  have t2 : 2≤T.card := shB.hall_two_terminals ss conn (by omega) us vs uv
  have dt : Disjoint (ports G B t) T := by
    apply disjoint_left.mpr
    intro y yp yt
    rcases mem_union.mp yt with hu|hv
    · exact deny y yp u us ut (mem_filter.mp hu).2.symm
    · exact deny y yp v vs vt (mem_filter.mp hv).2.symm
  have bound := card_le_card (union_subset
    (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=B) ts)
    (union_subset (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=B) us)
    (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=B) vs)))
  change ((ports G B t)∪T).card≤(visible G S B).card at bound
  rw [card_union_of_disjoint dt,vb] at bound
  obtain ⟨y,ym,ty⟩ := shB.hit ss conn ts
  have yp : y∈ports G B t := mem_filter.mpr ⟨ym,ty⟩
  have r1 : rank G S y=1 := by
    have eq : S.filter (G.Adj y)={t} := by
      ext w
      constructor
      · intro h
        obtain ⟨ws,yw⟩ := mem_filter.mp h
        by_cases e : w=t
        · exact mem_singleton.mpr e
        exact False.elim (deny y yp w ws e yw)
      · intro h
        have e := mem_singleton.mp h
        subst w
        exact mem_filter.mpr ⟨ts,ty.symm⟩
    simp [rank,eq]
  have cst := shB.port_cost_rank hc ts yp
  have high := bh y ym
  have qb : 5≤(localTwo G B t).card := by omega
  have lim := three_local_twos_le_six cap ab ac bc t
  have pc4 : 4≤(ports G C t).card := by omega
  have adjIn (w : V) (ws : w∈S) (wt : w≠t) : G.Adj t w := by
    by_contra no
    have wtwo := two_of_common hc (Ne.symm wt) no (ux t ts).symm (ux w ws)
    let D := localTwo G A t ∪ localTwo G B t
    have dw : w∉D := by
      intro h
      exact (mem_union.mp h).elim
        (fun ha=>disjoint_left.mp shA.disjoint (mem_inter.mp ha).1 ws)
        (fun hb=>disjoint_left.mp shB.disjoint (mem_inter.mp hb).1 ws)
    have incl : insert w D⊆DistanceTwo G t := insert_subset_iff.mpr
      ⟨wtwo,union_subset inter_subset_right inter_subset_right⟩
    have dis : Disjoint (localTwo G A t) (localTwo G B t) :=
      ab.mono inter_subset_left inter_subset_left
    have cost := (card_le_card incl).trans (distanceTwo_le_of_even 6 t (cap t))
    rw [card_insert_of_not_mem dw] at cost
    unfold D at cost
    rw [card_union_of_disjoint dis] at cost
    omega
  have cu : u∈DistanceTwo G y := two_of_common hc
    (fun e=>disjoint_left.mp shB.disjoint ym (e ▸ us)) (deny y yp u us ut) ty.symm (adjIn u us ut)
  have cv : v∈DistanceTwo G y := two_of_common hc
    (fun e=>disjoint_left.mp shB.disjoint ym (e ▸ vs)) (deny y yp v vs vt) ty.symm (adjIn v vs vt)
  have cl : l∈DistanceTwo G y := shB.foreign_distance_two shA ab.symm hc yp (mem_filter.mpr ⟨lm,tl⟩)
  have cc : ports G C t⊆DistanceTwo G y := fun _ hz=>shB.foreign_distance_two shC bc hc yp hz
  have lu : l≠u := fun e=>disjoint_left.mp shA.disjoint lm (e ▸ us)
  have lv : l≠v := fun e=>disjoint_left.mp shA.disjoint lm (e ▸ vs)
  have sub : ({l,u,v}:Finset V)⊆DistanceTwo G y := by simp [insert_subset_iff,cl,cu,cv]
  have dis : Disjoint ({l,u,v}:Finset V) (ports G C t) := by
    apply disjoint_left.mpr
    intro w hw wp
    have wc := (mem_filter.mp wp).1
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with h|h|h
    · exact disjoint_left.mp ac lm (h ▸ wc)
    · exact disjoint_left.mp shC.disjoint wc (h ▸ us)
    · exact disjoint_left.mp shC.disjoint wc (h ▸ vs)
  have lens : ({l,u,v}:Finset V).card=3 := by
    rw [card_insert_of_not_mem (by simp [lu,lv]),card_insert_of_not_mem (by simp [uv]),card_singleton]
  have cost := (card_le_card (union_subset sub cc)).trans (distanceTwo_le_of_even 6 y (cap y))
  rw [card_union_of_disjoint dis,lens] at cost
  omega

#print axioms exceptional_other_port_rank_two
end Graffiti189LongestPath.ThresholdSix.ThreeCut
