import NinePrime180
import TwoMixed180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 800000
namespace Minimal180.PairRepair.Nine
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals

private theorem twice {a b c : Bool} (h : a≠b) (k : b≠c) : a=c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem thrice {a b c d : Bool} (h : a≠b) (k : b≠c) (l : c≠d) : a≠d := (twice h k) ▸ l

private theorem first_force (x : V) (xm : x∈C) (t : Bool) (ok : TerminalColor G 0 1 (C.erase x) t) : t=true := by
  obtain ⟨e,good,ea,eb⟩ := ok
  obtain ⟨u,um,au,ub⟩ := (show ∀ x∈C,∃ u∈C.erase x,G.Adj 0 u ∧ G.Adj u 1 by decide) x xm
  have eq := twice (good 0 (by simp) u (mem_union_right _ um) au) (good u (mem_union_right _ um) 1 (by simp) ub)
  exact eb.symm.trans (eq.symm.trans ea)

private theorem second_force (y : V) (ym : y∈D) (t : Bool) (ok : TerminalColor G 0 1 (D.erase y) t) : t=false := by
  obtain ⟨e,good,ea,eb⟩ := ok
  obtain ⟨u,um,v,vm,au,uv,vb⟩ := (show ∀ y∈D,∃ u∈D.erase y,∃ v∈D.erase y,
    G.Adj 0 u ∧ G.Adj u v ∧ G.Adj v 1 by decide) y ym
  have dif := thrice (good 0 (by simp) u (mem_union_right _ um) au)
    (good u (mem_union_right _ um) v (mem_union_right _ vm) uv) (good v (mem_union_right _ vm) 1 (by simp) vb)
  cases t <;> simp_all

/-- The sets of feasible terminal colors after one private deletion are
disjoint singleton sets. Both remainders have one neighbor of each color. -/
theorem opposite_signatures (t : Bool) :
    ((∃ x∈C,TerminalColor G 0 1 (C.erase x) t) ↔ t=true) ∧
    ((∃ y∈D,TerminalColor G 0 1 (D.erase y) t) ↔ t=false) := by
  constructor
  · constructor
    · rintro ⟨x,xm,ok⟩;exact first_force x xm t ok
    · rintro rfl
      let e (z : V) := decide (z∈({0,1}:Finset V))
      exact ⟨2,by decide,e,by unfold ProperOn;decide,by decide,by decide⟩
  · constructor
    · rintro ⟨y,ym,ok⟩;exact second_force y ym t ok
    · rintro rfl
      let e (z : V) := decide (z∈({0,6,7}:Finset V))
      exact ⟨4,by decide,e,by unfold ProperOn;decide,by decide,by decide⟩

theorem balanced : (G.neighborFinset 0∩C=({2,3}:Finset V)) ∧ (G.neighborFinset 0∩D=({4,5}:Finset V)) ∧
    (∀ c : V→Bool,ProperOn G (univ\({0,1}:Finset V)) c → c 2≠c 3 ∧ c 4≠c 5) ∧
    C∪D=univ\({0,1}:Finset V) ∧ Disjoint C D ∧ (∀ x∈C,∀ y∈D,¬G.Adj x y) := by
  refine ⟨by decide,by decide,fun c cp => ⟨cp 2 (by decide) 3 (by decide) (by decide),
    cp 4 (by decide) 5 (by decide) (by decide)⟩,by decide,by decide,by decide⟩

private theorem triangle (a x y : V) (ax : G.Adj a x) (xy : G.Adj x y) (ya : G.Adj y a)
    (Z : Finset V) (col : TwoColor G Z) (am : a∈Z) (xm : x∈Z) (ym : y∈Z) : False := by
  obtain ⟨e,ok⟩ := (color_function ..).mp col
  exact (ok y ym a am ya) (twice (ok a am x xm ax) (ok x xm y ym xy)).symm

theorem pinned_cost (Z : Finset V) (col : TwoColor G Z) (az : (0:V)∈Z) : 3≤Fintype.card V-Z.card := by
  by_contra! low
  have l : ¬TwoColor G (insert 0 C) := fun h => triangle 0 2 3 (by decide) (by decide) (by decide) _ h
    (by decide) (by decide) (by decide)
  have r : ¬TwoColor G (insert 0 D) := fun h => triangle 0 4 5 (by decide) (by decide) (by decide) _ h
    (by decide) (by decide) (by decide)
  obtain ⟨x,xc,y,yd,miss⟩ := forced_two_deletions G 0 C D Z (by decide) l r col az (by omega)
  have exactZ : univ\({x,y}:Finset V)=Z := by rw [←miss,Finset.sdiff_sdiff_eq_self (subset_univ Z)]
  obtain ⟨e,proper⟩ := (color_function ..).mp col
  have paint (S : Finset V) (sub : ({0,1}:Finset V)∪S⊆Z) : TerminalColor G 0 1 S (e 1==e 0) := by
    refine ⟨fun v => e v==e 0,?_,by simp,rfl⟩
    intro i im j jm ed
    have dif := proper i (sub im) j (sub jm) ed
    cases a : e i <;> cases b : e j <;> cases c : e 0 <;> simp_all
  have sub := (show ∀ i∈C,∀ j∈D,(({0,1}:Finset V)∪C.erase i⊆univ\({i,j}:Finset V)) ∧
    (({0,1}:Finset V)∪D.erase j⊆univ\({i,j}:Finset V)) by decide) x xc y yd
  rw [exactZ] at sub
  have yes := first_force x xc _ (paint _ sub.1)
  have no := second_force y yd _ (paint _ sub.2)
  exact Bool.noConfusion (yes.symm.trans no)

theorem rank_exact : bipartiteNum G=7 := by
  have low := size_bip G transversal
  have sz : (univ\({0,1}:Finset V)).card=7 := by decide
  rw [sz] at low
  obtain ⟨Z,col,eq⟩ := optB G
  have n : Fintype.card V=9 := by decide
  by_contra falseEq
  have large : 8≤Z.card := by omega
  by_cases zero : (0:V)∈Z
  · have cost := pinned_cost Z col zero;omega
  · have need (v : V) (v0 : v≠0) : v∈Z := by
      by_contra absent
      have sub : ({v,0}:Finset V)⊆univ\Z := insert_subset (mem_sdiff.mpr ⟨mem_univ _,absent⟩)
        (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _,zero⟩))
      have h := card_le_card sub
      rw [card_pair v0] at h
      have tot := card_sdiff_add_card_eq_card (subset_univ Z)
      rw [card_univ] at tot;omega
    exact triangle 1 2 3 (by decide) (by decide) (by decide) Z col
      (need 1 (by decide)) (need 2 (by decide)) (need 3 (by decide))

theorem slack_regression : Prime G ∧ G.Connected ∧ ¬G.Adj 0 1 ∧ G.degree 0=4 ∧
    (∀ v,¬DomEdge G 6 v) ∧ allowance G 6 false A=3 ∧ Protected G 6 false A ∧
    (∀ Z,TwoColor G Z → (0:V)∈Z → 3≤Fintype.card V-Z.card) ∧
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  have deg := (card_neighborFinset_eq_degree G 0).symm.trans (by decide : (G.neighborFinset 0).card=4)
  have rk : Fintype.card V≤bipartiteNum G+2 := by rw [rank_exact];decide
  refine ⟨prime,data.1,by decide,deg,by unfold DomEdge;decide,budget,?_,pinned_cost,
    ordinary_of_rooted G data.1 (RootEar.family_of_rank G data.1 (by decide) rk).rooted⟩
  apply (protected_iff G data.1 (by decide) 6 false A data.2.2.1).mpr
  refine ⟨_,three_deletions,?_,?_⟩
  · rw [data.2.1,data.2.2.2.2];decide
  · rw [budget];decide

#print axioms opposite_signatures
#print axioms balanced
#print axioms pinned_cost
#print axioms rank_exact
#print axioms slack_regression
end Minimal180.PairRepair.Nine
