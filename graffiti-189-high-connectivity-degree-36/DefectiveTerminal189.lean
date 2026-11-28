import DefectiveCharge189
import OneExceptionTerminal189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.DefectiveCharge Graffiti189LongestPath.OneExceptionTerminal
open private Graffiti189LongestPath.WideWing.terminalOre from WideWing189
set_option warningAsError true
namespace Graffiti189LongestPath.DefectiveTerminal
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If a large exact opposite shore is available, the absence of a
degree-tight high vertex makes the universal star Hamilton-connected even
with a single ambient degree exception, provided the star has order ≥8. -/
theorem defective_shore_routes_one_exception (hc : G.Connected) (d k : Nat) (A U B : Finset V)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (exactB : B.card≤k+1) (ab : Disjoint A B) (ub : Disjoint U B)
    (au : Disjoint A U) (large : k≤U.card)
    (closedA : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (closedU : ∀ x∈U,∀ y∉U,G.Adj x y → y∈B)
    (cap : ∀ v, (DistanceTwo G v).card≤d)
    {r : V} (root : ∀ v∈A, v=r ∨ G.Adj r v)
    (h8 : 9≤A.card) (lo : ∀ z∈A,d-2≤G.degree z)
    (hi : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (noTight : ∀ u : ↥(A : Set V), d≤G.degree u.val →
      A.card/2 < (G.induce (A : Set V)).degree u)
    {x y : V} (hx : x∈A) (hy : y∈A) (ne : x≠y) :
    ∃ q : G.Walk x y, q.IsPath ∧ (∀ w∈q.support,w∈A) ∧ q.length+1=A.card := by
  classical
  let J := G.induce (A : Set V)
  let X : ↥(A : Set V) := ⟨x,hx⟩
  let Y : ↥(A : Set V) := ⟨y,hy⟩
  have ne' : X≠Y := fun e => ne (congrArg Subtype.val e)
  have cardA : Fintype.card ↥(A : Set V)=A.card := Fintype.card_coe _
  have span : ∃ q : J.Walk X Y,q.IsPath ∧ ∀ v,v∈q.support := by
    by_cases low : ∃ z : ↥(A : Set V), G.degree z.val<d
    · obtain ⟨z,hz⟩ := low
      have low3 : 3≤J.degree z := by
        have e := (defective_universal_shore_charge hc d k A U B conn exactB ab ub au
          large closedA closedU cap root z)
        change A.card+G.degree z.val+_≤2*J.degree z+d+2 at e
        have l := lo z.val z.property
        omega
      apply terminal_ore_one_exception z low3 _ ne'
      intro u v n uz vz no
      have hu := (hi u.val z.val (fun e => uz (Subtype.ext e))).resolve_right (Nat.not_le_of_lt hz)
      have hv := (hi v.val z.val (fun e => vz (Subtype.ext e))).resolve_right (Nat.not_le_of_lt hz)
      have uu := noTight u hu
      have vv := noTight v hv
      change A.card/2<J.degree u at uu
      change A.card/2<J.degree v at vv
      omega
    apply Graffiti189LongestPath.WideWing.terminalOre (G:=J) _ ne'
    intro u v n no
    have u' : d≤G.degree u.val := Nat.le_of_not_gt (fun e => low ⟨u,e⟩)
    have v' : d≤G.degree v.val := Nat.le_of_not_gt (fun e => low ⟨v,e⟩)
    have uu := noTight u u'
    have vv := noTight v v'
    change A.card/2<J.degree u at uu
    change A.card/2<J.degree v at vv
    omega
  obtain ⟨q,hq,all⟩ := span
  let f : J →g G := ⟨Subtype.val,fun e => e⟩
  refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective hq,?_,?_⟩
  · intro z hz
    rw [support_map] at hz
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
    exact w.property
  · have es : q.support.toFinset = univ := ext fun w =>
      ⟨fun _ => mem_univ _,fun _ => List.mem_toFinset.mpr (all w)⟩
    have c := congrArg card es
    rw [List.toFinset_card_of_nodup hq.support_nodup,length_support,card_univ,cardA] at c
    simpa only [length_map] using c

#print axioms defective_shore_routes_one_exception
end Graffiti189LongestPath.DefectiveTerminal
