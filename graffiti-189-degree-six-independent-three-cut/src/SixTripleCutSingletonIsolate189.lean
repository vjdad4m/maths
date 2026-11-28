import SixTripleCutSingleton189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189

/-- If one shore is a singleton and one cut vertex is isolated within
the three-cut, its remaining shores have exactly two ports apiece,
each of which is adjacent to all three cut vertices. -/
theorem singleton_three_shore_isolated_terminal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3) {s t : V}
    (one : Shore G S ({s}:Finset V)) (shA : Shore G S A) (shB : Shore G S B)
    (sA : Disjoint ({s}:Finset V) A) (sB : Disjoint ({s}:Finset V) B) (ab : Disjoint A B)
    (ts : t∈S) (isolate : ∀ a∈S,a≠t → ¬G.Adj t a) :
    ((ports G A t).card=2 ∧ (localTwo G A t).card=2 ∧
      ∀ x∈ports G A t,∀ a∈S,G.Adj x a) ∧
    ((ports G B t).card=2 ∧ (localTwo G B t).card=2 ∧
      ∀ x∈ports G B t,∀ a∈S,G.Adj x a) := by
  classical
  obtain ⟨va,vb,da,db,coverA,coverB⟩ := singleton_pin_dark_geometry hc cap conn degree ss one shA shB sA sB ab
  have rs : s∈({s}:Finset V) := mem_singleton_self _
  have lo := one.degree_bound rs
  rw [card_singleton,ss] at lo
  have touch (a : V) (am : a∈S) : G.Adj s a := by
    obtain ⟨z,zm,az⟩ := one.hit ss conn am
    rw [mem_singleton.mp zm] at az
    exact az.symm
  have high {W : Finset V} (sw : Disjoint ({s}:Finset V) W) {x : V} (xm : x∈W) :
      6≤G.degree x := by
    have ne : x≠s := fun e=>disjoint_left.mp sw rs (e ▸ xm)
    exact (degree x s ne).resolve_right (by omega)
  let R := S.erase t
  let QA := localTwo G A t
  let QB := localTwo G B t
  have rsub : R⊆DistanceTwo G t := by
    intro x xm
    obtain ⟨xt,xs⟩ := mem_erase.mp xm
    exact two_of_common hc (Ne.symm xt) (isolate x xs xt) (touch t ts).symm (touch x xs)
  have qsub : QA∪QB⊆DistanceTwo G t := union_subset inter_subset_right inter_subset_right
  have dab : Disjoint QA QB := ab.mono inter_subset_left inter_subset_left
  have dis : Disjoint R (QA∪QB) := by
    apply disjoint_left.mpr
    intro z zm q
    have zz := (mem_erase.mp zm).2
    exact (mem_union.mp q).elim
      (fun x=>disjoint_left.mp shA.disjoint (mem_inter.mp x).1 zz)
      (fun x=>disjoint_left.mp shB.disjoint (mem_inter.mp x).1 zz)
  have combined := (card_le_card (union_subset rsub qsub)).trans (distanceTwo_le_of_even 6 t (cap t))
  rw [card_union_of_disjoint dis,card_union_of_disjoint dab,show R.card=2 by
    dsimp [R]; rw [card_erase_of_mem ts,ss]] at combined
  have small {W : Finset V} (sh : Shore G S W)
      (sw : Disjoint ({s}:Finset V) W) (v3 : (visible G S W).card=3) (d4 : 4≤(dark G S W).card)
      (cover : ∀ z∈dark G S W,∃ w∈visible G S W,G.Adj z w) :
      (ports G W t).card≤3 ∧ 1≤(localTwo G W t).card ∧
        ((ports G W t).card=3 → 4≤(localTwo G W t).card) := by
    have incl : ports G W t⊆visible G S W := fun z zm =>
      mem_filter.mpr ⟨(mem_filter.mp zm).1,t,ts,(mem_filter.mp zm).2.symm⟩
    have up := card_le_card incl
    rw [v3] at up
    obtain ⟨x,xm,tx⟩ := sh.hit ss conn ts
    have xp : x∈ports G W t := mem_filter.mpr ⟨xm,tx⟩
    have h := sh.port_cost hc ss ts xp
    have big := high sw xm
    refine ⟨up,by omega,?_⟩
    intro p3
    have eq : ports G W t=visible G S W := eq_of_subset_of_card_le incl (by rw [v3,p3])
    have c : dark G S W⊆localTwo G W t := by
      intro z zm
      obtain ⟨w,wm,zw⟩ := cover z zm
      have tw := (mem_filter.mp (eq.symm ▸ wm)).2
      have zn : t≠z := fun e=>disjoint_left.mp sh.disjoint (mem_sdiff.mp zm).1 (e ▸ ts)
      exact mem_inter.mpr ⟨(mem_sdiff.mp zm).1,two_of_common hc zn
        (fun e=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark zm ts e.symm) tw zw.symm⟩
    exact d4.trans (card_le_card c)
  obtain ⟨pa,qa,farA⟩ := small shA sA va da coverA
  obtain ⟨pb,qb,farB⟩ := small shB sB vb db coverB
  have pa2 : (ports G A t).card≤2 := by
    by_contra! h
    have l := farA (by omega)
    change 4≤QA.card at l
    change 1≤QB.card at qb
    omega
  have pb2 : (ports G B t).card≤2 := by
    by_contra! h
    have l := farB (by omega)
    change 4≤QB.card at l
    change 1≤QA.card at qa
    omega
  have qbig {W : Finset V} (sh : Shore G S W)
      (sw : Disjoint ({s}:Finset V) W) (p2 : (ports G W t).card≤2) :
      2≤(localTwo G W t).card := by
    obtain ⟨x,xm,tx⟩ := sh.hit ss conn ts
    have h := sh.port_cost hc ss ts (mem_filter.mpr ⟨xm,tx⟩)
    have big := high sw xm
    omega
  have a2 : QA.card=2 := by
    have x : 2≤QA.card := qbig shA sA pa2
    have y : 2≤QB.card := qbig shB sB pb2
    omega
  have b2 : QB.card=2 := by have y : 2≤QB.card := qbig shB sB pb2; omega
  have exactSide {W : Finset V} (sh : Shore G S W) (sw : Disjoint ({s}:Finset V) W)
      (p2 : (ports G W t).card≤2) (q2 : (localTwo G W t).card=2) :
      (ports G W t).card=2 ∧ (localTwo G W t).card=2 ∧
        ∀ x∈ports G W t,∀ a∈S,G.Adj x a := by
    have support (x : V) (xp : x∈ports G W t) :
        (ports G W t).card=2 ∧ rank G S x=3 := by
      have h := sh.port_cost_rank hc ts xp
      have big := high sw (mem_filter.mp xp).1
      have r : rank G S x≤3 := (card_le_card (filter_subset (G.Adj x) S)).trans (by omega)
      rw [q2] at h
      omega
    obtain ⟨x,xm,tx⟩ := sh.hit ss conn ts
    refine ⟨(support x (mem_filter.mpr ⟨xm,tx⟩)).1,q2,?_⟩
    intro y ym a am
    have e := (support y ym).2
    have eq : S.filter (G.Adj y)=S := eq_of_subset_of_card_le (filter_subset _ _) (by
      change S.card≤rank G S y
      rw [ss,e])
    exact (mem_filter.mp (eq.symm ▸ am)).2
  exact ⟨exactSide shA sA pa2 a2,exactSide shB sB pb2 b2⟩

/-- An independent three-cut cannot have a singleton shore and two
other shores in the degree-six #189 setting. -/
theorem no_independent_three_cut_singleton
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3) {s : V}
    (one : Shore G S ({s}:Finset V)) (shA : Shore G S A) (shB : Shore G S B)
    (sA : Disjoint ({s}:Finset V) A) (sB : Disjoint ({s}:Finset V) B) (ab : Disjoint A B)
    (independent : ∀ t∈S,∀ a∈S,a≠t → ¬G.Adj t a) : False := by
  classical
  obtain ⟨va,_,_,_,_,_⟩ := singleton_pin_dark_geometry hc cap conn degree ss one shA shB sA sB ab
  have data (t : V) (ts : t∈S) :=
    singleton_three_shore_isolated_terminal hc cap conn degree ss one shA shB sA sB ab ts (independent t ts)
  obtain ⟨a,am⟩ := card_pos.mp (show 0<S.card by omega)
  have vside : visible G S A⊆ports G A a := by
    intro x xm
    obtain ⟨xa,t,ts,xt⟩ := mem_filter.mp xm
    have xt' : x∈ports G A t := mem_filter.mpr ⟨xa,xt.symm⟩
    exact mem_filter.mpr ⟨xa,((data t ts).1.2.2 x xt' a am).symm⟩
  have l := card_le_card vside
  rw [va,(data a am).1.1] at l
  omega

#print axioms singleton_three_shore_isolated_terminal
#print axioms no_independent_three_cut_singleton
end Graffiti189LongestPath.ThresholdSix.ThreeCut
