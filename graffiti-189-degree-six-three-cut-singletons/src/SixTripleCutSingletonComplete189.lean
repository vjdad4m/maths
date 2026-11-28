import SixTripleCutDarkPressure189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_visible_sum from SixTripleCutForeignHigh189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports from SixTripleCutUniversalPort189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189

/-- A three-separator at threshold six cannot have a singleton shore
and two other shores, regardless of edges inside the cut. -/
theorem no_three_shores_one_singleton
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3) {s : V}
    (one : Shore G S ({s}:Finset V)) (shA : Shore G S A) (shB : Shore G S B)
    (sA : Disjoint ({s}:Finset V) A) (sB : Disjoint ({s}:Finset V) B) (ab : Disjoint A B) :
    False := by
  classical
  obtain ⟨va,vb,da,db,coverA,coverB⟩ := singleton_pin_dark_geometry hc cap conn degree ss one shA shB sA sB ab
  have ss' : s∈({s}:Finset V) := mem_singleton_self _
  have lo := one.degree_bound ss'
  rw [card_singleton,ss] at lo
  have sp (t : V) (ts : t∈S) : G.Adj t s := by
    obtain ⟨x,xm,e⟩ := one.hit ss conn ts
    rwa [mem_singleton.mp xm] at e
  have high {W : Finset V} (sw : Disjoint ({s}:Finset V) W) {x : V} (xm : x∈W) :
      6≤G.degree x := by
    have ne : x≠s := fun e=>disjoint_left.mp sw ss' (e ▸ xm)
    exact (degree x s ne).resolve_right (by omega)
  have has_cut {W : Finset V} {t : V} (ts : t∈S) : ports G W t⊆visible G S W :=
    Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible ts
  have local_cap {W Z : Finset V} (shW : Shore G S W) (shZ : Shore G S Z)
      (sw : Disjoint ({s}:Finset V) W) (sz : Disjoint ({s}:Finset V) Z) (wz : Disjoint W Z)
      (vz : (visible G S Z).card=3) {t x : V} (ts : t∈S) (xp : x∈ports G W t)
      (fore : visible G S Z⊆DistanceTwo G x) : (localTwo G W x).card≤2 := by
    let F := insert s (visible G S Z)
    have off : s∉visible G S Z := fun p=>disjoint_left.mp sz ss' (mem_filter.mp p).1
    have size : F.card=4 := by dsimp only [F]; rw [card_insert_of_not_mem off,vz]
    have sub : F⊆DistanceTwo G x := insert_subset
      (shW.foreign_distance_two one sw.symm hc xp (mem_filter.mpr ⟨ss',sp t ts⟩)) fore
    have d : Disjoint F (localTwo G W x) := by
      apply disjoint_left.mpr
      intro y yf yw
      have ww := (mem_inter.mp yw).1
      rcases mem_insert.mp yf with h|h
      · exact disjoint_left.mp sw ss' (h ▸ ww)
      · exact disjoint_left.mp wz ww (mem_filter.mp h).1
    have u := (card_le_card (show F∪localTwo G W x⊆DistanceTwo G x from union_subset sub inter_subset_right)).trans
      (distanceTwo_le_of_even 6 x (cap x))
    rw [card_union_of_disjoint d,size] at u
    omega
  have price {W Z : Finset V}
      (shW : Shore G S W) (shZ : Shore G S Z)
      (sw : Disjoint ({s}:Finset V) W) (sz : Disjoint ({s}:Finset V) Z) (wz : Disjoint W Z)
      (vw : (visible G S W).card=3) (vz : (visible G S Z).card=3)
      {t : V} (ts : t∈S) :
      5≤(ports G W t).card+(localTwo G W t).card := by
    obtain ⟨x,xw,tx⟩ := shW.hit ss conn ts
    have xp : x∈ports G W t := mem_filter.mpr ⟨xw,tx⟩
    have pc := shW.port_cost_rank hc ts xp
    have xh := high sw xw
    by_cases miss : ∃ a∈S,¬G.Adj x a
    · obtain ⟨a,as',ha⟩ := miss
      have r := rank_le_two_of_missing ss as' ha
      omega
    have un (a : V) (am : a∈S) : G.Adj x a := by
      by_cases h : G.Adj x a
      · exact h
      exfalso
      exact miss ⟨a,am,h⟩
    have r3 : rank G S x=3 := by
      unfold rank
      rw [filter_eq_self.mpr un,ss]
    have f := shW.foreign_visible_of_universal shZ wz hc xw un
    have here := local_cap shW shZ sw sz wz vz ts xp f
    obtain ⟨y,yd,xy⟩ := shW.dark_neighbor_of_high_visible ss vw (has_cut ts xp) xh
    have b := shW.dark_neighbor_degree_bound hc yd xy
    have big := high sw (mem_sdiff.mp yd).1
    have sum := shW.degree_eq_inner_add_rank xw
    omega
  have q4 {W : Finset V} (sh : Shore G S W)
      (v3 : (visible G S W).card=3) (d4 : 4≤(dark G S W).card)
      (cover : ∀ y∈dark G S W,∃ x∈visible G S W,G.Adj y x)
      {t : V} (ts : t∈S) (p3 : (ports G W t).card=3) : 4≤(localTwo G W t).card := by
    have eq : ports G W t=visible G S W :=
      eq_of_subset_of_card_le (has_cut ts) (by rw [v3,p3])
    apply d4.trans
    apply card_le_card
    intro y yd
    obtain ⟨x,xm,yx⟩ := cover y yd
    have xp : x∈ports G W t := by rwa [eq]
    have yw := (mem_sdiff.mp yd).1
    have ne : t≠y := fun e=>disjoint_left.mp sh.disjoint yw (e ▸ ts)
    have na : ¬G.Adj t y := fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark yd ts h.symm
    exact mem_inter.mpr ⟨yw,two_of_common hc ne na (mem_filter.mp xp).2 yx.symm⟩
  have data (t : V) (ts : t∈S) :
      (ports G A t).card=2 ∧ (ports G B t).card=2 ∧
      (localTwo G A t).card=3 ∧ (localTwo G B t).card=3 := by
    let pa := (ports G A t).card
    let pb := (ports G B t).card
    let qa := (localTwo G A t).card
    let qb := (localTwo G B t).card
    have pa3 : pa≤3 := (card_le_card (has_cut (W:=A) ts)).trans va.le
    have pb3 : pb≤3 := (card_le_card (has_cut (W:=B) ts)).trans vb.le
    have ca : 5≤pa+qa := price shA shB sA sB ab va vb ts
    have cb : 5≤pb+qb := price shB shA sB sA ab.symm vb va ts
    have u : localTwo G A t∪localTwo G B t⊆DistanceTwo G t := union_subset inter_subset_right inter_subset_right
    have total := (card_le_card u).trans (distanceTwo_le_of_even 6 t (cap t))
    have dis : Disjoint (localTwo G A t) (localTwo G B t) := ab.mono inter_subset_left inter_subset_left
    rw [card_union_of_disjoint dis] at total
    change qa+qb≤6 at total
    have pa2 : pa≤2 := by
      by_contra! h
      have g : pa=3 := by omega
      have a := q4 shA va da coverA ts g
      have k : 4≤qa := a
      have l : pb=3 := by omega
      have z : 4≤qb := q4 shB vb db coverB ts l
      omega
    have pb2 : pb≤2 := by
      by_contra! h
      have l : pb=3 := by omega
      have z : 4≤qb := q4 shB vb db coverB ts l
      omega
    change pa=2 ∧ pb=2 ∧ qa=3 ∧ qb=3
    omega
  have complete (t : V) (ts : t∈S) (a : V) (as' : a∈S) (ta : t≠a) : G.Adj t a := by
    by_cases h : G.Adj t a
    · exact h
    exfalso
    let D := localTwo G A t∪localTwo G B t
    have size : D.card=6 := by
      change (localTwo G A t∪localTwo G B t).card=6
      have dis : Disjoint (localTwo G A t) (localTwo G B t) := ab.mono inter_subset_left inter_subset_left
      rw [card_union_of_disjoint dis,(data t ts).2.2.1,(data t ts).2.2.2]
    have off : a∉D := fun d=>(mem_union.mp d).elim
      (fun al=>disjoint_left.mp shA.disjoint (mem_inter.mp al).1 as')
      (fun bl=>disjoint_left.mp shB.disjoint (mem_inter.mp bl).1 as')
    have sub : insert a D⊆DistanceTwo G t := insert_subset (two_of_common hc ta h (sp t ts) (sp a as').symm)
      (union_subset inter_subset_right inter_subset_right)
    have c := (card_le_card sub).trans (distanceTwo_le_of_even 6 t (cap t))
    rw [card_insert_of_not_mem off,size] at c
    omega
  have ranks {W : Finset V} (sh : Shore G S W) (sw : Disjoint ({s}:Finset V) W)
      (v3 : (visible G S W).card=3)
      (p2 : ∀ t∈S,(ports G W t).card=2) (q3 : ∀ t∈S,(localTwo G W t).card=3) :
      ∀ x∈visible G S W,rank G S x=2 := by
    have base (x : V) (xm : x∈visible G S W) : 2≤rank G S x := by
      obtain ⟨xw,t,ts,xt⟩ := mem_filter.mp xm
      have cost := sh.port_cost_rank hc ts (mem_filter.mpr ⟨xw,xt.symm⟩)
      have hh := high sw xw
      rw [p2 t ts,q3 t ts] at cost
      omega
    have eq : (∑ t∈S,(ports G W t).card)=∑ _t∈S,(2:Nat) :=
      sum_congr rfl p2
    simp [ss] at eq
    intro x xm
    let E := (visible G S W).erase x
    have e2 : E.card=2 := by dsimp [E]; rw [card_erase_of_mem xm,v3]
    have lo := sum_le_sum (s:=E) (f:=fun _=>(2:Nat)) (g:=rank G S)
      (fun y ym=>base y (mem_erase.mp ym).2)
    have c : (∑ _∈E,(2:Nat))=4 := by simp [e2]
    rw [c] at lo
    have tot := sum_erase_add (visible G S W) (rank G S) xm
    rw [Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_visible_sum,
      Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports S W,eq] at tot
    change (∑ t∈E,rank G S t)+rank G S x=6 at tot
    change 4≤(∑ t∈E,rank G S t) at lo
    have b := base x xm
    omega
  have ra := ranks shA sA va (fun t ts=>(data t ts).1) (fun t ts=>(data t ts).2.2.1)
  have rb := ranks shB sB vb (fun t ts=>(data t ts).2.1) (fun t ts=>(data t ts).2.2.2)
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(visible G S A).card by omega)
  obtain ⟨xa,t,ts,xt⟩ := mem_filter.mp xm
  have xp : x∈ports G A t := mem_filter.mpr ⟨xa,xt.symm⟩
  have foreign : visible G S B⊆DistanceTwo G x := by
    intro y ym
    obtain ⟨a,as',ax,ay⟩ := rank_full_of_two_intersect ss (ra x xm).ge (rb y ym).ge
    exact shA.foreign_distance_two shB ab hc (mem_filter.mpr ⟨xa,ax.symm⟩)
      (mem_filter.mpr ⟨(mem_filter.mp ym).1,ay.symm⟩)
  have missing : ∃ a∈S,¬G.Adj x a := by
    by_cases yes : ∃ a∈S,¬G.Adj x a
    · exact yes
    exfalso
    have all (a : V) (am : a∈S) : G.Adj x a := by
      by_cases h : G.Adj x a
      · exact h
      exfalso
      exact yes ⟨a,am,h⟩
    have r := ra x xm
    unfold rank at r
    rw [filter_eq_self.mpr all,ss] at r
    omega
  obtain ⟨w,ws,xw⟩ := missing
  let F := insert s (visible G S B)
  have f4 : F.card=4 := by
    have off : s∉visible G S B := fun m=>disjoint_left.mp sB ss' (mem_filter.mp m).1
    change (insert s (visible G S B)).card=4
    rw [card_insert_of_not_mem off,vb]
  have wo : w∉F := by
    intro h
    rcases mem_insert.mp h with e|m
    · exact disjoint_left.mp one.disjoint (e ▸ mem_singleton_self s) ws
    · exact disjoint_left.mp shB.disjoint (mem_filter.mp m).1 ws
  have w2 : w∈DistanceTwo G x := two_of_common hc
    (fun e=>disjoint_left.mp shA.disjoint xa (e ▸ ws)) xw xt
    (complete t ts w ws (fun e=>xw (e ▸ xt)))
  have sub : insert w F⊆DistanceTwo G x := insert_subset w2 (insert_subset
    (shA.foreign_distance_two one sA.symm hc xp (mem_filter.mpr ⟨ss',sp t ts⟩)) foreign)
  have dis : Disjoint (insert w F) (localTwo G A x) := by
    apply disjoint_left.mpr
    intro z hz zz
    have za := (mem_inter.mp zz).1
    rcases mem_insert.mp hz with e|f
    · exact disjoint_left.mp shA.disjoint (e ▸ za) ws
    rcases mem_insert.mp f with e|m
    · exact disjoint_left.mp sA ss' (e ▸ za)
    · exact disjoint_left.mp ab za (mem_filter.mp m).1
  have c := (card_le_card (show insert w F∪localTwo G A x⊆DistanceTwo G x from union_subset sub inter_subset_right)).trans
    (distanceTwo_le_of_even 6 x (cap x))
  rw [card_union_of_disjoint dis,card_insert_of_not_mem wo,f4] at c
  have here : (localTwo G A x).card≤1 := by omega
  have so : G.neighborFinset x∩A⊆(ports G A t).erase x∪localTwo G A t := by
    intro y ym
    obtain ⟨yn,ya⟩ := mem_inter.mp ym
    exact (mem_union.mp (shA.port_neighbor_cover hc ts xp yn)).resolve_right
      (fun ys=>disjoint_left.mp shA.disjoint ya ys)
  have in_le := (card_le_card so).trans (card_union_le _ _)
  rw [card_erase_of_mem xp,(data t ts).1,(data t ts).2.2.1] at in_le
  change innerDegree G A x≤1+3 at in_le
  obtain ⟨y,yd,xy⟩ := shA.dark_neighbor_of_high_visible ss va xm (high sA xa)
  have h := shA.dark_neighbor_degree_bound hc yd xy
  have big := high sA (mem_sdiff.mp yd).1
  omega

#print axioms no_three_shores_one_singleton
end Graffiti189LongestPath.ThresholdSix.ThreeCut
