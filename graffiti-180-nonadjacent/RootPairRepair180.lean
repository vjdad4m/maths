import SaturatedRoot180
import IndependentStar180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If an independent mark attains the full-star budget exactly, every edge
missing the mark lies entirely inside the root neighborhood. -/
theorem confined_edges (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (P : Finset V) (pr : r∈P) (pi : Indep G P)
    (tight : Fintype.card V+weightedLeaves G P≤1+2*P.card+(G.degree r-2))
    {u v : V} (um : u∉P) (vm : v∉P) (ed : G.Adj u v) : G.Adj r v := by
  classical
  by_contra off
  obtain ⟨T,tg,tr,uv,star⟩ := star_and_edge G gc r u v (fun e => um (e ▸ pr))
    (fun e => vm (e ▸ pr)) ed off
  have full : T.neighborFinset r=G.neighborFinset r := by
    ext x;simp only [mem_neighborFinset];exact ⟨fun e => tg e,star x⟩
  have deg : T.degree r=G.degree r := by simpa only [card_neighborFinset_eq_degree] using congrArg card full
  have id := independent_tree_identity T tr hn P (fun x xm y ym ne e => pi x xm y ym ne (tg e))
  have pos : 0<(T.edgeFinset∩(univ\P).sym2).card := card_pos.mpr ⟨s(u,v),
    mem_inter.mpr ⟨mem_edgeFinset.mpr uv,mk_mem_sym2_iff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,um⟩,
      mem_sdiff.mpr ⟨mem_univ _,vm⟩⟩⟩⟩
  have branch := single_le_sum (f:=fun v => T.degree v-2) (fun v _ => Nat.zero_le _) pr
  change T.degree r-2≤∑ v∈P,(T.degree v-2) at branch
  rw [deg] at branch
  have pay : (P∩leaves T).card≤weightedLeaves G P := le_sup (f:=fun H => (P∩leaves H).card)
    (mem_filter.mpr ⟨mem_univ _,tg,tr⟩)
  omega

/-- Delete the cheaper neighborhood color. The independent mark and the
remaining complement are the two color classes. -/
theorem neighborhood_repair (G : SimpleGraph V) (r : V) (P : Finset V) (pr : r∈P)
    (pi : Indep G P) (localEdges : ∀ u∉P,∀ v∉P,G.Adj u v → G.Adj r v)
    (bip : TwoColor G (G.neighborFinset r)) :
    ∃ Z,TwoColor G Z ∧ P⊆Z ∧ 2*(Fintype.card V-Z.card)≤G.degree r := by
  classical
  obtain ⟨c,ok⟩ := (color_function ..).mp bip
  obtain ⟨s,cheap⟩ := cheap_side (G.neighborFinset r) c
  let F := (G.neighborFinset r).filter (fun x => c x=s)
  let Z := univ\F
  have keep : P⊆Z := by
    intro x xm
    apply mem_sdiff.mpr
    refine ⟨mem_univ _,fun f => ?_⟩
    have rx := (G.mem_neighborFinset r x).mp (mem_filter.mp f).1
    exact pi r pr x xm rx.ne rx
  have same_color {a b t : Bool} (ha : a≠t) (hb : b≠t) : a=b := by
    cases a <;> cases b <;> cases t <;> simp_all
  have rest : Indep G (Z\P) := by
    intro x xm y ym _ ed
    have rx := (G.mem_neighborFinset r x).mpr (localEdges y (mem_sdiff.mp ym).2 x (mem_sdiff.mp xm).2 ed.symm)
    have ry := (G.mem_neighborFinset r y).mpr (localEdges x (mem_sdiff.mp xm).2 y (mem_sdiff.mp ym).2 ed)
    have cx : c x≠s := fun eq => (mem_sdiff.mp (mem_sdiff.mp xm).1).2 (mem_filter.mpr ⟨rx,eq⟩)
    have cy : c y≠s := fun eq => (mem_sdiff.mp (mem_sdiff.mp ym).1).2 (mem_filter.mpr ⟨ry,eq⟩)
    exact (ok x rx y ry ed) (same_color cx cy)
  have sz := card_sdiff_add_card_eq_card (subset_univ F)
  rw [card_univ] at sz
  change 2*F.card≤(G.neighborFinset r).card at cheap
  rw [card_neighborFinset_eq_degree] at cheap
  refine ⟨Z,⟨P,Z\P,disjoint_sdiff,union_sdiff_of_subset keep,pi,rest⟩,keep,?_⟩
  change 2*(Fintype.card V-(univ\F).card)≤G.degree r
  omega

/-- A nonadjacent transversal pair cannot fail at a marking at which
the root is its sole protected tip. No primeness hypothesis is needed. -/
theorem root_solo_protected (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r b : V) (ne : r≠b) (nonedge : ¬G.Adj r b) (bi : TwoColor G (univ\{r,b}))
    (p : Bool) (A : Finset V) (ai : Indep G A) (rk : r∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) : Protected G r p A := by
  classical
  by_contra bad
  obtain ⟨four,two,_⟩ := solo_rigidity G gc hn r p A ai bad r b ne bi rk bk
  obtain ⟨rfl,same⟩ := solo_root G gc hn r p A ai bad b ne bi rk bk
  let P := parity G r false
  change A=P at same
  have rp : r∈P := same ▸ (mem_inter.mp rk).1
  have pi : Indep G P := same ▸ ai
  have eqU : eligible A P r=P := by rw [same];simp [eligible,rp]
  have pay := allowance_eq G gc hn r false A ai
  change 1+A.card+P.card+allowance G r false A=weightedLeaves G (eligible A P r)+Fintype.card V at pay
  rw [two,eqU] at pay
  have tight : Fintype.card V+weightedLeaves G P≤1+2*P.card+(G.degree r-2) := by rw [same] at pay;omega
  have localEdges (u : V) (um : u∉P) (v : V) (vm : v∉P) (ed : G.Adj u v) : G.Adj r v :=
    confined_edges G gc hn r P rp pi tight um vm ed
  have sub : G.neighborFinset r⊆univ\{r,b} := by
    intro x xm
    have rx := (G.mem_neighborFinset r x).mp xm
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    simp only [mem_insert,mem_singleton,not_or]
    exact ⟨rx.ne.symm,fun e => nonedge (e ▸ rx)⟩
  obtain ⟨c,ok⟩ := (color_function ..).mp bi
  have localBi : TwoColor G (G.neighborFinset r) := (color_function ..).mpr ⟨c,
    fun x xm y ym => ok x (sub xm) y (sub ym)⟩
  obtain ⟨Z,zbi,keep,cheap⟩ := neighborhood_repair G r P rp pi localEdges localBi
  exact bad ((protected_iff G gc hn r false A ai).mpr ⟨Z,zbi,
    fun x xm => keep (same ▸ (mem_inter.mp xm).1),by omega⟩)

#print axioms confined_edges
#print axioms neighborhood_repair
#print axioms root_solo_protected
end Minimal180.PairRepair
