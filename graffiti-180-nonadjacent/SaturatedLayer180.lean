import PairColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count the entire singly marked distance layer of the protected tip. -/
theorem marked_width (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r t : V) (p : Bool) (A : Finset V) (ai : Indep G A) (tr : t≠r)
    (at' : t∈A) (pt : t∈parity G r p) :
    let P := parity G r p
    let H := alternating G P
    1+A.card+P.card+(((A∪P)\(A∩P)).filter (fun y => G.dist y r=G.dist t r)).card+(H.degree t-2)≤
      weightedLeaves G (eligible A P r)+Fintype.card V := by
  classical
  intro P H
  let X := A∪P
  let D := X\(A∩P)
  let d x := G.dist x r
  let C := D.filter (fun x => d x<d t)
  let Y := D.filter (fun x => d x=d t)
  obtain ⟨T,q,rank,sub,tree,down,take,deg,mon,escape⟩ := apex_star G gc r t p A ai tr at' pt
  have kg : T≤G := fun _ _ e => (sub e).1
  obtain ⟨z⟩ := (leaf_core T T le_rfl tree hn (leaves T) Subset.rfl).1.nonempty
  have intZ : z.val∉leaves T := (mem_sdiff.mp z.property).2
  have exactScore := tree_defect T tree (by omega) z.val intZ A P (fun a am b bm ne e => ai a am b bm ne (kg e))
    (fun e => (sub e).2)
  have et : eligible A P z.val∩leaves T=X∩leaves T := by
    ext x
    by_cases eq : x=z.val
    · subst x; simp [intZ]
    · simp [eligible_iff,X,eq]
  change Fintype.card V+(eligible A P z.val∩leaves T).card+(T.edgeFinset∩D.sym2).card=
    1+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at exactScore
  rw [et,trimmed_weight A P (leaves T) r] at exactScore
  have width := forest_width T tree r q rank d down take D (d t)
    (by simpa [d,dist_self] using gc.pos_dist_of_ne tr) mon escape
  change (T.edgeFinset∩D.sym2).card+Y.card+(if r∈D ∧ r∈leaves T then 1 else 0)≤
    D.card+∑ v∈C,(T.degree v-2) at width
  have tm : t∉C := by simp [C]
  have incl : insert t C⊆X := insert_subset (mem_union_left _ at')
    ((filter_subset ..).trans sdiff_subset)
  have cost := sum_le_sum_of_subset_of_nonneg (f:=fun v => T.degree v-2) incl (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert tm] at cost
  change T.degree t-2+(∑ v∈C,(T.degree v-2))≤∑ v∈X,(T.degree v-2) at cost
  change T.degree t=H.degree t at deg
  have pay : (eligible A P r∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun T => (eligible A P r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,tree⟩)
  change Fintype.card V+((eligible A P r∩leaves T).card+(if r∈D ∧ r∈leaves T then 1 else 0))+
    (T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at exactScore
  change 1+A.card+P.card+Y.card+(H.degree t-2)≤weightedLeaves G (eligible A P r)+Fintype.card V
  omega

/-- At a nonroot protected tip whose degree saturates the allowance
bound, every unmarked vertex at the same distance is an actual neighbor. -/
theorem saturated_layer (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r t : V) (p : Bool) (A : Finset V) (ai : Indep G A) (tr : t≠r) (at' : t∈A)
    (pt : t∈parity G r p) (sat : G.degree t=allowance G r p A+2) :
    let P := parity G r p
    let H := alternating G P
    2≤H.degree t ∧ ∀ y,G.dist y r=G.dist t r → (y∉A ↔ G.Adj t y) := by
  classical
  intro P H
  let X := A∪P
  let D := X\(A∩P)
  let d (y : V) := G.dist y r
  let Y := D.filter (fun y => d y=d t)
  have subY : G.neighborFinset t\H.neighborFinset t⊆Y := by
    intro y ym
    obtain ⟨gm,hm⟩ := mem_sdiff.mp ym
    have ed := (G.mem_neighborFinset _ _).mp gm
    have ay : y∉A := fun ya => ai t at' y ya ed.ne ed
    have py : y∈P := by
      by_contra no
      exact hm ((H.mem_neighborFinset _ _).mpr ⟨ed,iff_of_true pt no⟩)
    have a := gc.dist_triangle (u:=y) (v:=t) (w:=r)
    have b := gc.dist_triangle (u:=t) (v:=y) (w:=r)
    rw [dist_eq_one_iff_adj.mpr ed.symm] at a
    rw [dist_eq_one_iff_adj.mpr ed] at b
    have m := (mem_parity G r y p).mp py
    have n := (mem_parity G r t p).mp pt
    exact mem_filter.mpr ⟨by simp [D,X,py,ay],by change G.dist y r=G.dist t r;omega⟩
  have inclusion : H.neighborFinset t⊆G.neighborFinset t := by
    intro y ym
    exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp ym).1
  have count := card_sdiff_add_card_eq_card inclusion
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at count
  have width := marked_width G gc hn r t p A ai tr at' pt
  change 1+A.card+P.card+Y.card+(H.degree t-2)≤weightedLeaves G (eligible A P r)+Fintype.card V at width
  have budget := allowance_eq G gc (by omega) r p A ai
  change 1+A.card+P.card+allowance G r p A=weightedLeaves G (eligible A P r)+Fintype.card V at budget
  have n := card_le_card subY
  have eq : G.neighborFinset t\H.neighborFinset t=Y := eq_of_subset_of_card_le subY (by omega)
  refine ⟨by omega,fun y dy => ⟨fun outside => ?_,fun ed ya => ai t at' y ya ed.ne ed⟩⟩
  have py : y∈P := (mem_parity G r y p).mpr (dy ▸ (mem_parity G r t p).mp pt)
  have ym : y∈Y := mem_filter.mpr ⟨by simp [D,X,outside,py],dy⟩
  rw [←eq] at ym
  exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp ym).1

theorem solo_layer (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (r : V) (p : Bool)
    (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A) (a b : V) (ab : a≠b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (ar : a≠r) :
    ∀ y,G.dist y r=G.dist a r → (y∉A ↔ G.Adj a y) := by
  have rig := solo_rigidity G gc hn r p A ai bad a b ab bi ak bk
  have pt := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  exact (saturated_layer G gc (budget_two G gc hn r p A ai bad a b ab bi).2 r a p A ai ar
    (mem_inter.mp ak).1 pt (by omega)).2

#print axioms marked_width
#print axioms saturated_layer
#print axioms solo_layer
end Minimal180.PairRepair
