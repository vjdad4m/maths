import ApexStar180
import ForestWidth180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem trimmed_weight (A P L : Finset V) (r : V) :
    let X := A∪P
    let D := X\(A∩P)
    (X∩L).card=(eligible A P r∩L).card+(if r∈D ∧ r∈L then 1 else 0) := by
  classical
  intro X D
  by_cases both : r∈A ∧ r∈P
  · simp [eligible,both,X,D,both.1,both.2]
  · have eq : eligible A P r∩L=(X∩L).erase r := by
      ext x; simp only [eligible,if_neg both,mem_inter,mem_erase,X,mem_union];tauto
    have ct := card_trim (X∩L) r
    rw [eq,←ct]
    have iff : r∈X∩L ↔ r∈D ∧ r∈L := by simp [D,both]
    simp only [weight,iff]

/-- All neighbors in the same distance layer are singly marked. The
marked-leaf slack pays for their entire number, together with every
branch at t beyond two in its vertical star. -/
theorem layer_payment (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r t : V) (p : Bool) (A : Finset V) (ai : Indep G A) (tr : t≠r)
    (at' : t∈A) (pt : t∈parity G r p) :
    let P := parity G r p
    let H := alternating G P
    1+A.card+P.card+(G.neighborFinset t\H.neighborFinset t).card+(H.degree t-2)≤
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
  have cap := card_le_card subY
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
  omega

#print axioms trimmed_weight
#print axioms layer_payment
end Minimal180.Transversals
